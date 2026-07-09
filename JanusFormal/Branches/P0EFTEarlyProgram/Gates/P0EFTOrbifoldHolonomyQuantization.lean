namespace JanusFormal
namespace P0EFTOrbifoldHolonomyQuantization

set_option autoImplicit false

structure OrbifoldHolonomyLock where
  visibleVolumeQuantum : Int
  mirrorVolumeQuantum : Int
  aSigmaNumerator : Int
  aSigmaDenominator : Int
  volumeQuantumLoaded : Prop
  volumeQuantumDerivedFromIndex : Prop

def aSigmaIsTwoThirds (h : OrbifoldHolonomyLock) : Prop :=
  h.aSigmaNumerator = 2 /\ h.aSigmaDenominator = 3

def threeASigmaMinusTwoClosed (h : OrbifoldHolonomyLock) : Prop :=
  3 * h.aSigmaNumerator - 2 * h.aSigmaDenominator = 0

def minimalZ2VolumeQuantum (h : OrbifoldHolonomyLock) : Prop :=
  h.volumeQuantumLoaded /\
  h.visibleVolumeQuantum = 2 /\
  h.mirrorVolumeQuantum = 1 /\
  h.aSigmaNumerator = h.visibleVolumeQuantum /\
  h.aSigmaDenominator = h.visibleVolumeQuantum + h.mirrorVolumeQuantum

theorem a_sigma_two_thirds_from_minimal_volume_quantum
    (h : OrbifoldHolonomyLock)
    (q : minimalZ2VolumeQuantum h) :
    aSigmaIsTwoThirds h := by
  unfold aSigmaIsTwoThirds
  constructor
  · rw [q.right.right.right.left, q.right.left]
  · rw [q.right.right.right.right, q.right.left, q.right.right.left]
    rfl

theorem three_a_sigma_minus_two_from_two_thirds
    (h : OrbifoldHolonomyLock)
    (h23 : aSigmaIsTwoThirds h) :
    threeASigmaMinusTwoClosed h := by
  unfold threeASigmaMinusTwoClosed
  rw [h23.left, h23.right]
  rfl

theorem no_global_no_fit_from_volume_quantum_alone
    (h : OrbifoldHolonomyLock)
    (hMissing : Not h.volumeQuantumDerivedFromIndex) :
    Not (h.volumeQuantumDerivedFromIndex /\ threeASigmaMinusTwoClosed h) := by
  intro closed
  exact hMissing closed.left

end P0EFTOrbifoldHolonomyQuantization
end JanusFormal
