import JanusFormal.Foundations.ProgramMFaithfulEmbeddingNoGo
import Mathlib.Order.Height

/-!
# MF-MAN-003: independently supplied causal-volume-time target

This is a stronger, still pre-geometric interface.  The target owns its order,
volume and proper-time proxy before a candidate embedding is assessed.  The
discrete clock is Mathlib's maximal chain height, not user-provided data.
-/

namespace JanusFormal.ProgramM

open Set

universe u v w

/-- Closed order interval in a candidate partial order. -/
def causalInterval (C : Type u) [PartialOrder C] (x y : C) : Set C :=
  {z | x ≤ z ∧ z ≤ y}

/-- Intrinsic maximal-chain cardinality of an order interval. -/
noncomputable def intrinsicChainLength
    (C : Type u) [PartialOrder C] (x y : C) : ℕ :=
  ENat.toNat ((causalInterval C x y).chainHeight (· < ·))

/-- Number of causal steps rather than number of visited elements.  This makes
a degenerate interval have duration zero. -/
noncomputable def intrinsicChainSteps
    (C : Type u) [PartialOrder C] (x y : C) : ℕ :=
  intrinsicChainLength C x y - 1

theorem causalInterval_finite
    (C : Type u) [PartialOrder C] [Finite C] (x y : C) :
    (causalInterval C x y).Finite :=
  Set.toFinite _

theorem causalInterval_chainHeight_ne_top
    (C : Type u) [PartialOrder C] [Finite C] (x y : C) :
    (causalInterval C x y).chainHeight (· < ·) ≠ ⊤ :=
  Set.chainHeight_ne_top_of_finite _ _ (causalInterval_finite C x y)

/-- The discrete clock is invariant under order-preserving relabelling. -/
theorem intrinsicChainLength_orderIso
    {C : Type u} {D : Type v} [PartialOrder C] [PartialOrder D]
    (e : C ≃o D) (x y : C) :
    intrinsicChainLength D (e x) (e y) = intrinsicChainLength C x y := by
  have himage : e '' causalInterval C x y = causalInterval D (e x) (e y) := by
    ext z
    constructor
    · rintro ⟨a, ⟨hxa, hay⟩, rfl⟩
      exact ⟨e.le_iff_le.mpr hxa, e.le_iff_le.mpr hay⟩
    · intro hz
      refine ⟨e.symm z, ⟨?_, ?_⟩, by simp⟩
      · exact e.le_iff_le.mp (by simpa using hz.1)
      · exact e.le_iff_le.mp (by simpa using hz.2)
  unfold intrinsicChainLength
  apply congrArg ENat.toNat
  rw [← himage]
  exact Set.chainHeight_eq_of_relIso (causalInterval C x y) e.toRelIsoLT

theorem intrinsicChainSteps_orderIso
    {C : Type u} {D : Type v} [PartialOrder C] [PartialOrder D]
    (e : C ≃o D) (x y : C) :
    intrinsicChainSteps D (e x) (e y) = intrinsicChainSteps C x y := by
  simp only [intrinsicChainSteps, intrinsicChainLength_orderIso e x y]

/-- A target supplied independently of the discrete candidate.  This is not
yet a Lorentzian manifold: it is the causal, volume and clock interface that a
future manifold implementation must instantiate. -/
structure CausalVolumeTimeTarget
    (M : Type v) (Region : Type w) [PartialOrder M] where
  identifier : String
  identifier_nonempty : identifier ≠ ""
  contains : Region → M → Prop
  volume : Region → ℝ
  properTime : M → M → ℝ
  volume_nonneg : ∀ r, 0 ≤ volume r
  properTime_nonneg : ∀ x y, 0 ≤ properTime x y
  properTime_zero_of_not_ordered : ∀ x y, ¬ x ≤ y → properTime x y = 0

/-- A well-conditioned proposal uses target-owned volume and time, and compares
the latter with the intrinsic maximal-chain length of the candidate. -/
structure WellConditionedEmbeddingSpecification
    (C : Type u) (M : Type v) (Region : Type w)
    [PartialOrder C] [PartialOrder M] [Finite C]
    (target : CausalVolumeTimeTarget M Region) where
  embedding : C ↪o M
  density : ℝ
  density_pos : 0 < density
  admissible : Region → Prop
  countTolerance : Region → ℝ
  countTolerance_nonneg : ∀ r, 0 ≤ countTolerance r
  minScale : ℝ
  maxScale : ℝ
  regionScale : Region → ℝ
  scaleWindow : minScale ≤ maxScale
  admissible_scale : ∀ r, admissible r →
    minScale ≤ regionScale r ∧ regionScale r ≤ maxScale
  chainToTime : ℝ
  chainToTime_pos : 0 < chainToTime
  timeTolerance : C → C → ℝ
  timeTolerance_nonneg : ∀ x y, 0 ≤ timeTolerance x y
  samplingAssumption : Prop
  countVolumeLaw : samplingAssumption → ∀ r, admissible r →
    |(Set.ncard {c : C | target.contains r (embedding c)} : ℝ) -
      density * target.volume r| ≤ countTolerance r
  chainTimeLaw : samplingAssumption → ∀ x y, x ≤ y →
    |chainToTime * (intrinsicChainSteps C x y : ℝ) -
      target.properTime (embedding x) (embedding y)| ≤ timeTolerance x y

structure WellConditionedEmbeddingCertificate
    (C : Type u) (M : Type v) (Region : Type w)
    [PartialOrder C] [PartialOrder M] [Finite C]
    (target : CausalVolumeTimeTarget M Region) where
  specification : WellConditionedEmbeddingSpecification C M Region target
  samplingProof : specification.samplingAssumption

theorem WellConditionedEmbeddingCertificate.order_preserved_and_reflected
    {C : Type u} {M : Type v} {Region : Type w}
    [PartialOrder C] [PartialOrder M] [Finite C]
    {target : CausalVolumeTimeTarget M Region}
    (cert : WellConditionedEmbeddingCertificate C M Region target) (x y : C) :
    cert.specification.embedding x ≤ cert.specification.embedding y ↔ x ≤ y :=
  cert.specification.embedding.le_iff_le

theorem WellConditionedEmbeddingCertificate.verified_countVolumeLaw
    {C : Type u} {M : Type v} {Region : Type w}
    [PartialOrder C] [PartialOrder M] [Finite C]
    {target : CausalVolumeTimeTarget M Region}
    (cert : WellConditionedEmbeddingCertificate C M Region target)
    (r : Region) (hr : cert.specification.admissible r) :
    |(Set.ncard {c : C | target.contains r (cert.specification.embedding c)} : ℝ) -
      cert.specification.density * target.volume r| ≤
      cert.specification.countTolerance r :=
  cert.specification.countVolumeLaw cert.samplingProof r hr

theorem WellConditionedEmbeddingCertificate.verified_chainTimeLaw
    {C : Type u} {M : Type v} {Region : Type w}
    [PartialOrder C] [PartialOrder M] [Finite C]
    {target : CausalVolumeTimeTarget M Region}
    (cert : WellConditionedEmbeddingCertificate C M Region target)
    (x y : C) (hxy : x ≤ y) :
    |cert.specification.chainToTime * (intrinsicChainSteps C x y : ℝ) -
      target.properTime (cert.specification.embedding x)
        (cert.specification.embedding y)| ≤ cert.specification.timeTolerance x y :=
  cert.specification.chainTimeLaw cert.samplingProof x y hxy

end JanusFormal.ProgramM
