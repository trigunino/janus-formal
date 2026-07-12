import Mathlib

namespace JanusFormal
namespace P0EFTJanusMirrorOrbifoldAlternative

set_option autoImplicit false

/-- Loop group expected for the free glide-reflection mapping torus. -/
abbrev GlideLoopGroup := ℤ

/--
Algebraic loop group expected for the global mirror quotient
`[S3 / Z2] x S1`, where the reflection isotropy and circle winding are
independent.
-/
abbrev MirrorOrbifoldLoopGroup := ℤ × ZMod 2

/-- The mirror-isotropy element. -/
def mirrorReflectionLoop : MirrorOrbifoldLoopGroup :=
  (0, 1)

/-- The ordinary circle-winding element. -/
def mirrorCircleLoop : MirrorOrbifoldLoopGroup :=
  (1, 0)

/-- Mirror reflection is nontrivial. -/
theorem mirror_reflection_loop_nonzero :
    mirrorReflectionLoop ≠ 0 := by
  intro hZero
  have hSecond : (1 : ZMod 2) = 0 := by
    simpa [mirrorReflectionLoop] using congrArg Prod.snd hZero
  exact one_ne_zero hSecond

/-- Mirror reflection has additive order two. -/
theorem mirror_reflection_loop_doubles_to_zero :
    mirrorReflectionLoop + mirrorReflectionLoop = 0 := by
  ext <;> native_decide

/-- The circle loop has infinite order in the integer component. -/
theorem nonzero_multiple_of_mirror_circle_nonzero
    (multiple : ℤ)
    (hMultiple : multiple ≠ 0) :
    multiple • mirrorCircleLoop ≠ 0 := by
  intro hZero
  have hFirst : multiple = 0 := by
    simpa [mirrorCircleLoop] using congrArg Prod.fst hZero
  exact hMultiple hFirst

/-- The smooth mapping-torus loop group has no nonzero element of order two. -/
theorem glide_loop_has_no_nonzero_two_torsion
    (loop : GlideLoopGroup)
    (hDouble : loop + loop = 0) :
    loop = 0 := by
  have hTwice : (2 : ℤ) * loop = 0 := by
    nlinarith [hDouble]
  exact (mul_eq_zero.mp hTwice).resolve_left (by norm_num)

/-- A torsion element distinguishes the mirror-orbifold group from the glide group. -/
theorem mirror_group_has_two_torsion_but_glide_group_does_not :
    (mirrorReflectionLoop ≠ 0 /\
      mirrorReflectionLoop + mirrorReflectionLoop = 0) /\
    (∀ loop : GlideLoopGroup, loop + loop = 0 → loop = 0) := by
  exact ⟨⟨mirror_reflection_loop_nonzero,
    mirror_reflection_loop_doubles_to_zero⟩,
    glide_loop_has_no_nonzero_two_torsion⟩

/-- There can be no additive-group equivalence between the two loop groups. -/
theorem no_add_equiv_glide_to_mirror :
    Not (Nonempty (GlideLoopGroup ≃+ MirrorOrbifoldLoopGroup)) := by
  rintro ⟨equivalence⟩
  let preimage : GlideLoopGroup :=
    equivalence.symm mirrorReflectionLoop
  have hDoublePreimage : preimage + preimage = 0 := by
    apply equivalence.injective
    rw [map_add, map_zero]
    simpa [preimage] using mirror_reflection_loop_doubles_to_zero
  have hPreimageZero : preimage = 0 :=
    glide_loop_has_no_nonzero_two_torsion preimage hDoublePreimage
  have hReflectionZero : mirrorReflectionLoop = 0 := by
    calc
      mirrorReflectionLoop = equivalence preimage := by
        simp [preimage]
      _ = equivalence 0 := by rw [hPreimageZero]
      _ = 0 := map_zero equivalence
  exact mirror_reflection_loop_nonzero hReflectionZero

/-- Orientation character for the free glide generator. -/
def glideOrientationCharacter
    (loop : GlideLoopGroup) : ZMod 2 :=
  loop

/-- Mirror orientation character depends only on the isotropy component. -/
def mirrorOrientationCharacter
    (loop : MirrorOrbifoldLoopGroup) : ZMod 2 :=
  loop.2

@[simp] theorem glide_generator_reverses_orientation :
    glideOrientationCharacter 1 = 1 := by
  native_decide

@[simp] theorem mirror_reflection_reverses_orientation :
    mirrorOrientationCharacter mirrorReflectionLoop = 1 := by
  native_decide

@[simp] theorem mirror_circle_preserves_orientation :
    mirrorOrientationCharacter mirrorCircleLoop = 0 := by
  native_decide

/--
In the free mapping torus, reflection and translation are one inseparable
infinite-order generator. In the true mirror orbifold, reflection is an
independent order-two isotropy element commuting with the circle loop.
-/
structure SmoothVersusMirrorPhysicalStatus where
  freeGlideQuotientConstructed : Prop
  mirrorOrbifoldConstructed : Prop
  glideFundamentalGroupComputed : Prop
  mirrorOrbifoldFundamentalGroupComputed : Prop
  localIsotropyCompared : Prop
  singularStrataCompared : Prop
  pinOrbifoldBundlesCompared : Prop
  indexAndEtaRecomputed : Prop
  phenomenologicalChoiceDerived : Prop


def smoothVersusMirrorPhysicalClosure
    (s : SmoothVersusMirrorPhysicalStatus) : Prop :=
  s.freeGlideQuotientConstructed /\
  s.mirrorOrbifoldConstructed /\
  s.glideFundamentalGroupComputed /\
  s.mirrorOrbifoldFundamentalGroupComputed /\
  s.localIsotropyCompared /\
  s.singularStrataCompared /\
  s.pinOrbifoldBundlesCompared /\
  s.indexAndEtaRecomputed /\
  s.phenomenologicalChoiceDerived

end P0EFTJanusMirrorOrbifoldAlternative
end JanusFormal
