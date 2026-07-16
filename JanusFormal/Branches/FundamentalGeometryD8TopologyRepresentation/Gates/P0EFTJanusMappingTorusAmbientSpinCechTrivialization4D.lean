import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusAmbientSpinSO4Surjectivity4D

/-!
# Exact Cech residual after ambient Spin(4) surjectivity

The proved surjectivity of the explicit `Spin(4) -> SO(4)` projection removes
the pointwise lifting obstruction on every oriented reduced atlas overlap.
This gate packages the resulting atlas-wide lift choice and proves that the
entire remaining algebraic Cech problem is exactly a kernel-valued one-cochain
whose translation normalizes the chosen lifts and kills their two-cocycle.

Continuity or smoothness of that cochain, and orientation of a supplied
orthonormal atlas reduction, are not asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientSpinCechTrivialization4D

set_option autoImplicit false

noncomputable section

open Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientSpinProjection
open P0EFTJanusMappingTorusAmbientSpinAtlasObstruction
open P0EFTJanusMappingTorusAmbientSpinSurjectivityFrontier
open P0EFTJanusMappingTorusAmbientSpinSO4Surjectivity4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod

private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)

/-- The actual `Spin(4) -> SO(4)` lifting function gives an atlas-wide
pointwise lift of every oriented reduced transition. -/
def ambientSpinAtlasLiftChoice4D
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (hOriented : AmbientSpinAtlasOriented period hPeriod reduction) :
    AmbientSpinAtlasLiftChoice period hPeriod reduction :=
  ambientSpinAtlasLiftChoiceOfOriented period hPeriod
    ambientSpinSO4LiftingFunction reduction hOriented

/-- A kernel-valued one-cochain on the actual overlap domains.  Values are
only requested where the corresponding atlas transition is defined. -/
structure AmbientSpinKernelOneCochain
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod) where
  correction :
    forall first second coordinate
      (_hCoordinate :
        coordinate ∈ (ambientAtlasTransition period hPeriod first second).source),
      MonoidHom.ker ambientSpinProjection

/-- Translate an atlas-wide lift choice by a kernel-valued one-cochain. -/
def ambientSpinAtlasLiftChoiceKernelTranslateBy
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientSpinAtlasLiftChoice period hPeriod reduction)
    (cochain : AmbientSpinKernelOneCochain period hPeriod reduction) :
    AmbientSpinAtlasLiftChoice period hPeriod reduction := by
  classical
  exact {
    transitionLift := fun first second coordinate =>
      if hCoordinate :
          coordinate ∈
            (ambientAtlasTransition period hPeriod first second).source then
        (cochain.correction first second coordinate hCoordinate).1 *
          choice.transitionLift first second coordinate
      else
        choice.transitionLift first second coordinate
    projects := by
      intro first second coordinate hCoordinate
      rw [dif_pos hCoordinate, map_mul,
        (cochain.correction first second coordinate hCoordinate).2,
        choice.projects first second coordinate hCoordinate, one_mul] }

@[simp] theorem ambientSpinAtlasLiftChoiceKernelTranslateBy_apply
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientSpinAtlasLiftChoice period hPeriod reduction)
    (cochain : AmbientSpinKernelOneCochain period hPeriod reduction)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source) :
    (ambientSpinAtlasLiftChoiceKernelTranslateBy period hPeriod reduction
      choice cochain).transitionLift
        first second coordinate =
      (cochain.correction first second coordinate hCoordinate).1 *
        choice.transitionLift first second coordinate := by
  simp [ambientSpinAtlasLiftChoiceKernelTranslateBy, hCoordinate]

/-- The pointwise kernel difference between two atlas lift choices is the
canonical one-cochain translating the first choice to the second one. -/
def ambientSpinKernelOneCochainBetween
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (source target : AmbientSpinAtlasLiftChoice period hPeriod reduction) :
    AmbientSpinKernelOneCochain period hPeriod reduction where
  correction first second coordinate hCoordinate :=
    ambientSpinOverlapLiftDifference period hPeriod reduction first second
      coordinate hCoordinate
      (target.overlapLift period hPeriod reduction first second coordinate
        hCoordinate)
      (source.overlapLift period hPeriod reduction first second coordinate
        hCoordinate)

/-- Translation by the canonical difference agrees with the target choice on
every genuine overlap. -/
theorem ambientSpinKernelOneCochainBetween_translates
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (source target : AmbientSpinAtlasLiftChoice period hPeriod reduction)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source) :
    (ambientSpinAtlasLiftChoiceKernelTranslateBy period hPeriod reduction source
      (ambientSpinKernelOneCochainBetween period hPeriod reduction source target)).transitionLift
        first second coordinate =
      target.transitionLift first second coordinate := by
  rw [ambientSpinAtlasLiftChoiceKernelTranslateBy_apply period hPeriod reduction
    source (ambientSpinKernelOneCochainBetween period hPeriod reduction
      source target) first second coordinate hCoordinate]
  change
    (target.transitionLift first second coordinate *
        (source.transitionLift first second coordinate)⁻¹) *
      source.transitionLift first second coordinate =
        target.transitionLift first second coordinate
  simp

/-- Exact residual datum: a kernel one-cochain whose translated lifts are
normalized and have trivial Cech defect. -/
structure AmbientSpinCechKernelTrivialization
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientSpinAtlasLiftChoice period hPeriod reduction) where
  cochain : AmbientSpinKernelOneCochain period hPeriod reduction
  normalized :
    forall anchor coordinate
      (_hCoordinate :
        coordinate ∈ (ambientAtlasTransition period hPeriod anchor anchor).source),
      (ambientSpinAtlasLiftChoiceKernelTranslateBy period hPeriod reduction
        choice cochain).transitionLift
        anchor anchor coordinate = 1
  defect_trivial :
    forall first second third coordinate
      (hFirstSecond :
        coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
      (hSecondThird :
        ambientAtlasTransition period hPeriod first second coordinate ∈
          (ambientAtlasTransition period hPeriod second third).source)
      (hFirstThird :
        coordinate ∈ (ambientAtlasTransition period hPeriod first third).source),
      (ambientSpinAtlasLiftChoiceKernelTranslateBy period hPeriod reduction
        choice cochain).cechKernelDefect
        period hPeriod reduction first second third coordinate
          hFirstSecond hSecondThird hFirstThird = 1

/-- A coherent kernel trivialization produces the full algebraic Spin Cech
transition lift. -/
def AmbientSpinCechKernelTrivialization.toCechTransitionLift
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientSpinAtlasLiftChoice period hPeriod reduction)
    (trivialization :
      AmbientSpinCechKernelTrivialization period hPeriod reduction choice) :
    AmbientSpinCechTransitionLift period hPeriod reduction :=
  AmbientSpinAtlasLiftChoice.toCechTransitionLiftOfDefectTrivial period hPeriod
    reduction
      (ambientSpinAtlasLiftChoiceKernelTranslateBy period hPeriod reduction
        choice trivialization.cochain)
      trivialization.normalized trivialization.defect_trivial

/-- Any full algebraic Spin Cech lift canonically trivializes the defect of
an arbitrary pointwise atlas lift choice. -/
def ambientSpinCechKernelTrivializationOfTransitionLift
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientSpinAtlasLiftChoice period hPeriod reduction)
    (lift : AmbientSpinCechTransitionLift period hPeriod reduction) :
    AmbientSpinCechKernelTrivialization period hPeriod reduction choice where
  cochain := ambientSpinKernelOneCochainBetween period hPeriod reduction choice
    (ambientSpinCechTransitionLiftToAtlasLiftChoice period hPeriod reduction lift)
  normalized := by
    intro anchor coordinate hCoordinate
    calc
      _ = (ambientSpinCechTransitionLiftToAtlasLiftChoice period hPeriod reduction
          lift).transitionLift anchor anchor coordinate :=
        ambientSpinKernelOneCochainBetween_translates period hPeriod reduction
          choice (ambientSpinCechTransitionLiftToAtlasLiftChoice period hPeriod
            reduction lift) anchor anchor coordinate hCoordinate
      _ = 1 := lift.normalized anchor coordinate hCoordinate
  defect_trivial := by
    intro first second third coordinate hFirstSecond hSecondThird hFirstThird
    apply Subtype.ext
    change
      (ambientSpinAtlasLiftChoiceKernelTranslateBy period hPeriod reduction choice
          (ambientSpinKernelOneCochainBetween period hPeriod reduction choice
            (ambientSpinCechTransitionLiftToAtlasLiftChoice period hPeriod
              reduction lift))).transitionLift second third
            (ambientAtlasTransition period hPeriod first second coordinate) *
          (ambientSpinAtlasLiftChoiceKernelTranslateBy period hPeriod reduction
            choice (ambientSpinKernelOneCochainBetween period hPeriod reduction
              choice (ambientSpinCechTransitionLiftToAtlasLiftChoice period hPeriod
                reduction lift))).transitionLift first second coordinate *
          ((ambientSpinAtlasLiftChoiceKernelTranslateBy period hPeriod reduction
            choice (ambientSpinKernelOneCochainBetween period hPeriod reduction
              choice (ambientSpinCechTransitionLiftToAtlasLiftChoice period hPeriod
                reduction lift))).transitionLift first third coordinate)⁻¹ = 1
    rw [ambientSpinKernelOneCochainBetween_translates period hPeriod reduction
          choice (ambientSpinCechTransitionLiftToAtlasLiftChoice period hPeriod
            reduction lift) second third
          (ambientAtlasTransition period hPeriod first second coordinate)
          hSecondThird,
        ambientSpinKernelOneCochainBetween_translates period hPeriod reduction
          choice (ambientSpinCechTransitionLiftToAtlasLiftChoice period hPeriod
            reduction lift) first second coordinate hFirstSecond,
        ambientSpinKernelOneCochainBetween_translates period hPeriod reduction
          choice (ambientSpinCechTransitionLiftToAtlasLiftChoice period hPeriod
            reduction lift) first third coordinate hFirstThird]
    change lift.transitionLift second third
          (ambientAtlasTransition period hPeriod first second coordinate) *
        lift.transitionLift first second coordinate *
        (lift.transitionLift first third coordinate)⁻¹ = 1
    rw [lift.cocycle first second third coordinate hFirstSecond hSecondThird
      hFirstThird]
    simp

/-- For any pointwise lift choice, coherent kernel trivializations are exactly
equivalent to full algebraic Spin Cech transition lifts. -/
theorem ambientSpinCechKernelTrivialization_nonempty_iff
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientSpinAtlasLiftChoice period hPeriod reduction) :
    Nonempty (AmbientSpinCechKernelTrivialization period hPeriod reduction choice) ↔
      Nonempty (AmbientSpinCechTransitionLift period hPeriod reduction) := by
  constructor
  · rintro ⟨trivialization⟩
    exact ⟨trivialization.toCechTransitionLift period hPeriod reduction choice⟩
  · rintro ⟨lift⟩
    exact ⟨ambientSpinCechKernelTrivializationOfTransitionLift period hPeriod
      reduction choice lift⟩

/-- Final algebraic criterion after the unconditional `Spin(4) -> SO(4)`
surjectivity theorem: orientation supplies all pointwise lifts, and one
kernel-valued Cech trivialization is the only remaining algebraic datum. -/
theorem ambientSpinCechTransitionLift_nonempty_iff
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod) :
    Nonempty (AmbientSpinCechTransitionLift period hPeriod reduction) ↔
      ∃ hOriented : AmbientSpinAtlasOriented period hPeriod reduction,
        Nonempty (AmbientSpinCechKernelTrivialization period hPeriod reduction
          (ambientSpinAtlasLiftChoice4D period hPeriod reduction hOriented)) := by
  constructor
  · rintro ⟨lift⟩
    let choice := ambientSpinCechTransitionLiftToAtlasLiftChoice period hPeriod
      reduction lift
    have hOriented : AmbientSpinAtlasOriented period hPeriod reduction :=
      ambientSpinAtlasOriented_of_liftChoice period hPeriod reduction choice
    refine ⟨hOriented, ?_⟩
    exact (ambientSpinCechKernelTrivialization_nonempty_iff period hPeriod
      reduction
      (ambientSpinAtlasLiftChoice4D period hPeriod reduction hOriented)).2 ⟨lift⟩
  · rintro ⟨hOriented, hTrivialization⟩
    exact (ambientSpinCechKernelTrivialization_nonempty_iff period hPeriod
      reduction
      (ambientSpinAtlasLiftChoice4D period hPeriod reduction hOriented)).1
        hTrivialization

end

end P0EFTJanusMappingTorusAmbientSpinCechTrivialization4D
end JanusFormal
