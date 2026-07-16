import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusAmbientSpinAtlasObstruction

/-!
# Exact ambient Spin-surjectivity frontier

Mathlib constructs the Clifford `spinGroup`, but currently supplies no theorem
that its vector action surjects onto the special orthogonal group.  This gate
isolates exactly that missing pointwise input and proves all atlas-level
consequences that do not require continuity of the chosen lifts.

In particular, once a lifting function for `Spin(4) → SO(4)` is supplied,
pointwise liftability is equivalent to determinant `+1`, and an oriented
orthonormal atlas has an atlas-wide pointwise lift choice.  The remaining
algebraic Čech obstruction is packaged without Boolean readiness flags: it is
precisely normalization together with triviality of the already constructed
kernel-valued two-cocycle.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientSpinSurjectivityFrontier

set_option autoImplicit false

noncomputable section

open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientSpinProjection
open P0EFTJanusMappingTorusAmbientSpinOrientation
open P0EFTJanusMappingTorusAmbientSpinAtlasObstruction

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod

private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)

/-- The exact missing Mathlib-facing datum for the pointwise double cover
`Spin(4) → SO(4)`.  No atlas or Čech choices are hidden in this structure. -/
structure AmbientSpinSO4LiftingFunction where
  lift :
    (target : ambientCoverEuclideanQuadraticForm.IsometryEquiv
      ambientCoverEuclideanQuadraticForm) →
    LinearEquiv.det target.toLinearEquiv = (1 : Realˣ) →
      AmbientCoordinateSpinGroup
  projects :
    ∀ target hDet,
      ambientSpinProjection (lift target hDet) = target.toLinearEquiv

/-- Proposition-level surjectivity of the explicit Clifford projection onto
the determinant-`+1` part of the ambient orthogonal group. -/
def AmbientSpinSO4Surjective : Prop :=
  ∀ target : ambientCoverEuclideanQuadraticForm.IsometryEquiv
      ambientCoverEuclideanQuadraticForm,
    LinearEquiv.det target.toLinearEquiv = (1 : Realˣ) →
      ∃ lift : AmbientCoordinateSpinGroup,
        ambientSpinProjection lift = target.toLinearEquiv

/-- A lifting function proves the corresponding surjectivity proposition. -/
theorem AmbientSpinSO4LiftingFunction.surjective
    (lifting : AmbientSpinSO4LiftingFunction) :
    AmbientSpinSO4Surjective := by
  intro target hDet
  exact ⟨lifting.lift target hDet, lifting.projects target hDet⟩

/-- Classical choice is the only step between proposition-level surjectivity
and an explicit pointwise lifting function. -/
def ambientSpinSO4LiftingFunctionOfSurjective
    (hSurjective : AmbientSpinSO4Surjective) :
    AmbientSpinSO4LiftingFunction where
  lift target hDet := Classical.choose (hSurjective target hDet)
  projects target hDet := Classical.choose_spec (hSurjective target hDet)

/-- The constructive lifting datum is nonempty exactly when the explicit
projection is surjective onto determinant-`+1` orthogonal isometries. -/
theorem ambientSpinSO4LiftingFunction_nonempty_iff_surjective :
    Nonempty AmbientSpinSO4LiftingFunction ↔ AmbientSpinSO4Surjective := by
  constructor
  · rintro ⟨lifting⟩
    exact lifting.surjective
  · intro hSurjective
    exact ⟨ambientSpinSO4LiftingFunctionOfSurjective hSurjective⟩

/-- Pointwise orientation condition for every actual reduced atlas overlap. -/
def AmbientSpinAtlasOriented
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod) : Prop :=
  ∀ first second coordinate
      (hCoordinate :
        coordinate ∈ (ambientAtlasTransition period hPeriod first second).source),
    LinearEquiv.det
      (reduction.orthogonalTransition period hPeriod first second
        coordinate hCoordinate).toLinearEquiv = (1 : Realˣ)

/-- Surjectivity makes determinant `+1` sufficient, while the orientation
gate already proved it necessary. -/
theorem ambientSpinOverlapLift_nonempty_iff_det_eq_one
    (lifting : AmbientSpinSO4LiftingFunction)
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source) :
    Nonempty (AmbientSpinOverlapLift period hPeriod reduction
      first second coordinate hCoordinate) ↔
      LinearEquiv.det
        (reduction.orthogonalTransition period hPeriod first second
          coordinate hCoordinate).toLinearEquiv = (1 : Realˣ) := by
  constructor
  · rintro ⟨overlapLift⟩
    exact overlapLift.orthogonalTransition_det period hPeriod reduction
      first second coordinate hCoordinate
  · intro hDet
    exact ⟨{
      lift := lifting.lift
        (reduction.orthogonalTransition period hPeriod first second
          coordinate hCoordinate) hDet
      projects := lifting.projects
        (reduction.orthogonalTransition period hPeriod first second
          coordinate hCoordinate) hDet }⟩

/-- An oriented reduced atlas acquires an atlas-wide pointwise lift choice
from the single `Spin(4) → SO(4)` lifting function.  Outside an overlap source
the transition value is irrelevant and is set to the identity. -/
def ambientSpinAtlasLiftChoiceOfOriented
    (lifting : AmbientSpinSO4LiftingFunction)
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (hOriented : AmbientSpinAtlasOriented period hPeriod reduction) :
    AmbientSpinAtlasLiftChoice period hPeriod reduction := by
  classical
  exact {
    transitionLift := fun first second coordinate ↦
      if hCoordinate :
          coordinate ∈ (ambientAtlasTransition period hPeriod first second).source then
        lifting.lift
          (reduction.orthogonalTransition period hPeriod first second
            coordinate hCoordinate)
          (hOriented first second coordinate hCoordinate)
      else
        1
    projects := by
      intro first second coordinate hCoordinate
      rw [dif_pos hCoordinate]
      exact lifting.projects
        (reduction.orthogonalTransition period hPeriod first second
          coordinate hCoordinate)
        (hOriented first second coordinate hCoordinate) }

/-- Any atlas-wide Spin lift choice forces every reduced transition to be
orientation preserving. -/
theorem ambientSpinAtlasOriented_of_liftChoice
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (choice : AmbientSpinAtlasLiftChoice period hPeriod reduction) :
    AmbientSpinAtlasOriented period hPeriod reduction := by
  intro first second coordinate hCoordinate
  exact (choice.overlapLift period hPeriod reduction first second coordinate
    hCoordinate).orthogonalTransition_det period hPeriod reduction first second
      coordinate hCoordinate

/-- Under the one pointwise surjectivity input, atlas orientation is exactly
equivalent to existence of an atlas-wide pointwise Spin lift choice. -/
theorem ambientSpinAtlasLiftChoice_nonempty_iff_oriented
    (lifting : AmbientSpinSO4LiftingFunction)
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod) :
    Nonempty (AmbientSpinAtlasLiftChoice period hPeriod reduction) ↔
      AmbientSpinAtlasOriented period hPeriod reduction := by
  constructor
  · rintro ⟨choice⟩
    exact ambientSpinAtlasOriented_of_liftChoice period hPeriod reduction choice
  · intro hOriented
    exact ⟨ambientSpinAtlasLiftChoiceOfOriented period hPeriod lifting reduction
      hOriented⟩

/-- Actual algebraic completion data for the ambient Spin Čech problem.  It
contains the pointwise lifts, their normalization, and a proof that their
kernel-valued two-cocycle vanishes.  Continuity and smoothness are deliberately
not asserted here. -/
structure AmbientSpinAlgebraicCechCompletion
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod) where
  choice : AmbientSpinAtlasLiftChoice period hPeriod reduction
  normalized :
    ∀ anchor coordinate
      (_hCoordinate :
        coordinate ∈ (ambientAtlasTransition period hPeriod anchor anchor).source),
      choice.transitionLift anchor anchor coordinate = 1
  defect_trivial :
    ∀ first second third coordinate
      (hFirstSecond :
        coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
      (hSecondThird :
        ambientAtlasTransition period hPeriod first second coordinate ∈
          (ambientAtlasTransition period hPeriod second third).source)
      (hFirstThird :
        coordinate ∈ (ambientAtlasTransition period hPeriod first third).source),
      choice.cechKernelDefect period hPeriod reduction first second third
        coordinate hFirstSecond hSecondThird hFirstThird = 1

/-- Completion data produces the genuine algebraic Spin Čech transition
lift, with no further hypothesis. -/
def AmbientSpinAlgebraicCechCompletion.toCechTransitionLift
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (completion : AmbientSpinAlgebraicCechCompletion period hPeriod reduction) :
    AmbientSpinCechTransitionLift period hPeriod reduction :=
  completion.choice.toCechTransitionLiftOfDefectTrivial period hPeriod reduction
    completion.normalized completion.defect_trivial

/-- Conversely, a genuine algebraic Spin Čech lift supplies exactly the
completion data above. -/
def ambientSpinAlgebraicCechCompletionOfTransitionLift
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (lift : AmbientSpinCechTransitionLift period hPeriod reduction) :
    AmbientSpinAlgebraicCechCompletion period hPeriod reduction where
  choice := ambientSpinCechTransitionLiftToAtlasLiftChoice period hPeriod reduction lift
  normalized := lift.normalized
  defect_trivial first second third coordinate hFirstSecond hSecondThird hFirstThird :=
    JanusFormal.P0EFTJanusMappingTorusAmbientSpinAtlasObstruction.AmbientSpinCechTransitionLift.toAtlasLiftChoice_cechKernelDefect_eq_one
      period hPeriod reduction lift first second third coordinate hFirstSecond
        hSecondThird hFirstThird

/-- Exact algebraic closure criterion: the completion package is nonempty if
and only if the actual Spin Čech transition-lift structure is nonempty. -/
theorem ambientSpinAlgebraicCechCompletion_nonempty_iff :
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod) →
    Nonempty (AmbientSpinAlgebraicCechCompletion period hPeriod reduction) ↔
      Nonempty (AmbientSpinCechTransitionLift period hPeriod reduction) := by
  intro reduction
  constructor
  · rintro ⟨completion⟩
    exact ⟨completion.toCechTransitionLift period hPeriod reduction⟩
  · rintro ⟨lift⟩
    exact ⟨ambientSpinAlgebraicCechCompletionOfTransitionLift period hPeriod
      reduction lift⟩

/-- Any algebraic Čech completion includes, in particular, the orientation
reduction required before the kernel two-cocycle can even be formed. -/
theorem AmbientSpinAlgebraicCechCompletion.oriented
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (completion : AmbientSpinAlgebraicCechCompletion period hPeriod reduction) :
    AmbientSpinAtlasOriented period hPeriod reduction :=
  ambientSpinAtlasOriented_of_liftChoice period hPeriod reduction completion.choice

end

end P0EFTJanusMappingTorusAmbientSpinSurjectivityFrontier
end JanusFormal
