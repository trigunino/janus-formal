import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusAmbientTangentOrientationCocycle

/-!
# Pointwise quadratic reduction of the ambient tangent cocycle

Every real tangent transition of the ambient quotient atlas transports the
standard Euclidean quadratic form to a positive-definite form.  The transition
is therefore a genuine quadratic-form isometry between these two fibers.

This is the maximal unconditional orthogonal reduction currently available:
the transported target form depends on the chosen transition.  A single
compatible metric on all charts, followed by a Cech lift through a specified
Pin or SpinC projection, remains additional data.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientTangentQuadraticReduction

set_option autoImplicit false

noncomputable section

open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod

private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)

/-- The ordinary Euclidean inner product, regarded as an algebraic bilinear
form on the four-dimensional cover-coordinate space. -/
def ambientCoverEuclideanBilinearForm :
    LinearMap.BilinForm Real CoverCoordinates :=
  LinearMap.mk₂ Real
    (fun first second ↦ inner Real first.1 second.1 + first.2 * second.2)
    (by
      intro first second third
      change inner Real (first.1 + second.1) third.1 +
          (first.2 + second.2) * third.2 = _
      rw [inner_add_left]
      ring)
    (by
      intro scalar first second
      change inner Real (scalar • first.1) second.1 +
          (scalar * first.2) * second.2 = scalar * _
      rw [real_inner_smul_left]
      ring)
    (by
      intro first second third
      change inner Real first.1 (second.1 + third.1) +
          first.2 * (second.2 + third.2) = _
      rw [inner_add_right]
      ring)
    (by
      intro scalar first second
      change inner Real first.1 (scalar • second.1) +
          first.2 * (scalar * second.2) = scalar * _
      rw [real_inner_smul_right]
      ring)

/-- Canonical positive-definite quadratic form on ambient cover coordinates. -/
def ambientCoverEuclideanQuadraticForm : QuadraticForm Real CoverCoordinates :=
  ambientCoverEuclideanBilinearForm.toQuadraticMap

@[simp] theorem ambientCoverEuclideanQuadraticForm_apply
    (tangent : CoverCoordinates) :
    ambientCoverEuclideanQuadraticForm tangent =
      ‖tangent.1‖ ^ 2 + tangent.2 ^ 2 := by
  simp [ambientCoverEuclideanQuadraticForm,
    ambientCoverEuclideanBilinearForm, pow_two]

/-- The canonical coordinate form is positive definite. -/
theorem ambientCoverEuclideanQuadraticForm_posDef :
    ambientCoverEuclideanQuadraticForm.PosDef := by
  intro tangent hTangent
  rw [ambientCoverEuclideanQuadraticForm_apply]
  by_cases hFirst : tangent.1 = 0
  · have hSecond : tangent.2 ≠ 0 := by
      intro hSecond
      apply hTangent
      exact Prod.ext hFirst hSecond
    exact add_pos_of_nonneg_of_pos (sq_nonneg _) (sq_pos_of_ne_zero hSecond)
  · exact add_pos_of_pos_of_nonneg
      (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr hFirst)) (sq_nonneg _)

private theorem posDef_nondegenerate
    (form : QuadraticForm Real CoverCoordinates)
    (hForm : form.PosDef) : form.Nondegenerate := by
  rw [QuadraticMap.nondegenerate_iff_radical_eq_bot]
  apply le_antisymm
  · intro tangent hTangent
    have hZero : tangent = 0 := hForm.anisotropic tangent hTangent.1
    simp [hZero]
  · exact bot_le

/-- In particular the canonical coordinate form is nondegenerate. -/
theorem ambientCoverEuclideanQuadraticForm_nondegenerate :
    ambientCoverEuclideanQuadraticForm.Nondegenerate :=
  posDef_nondegenerate ambientCoverEuclideanQuadraticForm
    ambientCoverEuclideanQuadraticForm_posDef

/-- The Euclidean form transported to the target of one actual atlas tangent
transition.  Its dependence on the transition is explicit and prevents an
unjustified promotion to a global metric. -/
def ambientAtlasTransportedQuadraticForm
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source) :
    QuadraticForm Real CoverCoordinates :=
  ambientCoverEuclideanQuadraticForm.comp
    (ambientAtlasTangentTransition period hPeriod first second coordinate hCoordinate).symm.toContinuousLinearMap.toLinearMap

@[simp] theorem ambientAtlasTransportedQuadraticForm_apply
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (tangent : CoverCoordinates) :
    ambientAtlasTransportedQuadraticForm period hPeriod first second coordinate hCoordinate
        tangent =
      let pulledBack :=
        (ambientAtlasTangentTransition period hPeriod first second coordinate hCoordinate).symm
          tangent
      ‖pulledBack.1‖ ^ 2 + pulledBack.2 ^ 2 := by
  simp [ambientAtlasTransportedQuadraticForm]

/-- Transport by an invertible tangent map preserves positive definiteness. -/
theorem ambientAtlasTransportedQuadraticForm_posDef
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source) :
    QuadraticMap.PosDef
      (ambientAtlasTransportedQuadraticForm period hPeriod first second coordinate hCoordinate) := by
  intro tangent hTangent
  let transition :=
    ambientAtlasTangentTransition period hPeriod first second coordinate hCoordinate
  change 0 < ambientCoverEuclideanQuadraticForm (transition.symm tangent)
  apply ambientCoverEuclideanQuadraticForm_posDef
  intro hZero
  apply hTangent
  exact transition.symm.injective (by simpa using hZero)

/-- The transported target form is nondegenerate. -/
theorem ambientAtlasTransportedQuadraticForm_nondegenerate
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source) :
    (ambientAtlasTransportedQuadraticForm period hPeriod first second coordinate hCoordinate).Nondegenerate :=
  posDef_nondegenerate
    (ambientAtlasTransportedQuadraticForm period hPeriod first second coordinate hCoordinate)
    (ambientAtlasTransportedQuadraticForm_posDef period hPeriod first second coordinate hCoordinate)

/-- The derivative of the actual atlas transition, now packaged as an honest
isometric equivalence from the Euclidean source form to its transported target
form. -/
def ambientAtlasQuadraticIsometry
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source) :
    ambientCoverEuclideanQuadraticForm.IsometryEquiv
      (ambientAtlasTransportedQuadraticForm period hPeriod first second coordinate hCoordinate) where
  __ := (ambientAtlasTangentTransition period hPeriod first second coordinate hCoordinate).toLinearEquiv
  map_app' tangent := by simp [ambientAtlasTransportedQuadraticForm]

@[simp] theorem ambientAtlasQuadraticIsometry_apply
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
    (tangent : CoverCoordinates) :
    ambientAtlasQuadraticIsometry period hPeriod first second coordinate hCoordinate tangent =
      ambientAtlasTangentTransition period hPeriod first second coordinate hCoordinate tangent :=
  rfl

/-- A compatible pointwise orthonormal reduction for the whole atlas.  Unlike
the pairwise transported forms above, this asks for one form per chart point
which all actual tangent transitions preserve. -/
structure AmbientOrthonormalAtlasReduction where
  form : AmbientCover period hPeriod → CoverModel →
    QuadraticForm Real CoverCoordinates
  positiveDefinite : ∀ anchor coordinate, (form anchor coordinate).PosDef
  orthonormalFrame : ∀ anchor coordinate,
    ambientCoverEuclideanQuadraticForm.IsometryEquiv (form anchor coordinate)
  transition :
    ∀ first second coordinate
      (_hCoordinate :
        coordinate ∈ (ambientAtlasTransition period hPeriod first second).source),
      (form first coordinate).IsometryEquiv
        (form second (ambientAtlasTransition period hPeriod first second coordinate))
  transition_coe :
    ∀ first second coordinate
      (hCoordinate :
        coordinate ∈ (ambientAtlasTransition period hPeriod first second).source),
      (transition first second coordinate hCoordinate).toLinearEquiv =
        (ambientAtlasTangentTransition period hPeriod first second coordinate hCoordinate).toLinearEquiv

/-- A positive compatible orthonormal reduction supplies the weaker
nondegenerate quadratic-atlas contract isolated by the orientation gate. -/
def AmbientOrthonormalAtlasReduction.toQuadraticAtlasContract
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod) :
    AmbientTangentQuadraticAtlasContract period hPeriod where
  form := reduction.form
  nondegenerate anchor coordinate :=
    posDef_nondegenerate (reduction.form anchor coordinate)
      (reduction.positiveDefinite anchor coordinate)
  transition_isometry first second coordinate hCoordinate tangent := by
    change reduction.form second
        (ambientAtlasTransition period hPeriod first second coordinate)
          ((ambientAtlasTangentTransition period hPeriod first second coordinate hCoordinate).toLinearEquiv
            tangent) =
      reduction.form first coordinate tangent
    rw [← reduction.transition_coe first second coordinate hCoordinate]
    exact (reduction.transition first second coordinate hCoordinate).map_app tangent

/-- The `O(4)`-valued coordinate transition obtained by conjugating the actual
tangent derivative with the supplied orthonormal frames. -/
def AmbientOrthonormalAtlasReduction.orthogonalTransition
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate :
      coordinate ∈ (ambientAtlasTransition period hPeriod first second).source) :
    ambientCoverEuclideanQuadraticForm.IsometryEquiv
      ambientCoverEuclideanQuadraticForm :=
  (reduction.orthonormalFrame first coordinate).trans
    ((reduction.transition first second coordinate hCoordinate).trans
      (reduction.orthonormalFrame second
        (ambientAtlasTransition period hPeriod first second coordinate)).symm)

/-- Minimal algebraic Cech-lift contract after an orthonormal reduction has
been supplied.  Instantiating `LiftGroup` and `projection` with the actual Pin
or SpinC group is deliberately left to the missing Mathlib-facing construction.
The equations are the projection and triple-overlap cocycle obligations, not
Boolean readiness flags. -/
structure AmbientPinSpinCCechLiftContract
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (LiftGroup : Type*) [Group LiftGroup]
    (projection : LiftGroup →* (CoverCoordinates ≃ₗ[Real] CoverCoordinates)) where
  projection_is_orthogonal : ∀ lift tangent,
    ambientCoverEuclideanQuadraticForm (projection lift tangent) =
      ambientCoverEuclideanQuadraticForm tangent
  transitionLift :
    AmbientCover period hPeriod → AmbientCover period hPeriod → CoverModel → LiftGroup
  projects_to_transition :
    ∀ first second coordinate
      (hCoordinate :
        coordinate ∈ (ambientAtlasTransition period hPeriod first second).source),
      projection (transitionLift first second coordinate) =
        (reduction.orthogonalTransition period hPeriod first second coordinate hCoordinate).toLinearEquiv
  normalized :
    ∀ anchor coordinate
      (_hCoordinate :
        coordinate ∈ (ambientAtlasTransition period hPeriod anchor anchor).source),
      transitionLift anchor anchor coordinate = 1
  cocycle :
    ∀ first second third coordinate
      (_hFirstSecond :
        coordinate ∈ (ambientAtlasTransition period hPeriod first second).source)
      (_hSecondThird :
        ambientAtlasTransition period hPeriod first second coordinate ∈
          (ambientAtlasTransition period hPeriod second third).source)
      (_hFirstThird :
        coordinate ∈ (ambientAtlasTransition period hPeriod first third).source),
      transitionLift second third
          (ambientAtlasTransition period hPeriod first second coordinate) *
          transitionLift first second coordinate =
        transitionLift first third coordinate

/-- Topological refinement required for transition functions of an actual
principal Pin/SpinC bundle.  Smoothness is a further refinement once the chosen
lift group has a Mathlib manifold model. -/
structure AmbientPinSpinCContinuousCechLiftContract
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (LiftGroup : Type*) [Group LiftGroup] [TopologicalSpace LiftGroup]
    [IsTopologicalGroup LiftGroup]
    (projection : LiftGroup →* (CoverCoordinates ≃ₗ[Real] CoverCoordinates))
    extends AmbientPinSpinCCechLiftContract period hPeriod reduction LiftGroup projection where
  projection_continuous_apply : ∀ tangent,
    Continuous (fun lift ↦ projection lift tangent)
  transitionLift_continuousOn : ∀ first second,
    ContinuousOn (transitionLift first second)
      (ambientAtlasTransition period hPeriod first second).source

end

end P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
end JanusFormal
