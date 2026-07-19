import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusAmbientSpinSO4Surjectivity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusProjection4D

/-!
# Pointwise Pin-minus lifts of the actual reduced ambient tangent transitions

Cartan--Dieudonné factors every ambient `O(4)` isometry into unit
reflections.  Each such reflection has the explicit negative-Clifford
generator already constructed in the Pin-minus projection gate.  Their
ordered product therefore proves unconditional pointwise surjectivity of
`Pin⁻(4) → O(4)` and lifts every genuine reduced tangent transition.

No continuity, normalization or Čech coherence of the classically selected
pointwise lifts is claimed here.  Those remain the global Pin-structure
obligation.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientPinMinusPointwiseTangentLift4D

set_option autoImplicit false

noncomputable section

open CliffordAlgebra
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientSpinEvenReflectionLift
open P0EFTJanusMappingTorusAmbientSpinSO4Surjectivity4D
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod
private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)

/-- The negative-Clifford unit generator projects to the ordinary Euclidean
hyperplane reflection with the same unit normal. -/
theorem ambientPinMinusProjection_unitNormalGenerator_eq_reflection
    (normal : CoverCoordinates)
    (hNormal : ambientCoverEuclideanQuadraticForm normal = 1) :
    ambientPinMinusProjection
        (ambientPinMinusUnitNormalGenerator normal hNormal) =
      ambientUnitReflection normal hNormal := by
  apply LinearEquiv.ext
  intro tangent
  rw [ambientPinMinusProjection_unitNormalGenerator_apply]
  change tangent +
      QuadraticMap.polar ambientCoverPinMinusQuadraticForm normal tangent • normal =
    tangent -
      QuadraticMap.polar ambientCoverEuclideanQuadraticForm normal tangent • normal
  have hPolar :
      QuadraticMap.polar ambientCoverPinMinusQuadraticForm normal tangent =
        -QuadraticMap.polar ambientCoverEuclideanQuadraticForm normal tangent := by
    rw [ambientCoverPinMinusQuadraticForm]
    simp only [QuadraticMap.polar, QuadraticMap.neg_apply]
    ring
  rw [hPolar]
  module

/-- Pin-minus lift of one unit reflection factor. -/
def ambientUnitReflectionFactorPinMinusLift
    (factor : AmbientUnitReflectionFactor) :
    AmbientCoordinatePinMinusGroup :=
  ambientPinMinusUnitNormalGenerator factor.vector factor.unit

@[simp] theorem ambientUnitReflectionFactorPinMinusLift_projects
    (factor : AmbientUnitReflectionFactor) :
    ambientPinMinusProjection
        (ambientUnitReflectionFactorPinMinusLift factor) =
      factor.reflectionEquiv :=
  ambientPinMinusProjection_unitNormalGenerator_eq_reflection
    factor.vector factor.unit

/-- Ordered Clifford product lifting a finite reflection factorization. -/
def ambientPinMinusLiftOfUnitFactors
    (factors : List AmbientUnitReflectionFactor) :
    AmbientCoordinatePinMinusGroup :=
  (factors.map ambientUnitReflectionFactorPinMinusLift).prod

/-- Projection commutes with the entire ordered reflection product. -/
theorem ambientPinMinusProjection_liftOfUnitFactors
    (factors : List AmbientUnitReflectionFactor) :
    ambientPinMinusProjection (ambientPinMinusLiftOfUnitFactors factors) =
      ambientReflectionProductOfUnitFactors factors := by
  induction factors with
  | nil => simp [ambientPinMinusLiftOfUnitFactors,
      ambientReflectionProductOfUnitFactors]
  | cons factor rest inductionHypothesis =>
      change ambientPinMinusProjection
          (ambientUnitReflectionFactorPinMinusLift factor *
            (rest.map ambientUnitReflectionFactorPinMinusLift).prod) =
        factor.reflectionEquiv *
          (rest.map AmbientUnitReflectionFactor.reflectionEquiv).prod
      rw [map_mul, ambientUnitReflectionFactorPinMinusLift_projects]
      simpa only [ambientPinMinusLiftOfUnitFactors,
        ambientReflectionProductOfUnitFactors] using congrArg
          (fun transition => factor.reflectionEquiv * transition)
          inductionHypothesis

/-- The Pin-minus lift carried by a full Cartan--Dieudonné factorization. -/
def ambientO4UnitReflectionFactorizationToPinMinusLift
    {target : ambientCoverEuclideanQuadraticForm.IsometryEquiv
      ambientCoverEuclideanQuadraticForm}
    (factorization : AmbientO4UnitReflectionFactorization target) :
    AmbientCoordinatePinMinusGroup :=
  ambientPinMinusLiftOfUnitFactors factorization.factors

/-- Exact projection of the factorization lift to its `O(4)` target. -/
theorem ambientO4UnitReflectionFactorizationToPinMinusLift_projects
    {target : ambientCoverEuclideanQuadraticForm.IsometryEquiv
      ambientCoverEuclideanQuadraticForm}
    (factorization : AmbientO4UnitReflectionFactorization target) :
    ambientPinMinusProjection
        (ambientO4UnitReflectionFactorizationToPinMinusLift factorization) =
      target.toLinearEquiv :=
  (ambientPinMinusProjection_liftOfUnitFactors factorization.factors).trans
    factorization.factorization

/-- The explicit negative-Clifford projection is pointwise surjective onto
the full ambient orthogonal group, including orientation-reversing maps. -/
theorem ambientPinMinusO4Surjective
    (target : ambientCoverEuclideanQuadraticForm.IsometryEquiv
      ambientCoverEuclideanQuadraticForm) :
    ∃ lift : AmbientCoordinatePinMinusGroup,
      ambientPinMinusProjection lift = target.toLinearEquiv := by
  rcases ambientO4HasUnitReflectionFactorization target with ⟨factorization⟩
  exact ⟨ambientO4UnitReflectionFactorizationToPinMinusLift factorization,
    ambientO4UnitReflectionFactorizationToPinMinusLift_projects factorization⟩

/-- A fixed pointwise lift selected from the proved surjectivity theorem. -/
def ambientPinMinusO4Lift
    (target : ambientCoverEuclideanQuadraticForm.IsometryEquiv
      ambientCoverEuclideanQuadraticForm) :
    AmbientCoordinatePinMinusGroup :=
  Classical.choose (ambientPinMinusO4Surjective target)

@[simp] theorem ambientPinMinusO4Lift_projects
    (target : ambientCoverEuclideanQuadraticForm.IsometryEquiv
      ambientCoverEuclideanQuadraticForm) :
    ambientPinMinusProjection (ambientPinMinusO4Lift target) =
      target.toLinearEquiv :=
  Classical.choose_spec (ambientPinMinusO4Surjective target)

/-- Pointwise Pin-minus lift of a genuine ambient tangent transition after
the already-constructed orthonormal frame reduction. -/
def ambientPinMinusPointwiseTangentTransitionLift
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    AmbientCoordinatePinMinusGroup :=
  ambientPinMinusO4Lift
    (reduction.orthogonalTransition period hPeriod first second coordinate
      hCoordinate)

/-- The selected pointwise lift projects exactly to the reduced derivative of
the actual ambient atlas transition. -/
theorem ambientPinMinusPointwiseTangentTransitionLift_projects
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    ambientPinMinusProjection
        (ambientPinMinusPointwiseTangentTransitionLift period hPeriod reduction
          first second coordinate hCoordinate) =
      (reduction.orthogonalTransition period hPeriod first second coordinate
        hCoordinate).toLinearEquiv :=
  ambientPinMinusO4Lift_projects _

/-- Consequently the pointwise lift implements the genuine reduced tangent
transition by the exact twisted Clifford action. -/
theorem ambientPinMinusPointwiseTangentTransitionLift_twisted_action
    (reduction : AmbientOrthonormalAtlasReduction period hPeriod)
    (first second : AmbientCover period hPeriod)
    (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source)
    (tangent : CoverCoordinates) :
    CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
        ((reduction.orthogonalTransition period hPeriod first second coordinate
          hCoordinate).toLinearEquiv tangent) =
      involute
          (ambientPinMinusPointwiseTangentTransitionLift period hPeriod reduction
            first second coordinate hCoordinate :
              AmbientPinMinusCliffordAlgebra) *
        CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm tangent *
        (↑((ambientPinMinusPointwiseTangentTransitionLift period hPeriod
          reduction first second coordinate hCoordinate)⁻¹) :
            AmbientPinMinusCliffordAlgebra) := by
  rw [← ambientPinMinusPointwiseTangentTransitionLift_projects period hPeriod
    reduction first second coordinate hCoordinate]
  exact ambientPinMinusVectorAction_spec
    (ambientPinMinusPointwiseTangentTransitionLift period hPeriod reduction
      first second coordinate hCoordinate) tangent

end

end P0EFTJanusMappingTorusAmbientPinMinusPointwiseTangentLift4D
end JanusFormal
