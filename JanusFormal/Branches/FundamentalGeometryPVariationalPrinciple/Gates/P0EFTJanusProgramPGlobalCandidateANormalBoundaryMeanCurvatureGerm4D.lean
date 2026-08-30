import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryGHYFactorGerm4D

/-!
# Mean-curvature germ from inverse metric and Gauss form

The completed and historical mean curvatures are finite contractions of the
same two geometric objects: the inverse induced metric and the symmetric Gauss
second fundamental form.  Their equality must therefore be derived from the
componentwise comparison and not stored as a fourth geometric hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryMeanCurvatureGerm4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped BigOperators Topology

universe u v w

variable {Variation : Type u}
  [NormedAddCommGroup Variation]
  [NormedSpace Real Variation]

variable {Boundary : Type v}
  [MeasurableSpace Boundary]

variable {Index : Type w}
  [Fintype Index]

open P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionGermCalculus4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryIntegrandGermClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryGHYFactorGerm4D

/-- Finite contraction convention for the trace of the second fundamental
form with the inverse induced metric. -/
def contractedMeanCurvature
    (inverseMetric secondForm : Index → Index → Real) : Real :=
  ∑ first : Index, ∑ second : Index,
    inverseMetric first second * secondForm second first

/-- Componentwise equality of inverse metrics and second fundamental forms on
one common variation germ. -/
structure SameContractedMeanCurvatureGermAt
    (completedInverse historicalInverse :
      Variation → Boundary → Index → Index → Real)
    (completedSecondForm historicalSecondForm :
      Variation → Boundary → Index → Index → Real)
    (base : Variation) where
  domain : Set Variation
  isOpen_domain : IsOpen domain
  base_mem_domain : base ∈ domain
  inverse_eq : ∀ variation, variation ∈ domain → ∀ boundary first second,
    completedInverse variation boundary first second =
      historicalInverse variation boundary first second
  secondForm_eq : ∀ variation, variation ∈ domain → ∀ boundary first second,
    completedSecondForm variation boundary first second =
      historicalSecondForm variation boundary first second

/-- Completed contracted mean curvature. -/
def completedContractedMeanCurvature
    (completedInverse completedSecondForm :
      Variation → Boundary → Index → Index → Real) :
    Variation → Boundary → Real :=
  fun variation boundary =>
    contractedMeanCurvature
      (completedInverse variation boundary)
      (completedSecondForm variation boundary)

/-- Historical contracted mean curvature. -/
def historicalContractedMeanCurvature
    (historicalInverse historicalSecondForm :
      Variation → Boundary → Index → Index → Real) :
    Variation → Boundary → Real :=
  fun variation boundary =>
    contractedMeanCurvature
      (historicalInverse variation boundary)
      (historicalSecondForm variation boundary)

/-- The finite contraction transports the two componentwise equalities. -/
theorem SameContractedMeanCurvatureGermAt.meanCurvature_eq
    {completedInverse historicalInverse :
      Variation → Boundary → Index → Index → Real}
    {completedSecondForm historicalSecondForm :
      Variation → Boundary → Index → Index → Real}
    {base : Variation}
    (germ : SameContractedMeanCurvatureGermAt
      completedInverse historicalInverse
      completedSecondForm historicalSecondForm base) :
    ∀ variation, variation ∈ germ.domain → ∀ boundary,
      completedContractedMeanCurvature completedInverse completedSecondForm
          variation boundary =
        historicalContractedMeanCurvature historicalInverse historicalSecondForm
          variation boundary := by
  intro variation hVariation boundary
  unfold completedContractedMeanCurvature historicalContractedMeanCurvature
    contractedMeanCurvature
  apply Finset.sum_congr rfl
  intro first hFirst
  apply Finset.sum_congr rfl
  intro second hSecond
  rw [germ.inverse_eq variation hVariation boundary first second,
    germ.secondForm_eq variation hVariation boundary second first]

/-- Combine the matrix comparison with the already established orientation and
volume-density comparisons. -/
def SameContractedMeanCurvatureGermAt.toGHYFactorGerm
    {completedInverse historicalInverse :
      Variation → Boundary → Index → Index → Real}
    {completedSecondForm historicalSecondForm :
      Variation → Boundary → Index → Index → Real}
    {completedOrientation historicalOrientation :
      Variation → Boundary → Real}
    {completedDensity historicalDensity : Variation → Boundary → Real}
    {base : Variation}
    (curvature : SameContractedMeanCurvatureGermAt
      completedInverse historicalInverse
      completedSecondForm historicalSecondForm base)
    (orientationEq : ∀ variation, variation ∈ curvature.domain → ∀ boundary,
      completedOrientation variation boundary =
        historicalOrientation variation boundary)
    (densityEq : ∀ variation, variation ∈ curvature.domain → ∀ boundary,
      completedDensity variation boundary =
        historicalDensity variation boundary) :
    SameRealGHYFactorGermAt
      completedOrientation historicalOrientation
      completedDensity historicalDensity
      (completedContractedMeanCurvature completedInverse completedSecondForm)
      (historicalContractedMeanCurvature historicalInverse historicalSecondForm)
      base where
  domain := curvature.domain
  isOpen_domain := curvature.isOpen_domain
  base_mem_domain := curvature.base_mem_domain
  orientation_eq := orientationEq
  density_eq := densityEq
  meanCurvature_eq := curvature.meanCurvature_eq

/-- Componentwise inverse-metric and Gauss-form equality therefore gives the
same two-sheet action and Hessian germ. -/
def SameContractedMeanCurvatureGermAt.toTwoSheetActionGerm
    {completedInverse historicalInverse :
      Variation → Boundary → Index → Index → Real}
    {completedSecondForm historicalSecondForm :
      Variation → Boundary → Index → Index → Real}
    {completedOrientation historicalOrientation :
      Variation → Boundary → Real}
    {completedDensity historicalDensity : Variation → Boundary → Real}
    {base : Variation}
    (curvature : SameContractedMeanCurvatureGermAt
      completedInverse historicalInverse
      completedSecondForm historicalSecondForm base)
    (orientationEq : ∀ variation, variation ∈ curvature.domain → ∀ boundary,
      completedOrientation variation boundary =
        historicalOrientation variation boundary)
    (densityEq : ∀ variation, variation ∈ curvature.domain → ∀ boundary,
      completedDensity variation boundary =
        historicalDensity variation boundary)
    (measure : Measure Boundary) :=
  (curvature.toGHYFactorGerm orientationEq densityEq).toTwoSheetActionGerm
    measure

/-- Public matrix-level H10 closure gate. -/
theorem candidate_a_normal_boundary_mean_curvature_germ_gate
    {completedInverse historicalInverse :
      Variation → Boundary → Index → Index → Real}
    {completedSecondForm historicalSecondForm :
      Variation → Boundary → Index → Index → Real}
    {base : Variation}
    (curvature : SameContractedMeanCurvatureGermAt
      completedInverse historicalInverse
      completedSecondForm historicalSecondForm base) :
    ∀ variation, variation ∈ curvature.domain → ∀ boundary,
      completedContractedMeanCurvature completedInverse completedSecondForm
          variation boundary =
        historicalContractedMeanCurvature historicalInverse historicalSecondForm
          variation boundary :=
  curvature.meanCurvature_eq

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryMeanCurvatureGerm4D
end JanusFormal
