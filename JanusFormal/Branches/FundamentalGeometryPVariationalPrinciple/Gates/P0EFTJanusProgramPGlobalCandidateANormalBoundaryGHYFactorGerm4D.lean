import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryIntegrandGermClosure4D

/-!
# Factorwise closure of the Candidate-A normal-boundary GHY germ

Both the completed and historical mobile GHY integrands have the same three
geometric factors: orientation sign, induced relative volume density and mean
curvature.  The long geometric construction proves these factors through
separate chains.  Their recombination should be algebraic and should not be
stored as another independent integrand hypothesis.

This module packages the factorwise comparison and derives pointwise, action
and Hessian germ equality automatically.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryGHYFactorGerm4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped Topology

universe u v

variable {Variation : Type u}
  [NormedAddCommGroup Variation]
  [NormedSpace Real Variation]

variable {Boundary : Type v}
  [MeasurableSpace Boundary]

open P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionGermCalculus4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryIntegrandGermClosure4D

/-- The canonical product convention used for an oriented GHY density. -/
def realGHYFactorProduct
    (orientation density meanCurvature : Real) : Real :=
  orientation * density * meanCurvature

/-- Factorwise comparison of the completed and historical GHY geometries on
one common open variation domain. -/
structure SameRealGHYFactorGermAt
    (completedOrientation historicalOrientation : Variation → Boundary → Real)
    (completedDensity historicalDensity : Variation → Boundary → Real)
    (completedMeanCurvature historicalMeanCurvature :
      Variation → Boundary → Real)
    (base : Variation) : Type u where
  domain : Set Variation
  isOpen_domain : IsOpen domain
  base_mem_domain : base ∈ domain
  orientation_eq : ∀ variation, variation ∈ domain → ∀ boundary,
    completedOrientation variation boundary =
      historicalOrientation variation boundary
  density_eq : ∀ variation, variation ∈ domain → ∀ boundary,
    completedDensity variation boundary = historicalDensity variation boundary
  meanCurvature_eq : ∀ variation, variation ∈ domain → ∀ boundary,
    completedMeanCurvature variation boundary =
      historicalMeanCurvature variation boundary

/-- Completed factor product. -/
def completedRealGHYIntegrand
    (completedOrientation completedDensity completedMeanCurvature :
      Variation → Boundary → Real) : Variation → Boundary → Real :=
  fun variation boundary =>
    realGHYFactorProduct
      (completedOrientation variation boundary)
      (completedDensity variation boundary)
      (completedMeanCurvature variation boundary)

/-- Historical factor product. -/
def historicalRealGHYIntegrand
    (historicalOrientation historicalDensity historicalMeanCurvature :
      Variation → Boundary → Real) : Variation → Boundary → Real :=
  fun variation boundary =>
    realGHYFactorProduct
      (historicalOrientation variation boundary)
      (historicalDensity variation boundary)
      (historicalMeanCurvature variation boundary)

/-- The factorwise packet reconstructs the pointwise integrand germ. -/
def SameRealGHYFactorGermAt.toIntegrandGerm
    {completedOrientation historicalOrientation : Variation → Boundary → Real}
    {completedDensity historicalDensity : Variation → Boundary → Real}
    {completedMeanCurvature historicalMeanCurvature :
      Variation → Boundary → Real}
    {base : Variation}
    (germ : SameRealGHYFactorGermAt
      completedOrientation historicalOrientation
      completedDensity historicalDensity
      completedMeanCurvature historicalMeanCurvature base) :
    SameRealIntegrandGermAt
      (completedRealGHYIntegrand completedOrientation completedDensity
        completedMeanCurvature)
      (historicalRealGHYIntegrand historicalOrientation historicalDensity
        historicalMeanCurvature)
      base where
  domain := germ.domain
  isOpen_domain := germ.isOpen_domain
  base_mem_domain := germ.base_mem_domain
  eqOn_domain := by
    intro variation hVariation boundary
    unfold completedRealGHYIntegrand historicalRealGHYIntegrand
      realGHYFactorProduct
    rw [germ.orientation_eq variation hVariation boundary,
      germ.density_eq variation hVariation boundary,
      germ.meanCurvature_eq variation hVariation boundary]

/-- Factorwise equality directly produces the two-sheet same-action germ. -/
def SameRealGHYFactorGermAt.toTwoSheetActionGerm
    {completedOrientation historicalOrientation : Variation → Boundary → Real}
    {completedDensity historicalDensity : Variation → Boundary → Real}
    {completedMeanCurvature historicalMeanCurvature :
      Variation → Boundary → Real}
    {base : Variation}
    (germ : SameRealGHYFactorGermAt
      completedOrientation historicalOrientation
      completedDensity historicalDensity
      completedMeanCurvature historicalMeanCurvature base)
    (measure : Measure Boundary) :
    SameRealActionGermAt
      (fun variation => 2 * integratedRealBoundaryAction measure
        (completedRealGHYIntegrand completedOrientation completedDensity
          completedMeanCurvature) variation)
      (fun variation => 2 * integratedRealBoundaryAction measure
        (historicalRealGHYIntegrand historicalOrientation historicalDensity
          historicalMeanCurvature) variation)
      base :=
  germ.toIntegrandGerm.integratedTwoSheetActionGerm measure 2

/-- The terminal H10 second-Fréchet identity derived from the three geometric
factor comparisons. -/
theorem SameRealGHYFactorGermAt.twoSheet_second_fderiv_eq
    {completedOrientation historicalOrientation : Variation → Boundary → Real}
    {completedDensity historicalDensity : Variation → Boundary → Real}
    {completedMeanCurvature historicalMeanCurvature :
      Variation → Boundary → Real}
    {base : Variation}
    (germ : SameRealGHYFactorGermAt
      completedOrientation historicalOrientation
      completedDensity historicalDensity
      completedMeanCurvature historicalMeanCurvature base)
    (measure : Measure Boundary) :
    fderiv Real
        (fun state => fderiv Real
          (fun variation => 2 * integratedRealBoundaryAction measure
            (completedRealGHYIntegrand completedOrientation completedDensity
              completedMeanCurvature) variation)
          state)
        base =
      fderiv Real
        (fun state => fderiv Real
          (fun variation => 2 * integratedRealBoundaryAction measure
            (historicalRealGHYIntegrand historicalOrientation historicalDensity
              historicalMeanCurvature) variation)
          state)
        base :=
  (germ.toTwoSheetActionGerm measure).second_fderiv_eq

/-- Public factorwise H10 closure gate. -/
def candidate_a_normal_boundary_ghy_factor_germ_gate
    {completedOrientation historicalOrientation : Variation → Boundary → Real}
    {completedDensity historicalDensity : Variation → Boundary → Real}
    {completedMeanCurvature historicalMeanCurvature :
      Variation → Boundary → Real}
    {base : Variation}
    (germ : SameRealGHYFactorGermAt
      completedOrientation historicalOrientation
      completedDensity historicalDensity
      completedMeanCurvature historicalMeanCurvature base)
    (measure : Measure Boundary) :
    SameRealActionGermAt
      (fun variation => 2 * integratedRealBoundaryAction measure
        (completedRealGHYIntegrand completedOrientation completedDensity
          completedMeanCurvature) variation)
      (fun variation => 2 * integratedRealBoundaryAction measure
        (historicalRealGHYIntegrand historicalOrientation historicalDensity
          historicalMeanCurvature) variation)
      base :=
  germ.toTwoSheetActionGerm measure

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryGHYFactorGerm4D
end JanusFormal
