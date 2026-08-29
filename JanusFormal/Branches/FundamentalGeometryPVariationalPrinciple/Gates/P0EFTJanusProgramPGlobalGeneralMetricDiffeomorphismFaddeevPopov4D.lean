import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalGeneralMetricDeDonderLinear4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusMetricCartanGlobalAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D

/-!
# Global general-metric diffeomorphism Faddeev--Popov operator

The existing global Cartan action gives the genuine infinitesimal metric
action `c ↦ L_c g`.  Composing it with the existing global de Donder operator
constructs the differential Faddeev--Popov operator `B_g (L_c g)`.

This single-metric construction makes no choice for coupling one diagonal
diffeomorphism ghost to the two Candidate-A metric gauge conditions.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGlobalGeneralMetricSymmetricTensorDivergence4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The genuine infinitesimal metric action `c ↦ L_c g`, on the already
typed global diffeomorphism ghost wrapper. -/
def globalGeneralMetricDiffeomorphismGaugeGeneratorLinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalDiffeomorphismGhostField period hPeriod →ₗ[Real]
      SmoothSymmetricCovariantTwoTensor period hPeriod where
  toFun := fun ghost =>
    smoothMetricCartanActionBilinear period hPeriod ghost.field metric.tensor
  map_add' first second := by
    exact LinearMap.congr_fun
      ((smoothMetricCartanActionBilinear period hPeriod).map_add
        first.field second.field) metric.tensor
  map_smul' scalar ghost := by
    exact LinearMap.congr_fun
      ((smoothMetricCartanActionBilinear period hPeriod).map_smul
        scalar ghost.field) metric.tensor

@[simp]
theorem globalGeneralMetricDiffeomorphismGaugeGeneratorLinearMap_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    globalGeneralMetricDiffeomorphismGaugeGeneratorLinearMap
        period hPeriod metric ghost =
      smoothMetricCartanAction period hPeriod ghost.field metric.tensor :=
  rfl

/-- The unconditional global diffeomorphism Faddeev--Popov operator
`B_g ∘ (c ↦ L_c g)`. -/
def globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    GlobalDiffeomorphismGhostField period hPeriod →ₗ[Real]
      EffectiveD8SmoothCovectorField
        (generalMetricDivergenceBackground period hPeriod) :=
  (globalGeneralMetricDeDonderLinearMap period hPeriod metric).comp
    (globalGeneralMetricDiffeomorphismGaugeGeneratorLinearMap
      period hPeriod metric)

@[simp]
theorem globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (ghost : GlobalDiffeomorphismGhostField period hPeriod) :
    globalGeneralMetricDiffeomorphismFaddeevPopovLinearMap
        period hPeriod metric ghost =
      globalGeneralMetricDeDonder period hPeriod metric
        (smoothMetricCartanAction period hPeriod ghost.field metric.tensor) :=
  rfl

end
end P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
end JanusFormal
