import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalGeneralMetricSymmetricTensorDivergence4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D

/-!
# Global de Donder one-form for a general metric

This gate combines the global smooth divergence with the already established
smooth trace correction.  Thus
`B_g(h)_ν = ∇^μ h_{μν} - (1 / 2) d(tr_g h)_ν`
is a genuine smooth global one-form.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergenceIntrinsic4D
open P0EFTJanusMappingTorusGlobalGeneralMetricSymmetricTensorDivergence4D
open P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D
open P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Vector4 :=
  P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergence4D.Vector4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The complete smooth de Donder one-form
`∇^μ h_{μν} - (1 / 2) d(tr_g h)_ν`. -/
def globalGeneralMetricDeDonder
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    EffectiveD8SmoothCovectorField
      (generalMetricDivergenceBackground period hPeriod) :=
  globalGeneralMetricSymmetricTensorDivergence period hPeriod metric tensor +
    generalMetricDeDonderTraceCorrection period hPeriod metric tensor

@[simp]
theorem globalGeneralMetricDeDonder_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalGeneralMetricDeDonder period hPeriod metric tensor point =
      globalGeneralMetricSymmetricTensorDivergenceAt
          period hPeriod metric tensor point +
        (-1 / 2 : Real) •
          generalMetricTensorTraceDifferential
            period hPeriod metric tensor point :=
  rfl

/-- In every holonomic chart, the global de Donder field has the expected
local divergence-plus-trace formula. -/
theorem globalGeneralMetricDeDonder_apply_local
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    globalGeneralMetricDeDonder period hPeriod metric tensor
        (patch.coordinateMap coordinate) =
      localSymmetricTensorDivergenceIntrinsicCovector period hPeriod metric
          tensor patch coordinate +
        (-1 / 2 : Real) •
          generalMetricTensorTraceDifferential period hPeriod metric tensor
            (patch.coordinateMap coordinate) := by
  rw [globalGeneralMetricDeDonder_apply]
  rw [globalGeneralMetricSymmetricTensorDivergenceAt_eq_local]

end

end P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
end JanusFormal
