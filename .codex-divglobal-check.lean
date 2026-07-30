import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergence4D

namespace JanusFormal
namespace DivGlobalCheck

set_option autoImplicit false
set_option maxHeartbeats 200000

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergence4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev Vector4 :=
  P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergence4D.Vector4

private abbrev Index4 :=
  P0EFTJanusMappingTorusGeneralMetricSymmetricTensorDivergence4D.Index4

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

#check ContinuousLinearMap.comp_apply
#check Bundle.Trivialization.continuousLinearEquivAt_apply
#check Bundle.Trivialization.symm_continuousLinearEquivAt_eq
#check trivializationAt_model_space_apply
#check Bundle.Trivialization.continuousLinearMapAt_apply

local instance effectiveTangentFiniteDimensional
    (point : EffectiveQuotient period hPeriod) :
    FiniteDimensional Real
      (TangentSpace coverModelWithCorners point) := by
  change FiniteDimensional Real CoverCoordinates
  infer_instance

local instance effectiveTangentT2
    (point : EffectiveQuotient period hPeriod) :
    T2Space (TangentSpace coverModelWithCorners point) := by
  change T2Space CoverCoordinates
  infer_instance

def testLinear
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    TangentSpace coverModelWithCorners (patch.coordinateMap coordinate) →ₗ[Real]
      Real :=
  (localSymmetricTensorDivergenceModelCovector period hPeriod metric tensor
    patch coordinate).toLinearMap.comp
      ((Pi.basisFun Real Index4).equiv (patch.frame coordinate)
        (Equiv.refl Index4)).symm.toLinearMap

def testContinuous
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Vector4) :
    TangentSpace coverModelWithCorners (patch.coordinateMap coordinate) →L[Real]
      Real :=
  LinearMap.toContinuousLinearMap
    (testLinear period hPeriod metric tensor patch coordinate)

end
end DivGlobalCheck
end JanusFormal
