import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCompleteVariationMatterLLActionHessian4D

namespace JanusFormal
namespace P0EFTJanusCompleteVariationGlobalMetricD9Projection4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusD9GlobalTensorHolonomicMetricBridge4D
open P0EFTJanusD9FullSymmetricMetricLocalCompletion4D
open P0EFTJanusD9CanonicalGlobalTensorHolonomicMetricCompletion4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient

variable (period : ℝ) (hPeriod : period ≠ 0)
private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)

/-- Add a genuine smooth global symmetric metric perturbation in each sector
to the same complete variation that already carries the common action data. -/
def completeVariationWithGlobalMetric
    (variation : IndependentFieldVariation period hPeriod)
    (metric : Sector → SmoothSymmetricCovariantTwoTensor period hPeriod) :
    ProgramPCompleteVariation4D period hPeriod :=
  { independentCompleteVariation period hPeriod variation with
      fullMetricPerturbation := metric }

@[simp] theorem completeVariationWithGlobalMetric_independent
    (variation : IndependentFieldVariation period hPeriod)
    (metric : Sector → SmoothSymmetricCovariantTwoTensor period hPeriod) :
    (completeVariationWithGlobalMetric period hPeriod variation metric).independent =
      variation := rfl

@[simp] theorem completeVariationWithGlobalMetric_tensor
    (variation : IndependentFieldVariation period hPeriod)
    (metric : Sector → SmoothSymmetricCovariantTwoTensor period hPeriod)
    (sector : Sector) :
    (completeVariationWithGlobalMetric period hPeriod variation metric).fullMetricPerturbation
        sector = metric sector := rfl

theorem completeVariationWithGlobalMetric_injective
    (variation : IndependentFieldVariation period hPeriod) :
    Function.Injective
      (completeVariationWithGlobalMetric period hPeriod variation) := by
  intro first second h
  exact congrArg ProgramPCompleteVariation4D.fullMetricPerturbation h

/-- Its D9 metric projection is exactly the six spatial holonomic
coefficients of that same global tensor at the selected throat chart. -/
theorem completeVariationWithGlobalMetric_metricPerturbationAt
    (variation : IndependentFieldVariation period hPeriod)
    (metric : Sector → SmoothSymmetricCovariantTwoTensor period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) :
    (completeVariationWithGlobalMetric period hPeriod variation metric).metricPerturbationAt
        period hPeriod sector point =
      d9FullMetricProjection
        (d9TensorChartMetricVariation period hPeriod (metric sector)
          (selectedD9ThroatHolonomicPatch period hPeriod point)
          (selectedD9ThroatHolonomicCoordinate period hPeriod point)) := rfl

theorem completeVariationWithGlobalMetric_xy
    (variation : IndependentFieldVariation period hPeriod)
    (metric : Sector → SmoothSymmetricCovariantTwoTensor period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) :
    ((completeVariationWithGlobalMetric period hPeriod variation metric).metricPerturbationAt
        period hPeriod sector point).xy =
      d9TensorChartCoefficient period hPeriod (metric sector)
        (selectedD9ThroatHolonomicPatch period hPeriod point) 1 2
        (selectedD9ThroatHolonomicCoordinate period hPeriod point) := rfl

theorem completeVariationWithGlobalMetric_xz
    (variation : IndependentFieldVariation period hPeriod)
    (metric : Sector → SmoothSymmetricCovariantTwoTensor period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) :
    ((completeVariationWithGlobalMetric period hPeriod variation metric).metricPerturbationAt
        period hPeriod sector point).xz =
      d9TensorChartCoefficient period hPeriod (metric sector)
        (selectedD9ThroatHolonomicPatch period hPeriod point) 1 3
        (selectedD9ThroatHolonomicCoordinate period hPeriod point) := rfl

theorem completeVariationWithGlobalMetric_yz
    (variation : IndependentFieldVariation period hPeriod)
    (metric : Sector → SmoothSymmetricCovariantTwoTensor period hPeriod)
    (sector : Sector) (point : EffectiveThroat period hPeriod) :
    ((completeVariationWithGlobalMetric period hPeriod variation metric).metricPerturbationAt
        period hPeriod sector point).yz =
      d9TensorChartCoefficient period hPeriod (metric sector)
        (selectedD9ThroatHolonomicPatch period hPeriod point) 2 3
        (selectedD9ThroatHolonomicCoordinate period hPeriod point) := rfl

end
end P0EFTJanusCompleteVariationGlobalMetricD9Projection4D
end JanusFormal
