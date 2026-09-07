import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D

/-! # Covariant tensor coefficients from the relative C² metric core

Multiplication by the fixed covariant metric matrix reconstructs the actual
tensor coefficients. This gives bounded tensor readout and affine metric
readout on the same C² domain used by the inverse coefficients.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2MetricTensorCoefficients4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameBRSTPairing4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)

private theorem smoothFiniteFrameMetric_times_relative
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    smoothFiniteMatrixProduct period hPeriod frame.count
      (generalMetricFrameCoefficient period hPeriod frame baseMetric.tensor)
      (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame baseMetric tensor) =
    generalMetricFrameCoefficient period hPeriod frame tensor := by
  funext row column
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  have hPair := finiteFrameCovector_pairing period hPeriod frame baseMetric point
    (baseMetric.tensor.tensor point (frame.vectorAt point row))
    (inverseMetricSharp period hPeriod baseMetric point (tensor.tensor point (frame.vectorAt point column)))
  have hFlat := congrArg (fun covector => covector (frame.vectorAt point row))
    (metric_flat_inverseMetricSharp period hPeriod baseMetric point
      (tensor.tensor point (frame.vectorAt point column)))
  change (baseMetric.musical point).toContinuousLinearMap
    (inverseMetricSharp period hPeriod baseMetric point (tensor.tensor point (frame.vectorAt point column)))
      (frame.vectorAt point row) = _ at hFlat
  rw [baseMetric.musical_eq_tensor point, baseMetric.tensor.symmetric,
    tensor.symmetric point] at hFlat
  have hResult := hPair.symm.trans hFlat
  simpa only [smoothFiniteMatrixProduct,
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldMul_apply, generalMetricFrameCoefficient_apply,
    smoothGeneralMetricRelativeEndomorphismMatrix_entry_apply,
    finiteFrameEndomorphismMatrixAt_apply, raisedGeneralMetricTensorAt,
    ContinuousLinearMap.comp_apply, inverseMetricSharp] using hResult

/-- Bounded covariant tensor readout from the faithful relative metric core. -/
def finiteFrameRelativeC2ToTensorCoefficients :
    GeneralMetricRelativeC2Core period hPeriod frame baseMetric →L[Real]
      C2FiniteMatrix period hPeriod frame.count :=
  (c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
    (smoothGeneralMetricTensorToC2Matrix period hPeriod frame baseMetric.tensor)).comp
      (generalMetricRelativeC2CoreToMatrix period hPeriod frame baseMetric)

theorem finiteFrameRelativeC2ToTensorCoefficients_smooth
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    finiteFrameRelativeC2ToTensorCoefficients period hPeriod frame baseMetric
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric tensor) =
    smoothGeneralMetricTensorToC2Matrix period hPeriod frame tensor := by
  change c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
    (smoothFiniteMatrixToC2 period hPeriod frame.count
      (generalMetricFrameCoefficient period hPeriod frame baseMetric.tensor))
    (smoothFiniteMatrixToC2 period hPeriod frame.count
      (smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame baseMetric tensor)) = _
  rw [c2FiniteMatrixProduct_smooth, smoothFiniteFrameMetric_times_relative]
  rfl

/-- Joint metric coefficients, on the same core as the inverse-metric chart. -/
def finiteFrameMetricC2Coefficients
    (variation : GeneralMetricRelativeC2Core period hPeriod frame baseMetric) :
    C2FiniteMatrix period hPeriod frame.count :=
  smoothGeneralMetricTensorToC2Matrix period hPeriod frame baseMetric.tensor +
    finiteFrameRelativeC2ToTensorCoefficients period hPeriod frame baseMetric variation

theorem finiteFrameMetricC2Coefficients_contDiff :
    ContDiff Real ∞ (finiteFrameMetricC2Coefficients period hPeriod frame baseMetric) :=
  contDiff_const.add (finiteFrameRelativeC2ToTensorCoefficients period hPeriod frame baseMetric).contDiff

theorem finiteFrameMetricC2Coefficients_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation) :
    finiteFrameMetricC2Coefficients period hPeriod frame baseMetric
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) =
    smoothGeneralMetricTensorToC2Matrix period hPeriod frame metric.tensor := by
  unfold finiteFrameMetricC2Coefficients
  rw [finiteFrameRelativeC2ToTensorCoefficients_smooth, hMetric, map_add]

theorem finiteFrameMetricC2Coefficients_zero :
    finiteFrameMetricC2Coefficients period hPeriod frame baseMetric 0 =
    smoothGeneralMetricTensorToC2Matrix period hPeriod frame baseMetric.tensor := by
  unfold finiteFrameMetricC2Coefficients
  rw [(finiteFrameRelativeC2ToTensorCoefficients period hPeriod frame baseMetric).map_zero, add_zero]

end
end P0EFTJanusFiniteFrameC2MetricTensorCoefficients4D
end JanusFormal
