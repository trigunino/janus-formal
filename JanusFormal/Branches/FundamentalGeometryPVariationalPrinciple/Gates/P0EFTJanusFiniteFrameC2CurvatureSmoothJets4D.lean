import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2ScalarCurvature4D

/-! # Smooth fidelity of the atomic curvature jets -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2CurvatureSmoothJets4D

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameScalarC2Derivatives4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2MetricTensorCoefficients4D
open P0EFTJanusFiniteFrameC2KoszulConnection4D
open P0EFTJanusFiniteFrameC2DeDonderFirstJet4D
open P0EFTJanusFiniteFrameC2ScalarCurvature4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev C2Scalar := CanonicalPhysicalScalarC2JetCore period hPeriod
private abbrev C0Scalar := C(EffectiveQuotient period hPeriod, Real)
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

/-- The completed ordered second metric jet is the genuine ordered frame derivative. -/
theorem finiteFrameMetricC0SecondDerivative_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (outer inner row column : Fin frame.count) :
    finiteFrameMetricC0SecondDerivative period hPeriod frame baseMetric outer inner row column
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        { toFun := fun point => frameSecondDerivative period hPeriod frame
            (generalMetricFrameCoefficient period hPeriod frame metric.tensor row column)
            point outer inner
          contMDiff_toFun := (contMDiff_pi_space.mp (contMDiff_pi_space.mp
            (frameSecondDerivative_contMDiff period hPeriod frame
              (generalMetricFrameCoefficient period hPeriod frame metric.tensor row column)) outer) inner) } := by
  apply ContinuousMap.ext
  intro point
  unfold finiteFrameMetricC0SecondDerivative
  rw [finiteFrameMetricC2Coefficients_smooth period hPeriod frame baseMetric variation metric hMetric]
  exact finiteFrameScalarC2SecondDerivative_smooth period hPeriod baseMetric frame outer inner _ point

/-- The completed inverse first jet is the actual derivative of the smooth inverse coefficient. -/
theorem finiteFrameInverseMetricC0FirstDerivative_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
      generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric)
    (derivative row column : Fin frame.count) :
    finiteFrameInverseMetricC0FirstDerivative period hPeriod frame baseMetric derivative row column
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (frameDerivativeComponentField period hPeriod frame
          (finiteFrameInverseMetricCoefficient period hPeriod frame baseMetric metric row column)
          derivative) := by
  apply ContinuousMap.ext
  intro point
  unfold finiteFrameInverseMetricC0FirstDerivative
  rw [finiteFrameInverseMetricC2Coefficients_smooth period hPeriod frame baseMetric variation metric
    hMetric hVariation]
  exact finiteFrameScalarC2FirstDerivative_smooth period hPeriod baseMetric frame derivative _ point

/-- Smooth Leibniz target for a differentiated anholonomy-metric product. -/
def finiteFrameSmoothStructureMetricDerivativeTerm
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (derivative bracketFirst bracketSecond contracted metricRow metricColumn : Fin frame.count) :
    SmoothScalarField period hPeriod :=
  smoothScalarFieldMul period hPeriod
    (frameDerivativeComponentField period hPeriod frame
      (finiteFrameStructureCoefficient period hPeriod frame baseMetric
        bracketFirst bracketSecond contracted) derivative)
    (generalMetricFrameCoefficient period hPeriod frame metric.tensor metricRow metricColumn) +
  smoothScalarFieldMul period hPeriod
    (finiteFrameStructureCoefficient period hPeriod frame baseMetric
      bracketFirst bracketSecond contracted)
    (frameDerivativeComponentField period hPeriod frame
      (generalMetricFrameCoefficient period hPeriod frame metric.tensor metricRow metricColumn) derivative)

/-- The completed anholonomy-metric derivative is the genuine smooth product rule. -/
theorem finiteFrameStructureMetricC0DerivativeTerm_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (derivative bracketFirst bracketSecond contracted metricRow metricColumn : Fin frame.count) :
    finiteFrameStructureMetricC0DerivativeTerm period hPeriod frame baseMetric derivative
        bracketFirst bracketSecond contracted metricRow metricColumn
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (finiteFrameSmoothStructureMetricDerivativeTerm period hPeriod frame baseMetric metric
          derivative bracketFirst bracketSecond contracted metricRow metricColumn) := by
  apply ContinuousMap.ext
  intro point
  simp only [finiteFrameStructureMetricC0DerivativeTerm,
    finiteFrameSmoothStructureMetricDerivativeTerm,
    ContinuousMap.add_apply, ContinuousMap.mul_apply]
  rw [finiteFrameMetricC0Coefficient_smooth period hPeriod frame baseMetric variation metric hMetric,
    finiteFrameMetricC0FirstDerivative_smooth period hPeriod frame baseMetric variation metric hMetric]
  rfl

end
end P0EFTJanusFiniteFrameC2CurvatureSmoothJets4D
end JanusFormal
