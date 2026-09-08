import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2CurvatureSmoothJets4D

/-! # Smooth fidelity of the differentiated finite-frame connection -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2ConnectionSmoothDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Manifold ContDiff BigOperators
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
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameMetricContraction4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2KoszulConnection4D
open P0EFTJanusFiniteFrameC2DeDonderFirstJet4D
open P0EFTJanusFiniteFrameC2ScalarCurvature4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusFiniteFrameC2CurvatureSmoothJets4D

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

@[simp] private theorem smoothToContinuous_apply
    (field : SmoothScalarField period hPeriod) (point : EffectiveQuotient period hPeriod) :
    smoothToCanonicalPhysicalContinuousScalar period hPeriod field point = field point := rfl

def finiteFrameSmoothKoszulLowerDerivative
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (derivative first second lower : Fin frame.count) : SmoothScalarField period hPeriod :=
  (1 / 2 : Real) •
    (frameDerivativeComponentField period hPeriod frame
        (frameDerivativeComponentField period hPeriod frame
          (generalMetricFrameCoefficient period hPeriod frame metric.tensor second lower) first) derivative +
      frameDerivativeComponentField period hPeriod frame
        (frameDerivativeComponentField period hPeriod frame
          (generalMetricFrameCoefficient period hPeriod frame metric.tensor first lower) second) derivative -
      frameDerivativeComponentField period hPeriod frame
        (frameDerivativeComponentField period hPeriod frame
          (generalMetricFrameCoefficient period hPeriod frame metric.tensor first second) lower) derivative -
      (∑ contracted : Fin frame.count,
        finiteFrameSmoothStructureMetricDerivativeTerm period hPeriod frame baseMetric metric derivative
          second lower contracted first contracted) +
      (∑ contracted : Fin frame.count,
        finiteFrameSmoothStructureMetricDerivativeTerm period hPeriod frame baseMetric metric derivative
          lower first contracted second contracted) +
      ∑ contracted : Fin frame.count,
        finiteFrameSmoothStructureMetricDerivativeTerm period hPeriod frame baseMetric metric derivative
          first second contracted lower contracted)

theorem finiteFrameKoszulLowerC0Derivative_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (derivative first second lower : Fin frame.count) :
    finiteFrameKoszulLowerC0Derivative period hPeriod frame baseMetric derivative first second lower
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (finiteFrameSmoothKoszulLowerDerivative period hPeriod frame baseMetric metric
          derivative first second lower) := by
  apply ContinuousMap.ext
  intro point
  change finiteFrameKoszulLowerC0Derivative period hPeriod frame baseMetric derivative first second lower
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) point =
    finiteFrameSmoothKoszulLowerDerivative period hPeriod frame baseMetric metric
      derivative first second lower point
  simp only [finiteFrameKoszulLowerC0Derivative, finiteFrameSmoothKoszulLowerDerivative,
    ContinuousMap.smul_apply, ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.sum_apply, smul_eq_mul]
  simp_rw [finiteFrameMetricC0SecondDerivative_smooth period hPeriod frame baseMetric variation metric hMetric]
  simp_rw [finiteFrameStructureMetricC0DerivativeTerm_smooth period hPeriod frame baseMetric variation metric hMetric]
  simp only [smoothToContinuous_apply, smoothScalarFieldSmul_toFun,
    smoothScalarFieldAdd_apply, smoothScalarFieldSub_apply,
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply]
  rfl

def finiteFrameSmoothChristoffelDerivative
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (derivative upper first second : Fin frame.count) : SmoothScalarField period hPeriod :=
  ∑ lower : Fin frame.count, (
    smoothScalarFieldMul period hPeriod
      (frameDerivativeComponentField period hPeriod frame
        (finiteFrameInverseMetricCoefficient period hPeriod frame baseMetric metric upper lower) derivative)
      (finiteFrameKoszulLowerCoefficient period hPeriod frame baseMetric metric first second lower) +
    smoothScalarFieldMul period hPeriod
      (finiteFrameInverseMetricCoefficient period hPeriod frame baseMetric metric upper lower)
      (finiteFrameSmoothKoszulLowerDerivative period hPeriod frame baseMetric metric
        derivative first second lower))

theorem finiteFrameChristoffelC0Derivative_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
      generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric)
    (derivative upper first second : Fin frame.count) :
    finiteFrameChristoffelC0Derivative period hPeriod frame baseMetric derivative upper first second
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (finiteFrameSmoothChristoffelDerivative period hPeriod frame baseMetric metric
          derivative upper first second) := by
  apply ContinuousMap.ext
  intro point
  change finiteFrameChristoffelC0Derivative period hPeriod frame baseMetric derivative upper first second
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) point =
    finiteFrameSmoothChristoffelDerivative period hPeriod frame baseMetric metric
      derivative upper first second point
  simp only [finiteFrameChristoffelC0Derivative, finiteFrameSmoothChristoffelDerivative,
    ContinuousMap.sum_apply, ContinuousMap.add_apply, ContinuousMap.mul_apply]
  simp only [
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply,
    smoothScalarFieldAdd_apply, smoothScalarFieldMul_apply]
  apply Finset.sum_congr rfl
  intro lower _
  rw [finiteFrameInverseMetricC0FirstDerivative_smooth period hPeriod frame baseMetric variation metric
      hMetric hVariation,
    finiteFrameKoszulLowerC0Coefficient_smooth period hPeriod frame baseMetric variation metric hMetric,
    finiteFrameInverseMetricC0Coefficient_smooth period hPeriod frame baseMetric variation metric
      hMetric hVariation,
    finiteFrameKoszulLowerC0Derivative_smooth period hPeriod frame baseMetric variation metric hMetric]
  rfl

end
end P0EFTJanusFiniteFrameC2ConnectionSmoothDerivative4D
end JanusFormal
