import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2ConnectionSmoothDerivative4D

/-! # Smooth finite-frame Riemann, Ricci and scalar coefficients -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameC2ScalarCurvatureSmoothCoefficients4D

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
open P0EFTJanusFiniteFrameC2ScalarCurvature4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusFiniteFrameC2ConnectionSmoothDerivative4D

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

def finiteFrameSmoothRiemannCoefficient (metric : SmoothGeneralLorentzMetric period hPeriod)
    (upper lower first second : Fin frame.count) : SmoothScalarField period hPeriod :=
  finiteFrameSmoothChristoffelDerivative period hPeriod frame baseMetric metric
      first upper second lower -
    finiteFrameSmoothChristoffelDerivative period hPeriod frame baseMetric metric
      second upper first lower +
    (∑ contracted : Fin frame.count,
      smoothScalarFieldMul period hPeriod
        (finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
          contracted second lower)
        (finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
          upper first contracted)) -
    (∑ contracted : Fin frame.count,
      smoothScalarFieldMul period hPeriod
        (finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
          contracted first lower)
        (finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
          upper second contracted)) -
    ∑ contracted : Fin frame.count,
      smoothScalarFieldMul period hPeriod
        (finiteFrameStructureCoefficient period hPeriod frame baseMetric first second contracted)
        (finiteFrameKoszulChristoffelCoefficient period hPeriod frame baseMetric metric
          upper contracted lower)

theorem finiteFrameRiemannC0Coefficient_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
      generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric)
    (upper lower first second : Fin frame.count) :
    finiteFrameRiemannC0Coefficient period hPeriod frame baseMetric upper lower first second
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (finiteFrameSmoothRiemannCoefficient period hPeriod frame baseMetric metric
          upper lower first second) := by
  apply ContinuousMap.ext
  intro point
  change finiteFrameRiemannC0Coefficient period hPeriod frame baseMetric upper lower first second
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) point =
    finiteFrameSmoothRiemannCoefficient period hPeriod frame baseMetric metric
      upper lower first second point
  simp only [finiteFrameRiemannC0Coefficient, finiteFrameSmoothRiemannCoefficient,
    ContinuousMap.add_apply, ContinuousMap.sub_apply, ContinuousMap.sum_apply,
    ContinuousMap.mul_apply, smoothScalarFieldAdd_apply, smoothScalarFieldSub_apply,
    smoothScalarFieldMul_apply,
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply]
  rw [finiteFrameChristoffelC0Derivative_smooth period hPeriod frame baseMetric variation metric
      hMetric hVariation first upper second lower,
    finiteFrameChristoffelC0Derivative_smooth period hPeriod frame baseMetric variation metric
      hMetric hVariation second upper first lower]
  simp_rw [finiteFrameChristoffelC0Coefficient_smooth period hPeriod frame baseMetric variation metric
    hMetric hVariation]
  rfl

def finiteFrameSmoothRicciCoefficient (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : Fin frame.count) : SmoothScalarField period hPeriod :=
  ∑ contracted : Fin frame.count,
    finiteFrameSmoothRiemannCoefficient period hPeriod frame baseMetric metric
      contracted first contracted second

theorem finiteFrameRicciC0Coefficient_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
      generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric)
    (first second : Fin frame.count) :
    finiteFrameRicciC0Coefficient period hPeriod frame baseMetric first second
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (finiteFrameSmoothRicciCoefficient period hPeriod frame baseMetric metric first second) := by
  apply ContinuousMap.ext
  intro point
  change finiteFrameRicciC0Coefficient period hPeriod frame baseMetric first second
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) point =
    finiteFrameSmoothRicciCoefficient period hPeriod frame baseMetric metric first second point
  simp only [finiteFrameRicciC0Coefficient, finiteFrameSmoothRicciCoefficient,
    ContinuousMap.sum_apply,
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply]
  apply Finset.sum_congr rfl
  intro contracted _
  exact congrArg (fun value => value point)
    (finiteFrameRiemannC0Coefficient_smooth period hPeriod frame baseMetric variation metric
      hMetric hVariation contracted first contracted second)

def finiteFrameSmoothScalarCurvature (metric : SmoothGeneralLorentzMetric period hPeriod) :
    SmoothScalarField period hPeriod :=
  ∑ first : Fin frame.count, ∑ second : Fin frame.count,
    smoothScalarFieldMul period hPeriod
      (finiteFrameInverseMetricCoefficient period hPeriod frame baseMetric metric first second)
      (finiteFrameSmoothRicciCoefficient period hPeriod frame baseMetric metric first second)

theorem finiteFrameScalarCurvatureC0_smooth
    (variation : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVariation : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
      generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric) :
    finiteFrameScalarCurvatureC0 period hPeriod frame baseMetric
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) =
      smoothToCanonicalPhysicalContinuousScalar period hPeriod
        (finiteFrameSmoothScalarCurvature period hPeriod frame baseMetric metric) := by
  apply ContinuousMap.ext
  intro point
  change finiteFrameScalarCurvatureC0 period hPeriod frame baseMetric
      (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation) point =
    finiteFrameSmoothScalarCurvature period hPeriod frame baseMetric metric point
  simp only [finiteFrameScalarCurvatureC0, finiteFrameSmoothScalarCurvature,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply, smoothScalarFieldMul_apply,
    P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D.smoothScalarFieldFinsetSum_apply]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  rw [finiteFrameInverseMetricC0Coefficient_smooth period hPeriod frame baseMetric variation metric
      hMetric hVariation,
    finiteFrameRicciC0Coefficient_smooth period hPeriod frame baseMetric variation metric
      hMetric hVariation]
  rfl

end
end P0EFTJanusFiniteFrameC2ScalarCurvatureSmoothCoefficients4D
end JanusFormal
