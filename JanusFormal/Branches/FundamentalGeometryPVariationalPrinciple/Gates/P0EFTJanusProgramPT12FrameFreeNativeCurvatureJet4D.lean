import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ProjectedCurvatureJetSymbol4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D

/-! Exact pointwise realization of the projected polynomial by native completed C² features. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeNativeCurvatureJet4D
set_option autoImplicit false
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
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGeneralMetricC2VariationCore4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusFiniteFrameC2CanonicalVolume4D
open P0EFTJanusFiniteFrameC2ScalarCurvature4D
open P0EFTJanusFiniteFrameC2ProjectedScalarCompletion4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D

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
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl
local instance : MeasureTheory.IsFiniteMeasure
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance
local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

open P0EFTJanusProgramPT12ProjectedCurvatureJetSymbol4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D
open P0EFTJanusFiniteFrameC2MetricTensorCoefficients4D
open P0EFTJanusFiniteFrameC2KoszulConnection4D
open P0EFTJanusFiniteFrameC2DeDonderFirstJet4D
open P0EFTJanusFiniteFrameC2ProjectedRicciCompletion4D
open P0EFTJanusFiniteFrameCovectorC2Projection4D
open P0EFTJanusFiniteFrameC2EinsteinHilbertAction4D
variable (frame : SmoothD8Frame period hPeriod) (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
local notation "Model" => GeneralMetricRelativeC2Core period hPeriod frame baseMetric
local notation "N" => Fin frame.count
local notation "Jet" => CurvatureJet frame.count

def frameFreeNativeCurvatureJet (variation : Model) (point : EffectiveQuotient period hPeriod) : Jet :=
  ((fun row column => finiteFrameMetricC0Coefficient period hPeriod frame baseMetric row column variation point),
   (fun row column => finiteFrameInverseMetricC0Coefficient period hPeriod frame baseMetric row column variation point),
   (fun direction row column => finiteFrameMetricC0FirstDerivative period hPeriod frame baseMetric direction row column variation point),
   (fun outer innerIndex row column => finiteFrameMetricC0SecondDerivative period hPeriod frame baseMetric outer innerIndex row column variation point),
   (fun direction row column => finiteFrameInverseMetricC0FirstDerivative period hPeriod frame baseMetric direction row column variation point))

def frameFreeNativeStructureJet (point : EffectiveQuotient period hPeriod) : MetricFirstJet frame.count :=
  fun first second upper => finiteFrameStructureC0Coefficient period hPeriod frame baseMetric first second upper point

def frameFreeNativeStructureDerivativeJet (point : EffectiveQuotient period hPeriod) : MetricSecondJet frame.count :=
  fun direction first second upper => finiteFrameStructureC0Derivative period hPeriod frame baseMetric direction first second upper point

def frameFreeNativeTraceProjection (point : EffectiveQuotient period hPeriod) : MetricMatrix frame.count :=
  fun upper traced => finiteFrameCovectorProjectionCoefficient period hPeriod frame baseMetric upper traced point

local notation "jet" => frameFreeNativeCurvatureJet period hPeriod frame baseMetric
local notation "bracket" => frameFreeNativeStructureJet period hPeriod frame baseMetric
local notation "dBracket" => frameFreeNativeStructureDerivativeJet period hPeriod frame baseMetric
local notation "projection" => frameFreeNativeTraceProjection period hPeriod frame baseMetric

private theorem koszul (variation : Model) (point : EffectiveQuotient period hPeriod) (first second lower : N) :
    finiteFrameKoszulLowerC0Coefficient period hPeriod frame baseMetric first second lower variation point =
      projectedJetKoszul (bracket point) (jet variation point) first second lower := by
  simp only [finiteFrameKoszulLowerC0Coefficient, projectedJetKoszul, frameFreeNativeCurvatureJet,
    frameFreeNativeStructureJet, ContinuousMap.smul_apply, ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply, smul_eq_mul]

private theorem structure_derivative (variation : Model) (point : EffectiveQuotient period hPeriod)
    (direction first second contracted row column : N) :
    finiteFrameStructureMetricC0DerivativeTerm period hPeriod frame baseMetric direction first second contracted row column variation point =
      projectedJetStructureDerivative (bracket point) (dBracket point) (jet variation point)
        direction first second contracted row column := by
  simp only [finiteFrameStructureMetricC0DerivativeTerm, projectedJetStructureDerivative,
    frameFreeNativeCurvatureJet, frameFreeNativeStructureJet, frameFreeNativeStructureDerivativeJet,
    ContinuousMap.add_apply, ContinuousMap.mul_apply]

private theorem koszul_derivative (variation : Model) (point : EffectiveQuotient period hPeriod)
    (direction first second lower : N) :
    finiteFrameKoszulLowerC0Derivative period hPeriod frame baseMetric direction first second lower variation point =
      projectedJetKoszulDerivative (bracket point) (dBracket point) (jet variation point) direction first second lower := by
  simp only [finiteFrameKoszulLowerC0Derivative, projectedJetKoszulDerivative,
    ContinuousMap.smul_apply, ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.sum_apply, smul_eq_mul, structure_derivative]
  rfl

private theorem christoffel (variation : Model) (point : EffectiveQuotient period hPeriod) (upper first second : N) :
    finiteFrameChristoffelC0Coefficient period hPeriod frame baseMetric upper first second variation point =
      projectedJetChristoffel (bracket point) (jet variation point) upper first second := by
  simp only [finiteFrameChristoffelC0Coefficient, projectedJetChristoffel,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply, koszul]
  rfl

private theorem christoffel_derivative (variation : Model) (point : EffectiveQuotient period hPeriod)
    (direction upper first second : N) :
    finiteFrameChristoffelC0Derivative period hPeriod frame baseMetric direction upper first second variation point =
      projectedJetChristoffelDerivative (bracket point) (dBracket point) (jet variation point) direction upper first second := by
  simp only [finiteFrameChristoffelC0Derivative, projectedJetChristoffelDerivative,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply, ContinuousMap.add_apply, koszul, koszul_derivative]
  rfl

theorem frameFreeNativeRiemann_eq_jet (variation : Model) (point : EffectiveQuotient period hPeriod)
    (upper lower first second : N) :
    finiteFrameRiemannC0Coefficient period hPeriod frame baseMetric upper lower first second variation point =
      projectedJetRiemann (bracket point) (dBracket point) (jet variation point) upper lower first second := by
  simp only [finiteFrameRiemannC0Coefficient, projectedJetRiemann, ContinuousMap.add_apply, ContinuousMap.sub_apply,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply, christoffel, christoffel_derivative]
  rfl

theorem frameFreeNativeProjectedRicci_eq_jet (variation : Model) (point : EffectiveQuotient period hPeriod)
    (first second : N) :
    finiteFrameProjectedRicciC0Coefficient period hPeriod frame baseMetric first second variation point =
      projectedJetRicci (bracket point) (dBracket point) (projection point) (jet variation point) first second := by
  simp only [finiteFrameProjectedRicciC0Coefficient, projectedJetRicci,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply, frameFreeNativeRiemann_eq_jet]
  rfl

theorem frameFreeNativeProjectedScalar_eq_jet (variation : Model) (point : EffectiveQuotient period hPeriod) :
    finiteFrameProjectedScalarCurvatureC0 period hPeriod frame baseMetric variation point =
      projectedJetScalarCurvature (bracket point) (dBracket point) (projection point) (jet variation point) := by
  simp only [finiteFrameProjectedScalarCurvatureC0, projectedJetScalarCurvature,
    ContinuousMap.sum_apply, ContinuousMap.mul_apply, frameFreeNativeProjectedRicci_eq_jet]
  rfl

/-- The genuine Einstein density, including canonical volume and the cosmological term. -/
theorem frameFreeNativeEinsteinDensity_eq_jet (couplings : EinsteinHilbertCouplings)
    (variation : Model) (point : EffectiveQuotient period hPeriod) :
    finiteFrameC2EinsteinHilbertDensity period hPeriod frame baseMetric couplings variation point =
      projectedJetEinsteinDensity (bracket point) (dBracket point) (projection point)
        couplings.gravitationalCoupling couplings.cosmologicalConstant
        (finiteFrameCanonicalVolumeC0 period hPeriod frame baseMetric variation point, jet variation point) := by
  simp only [finiteFrameC2EinsteinHilbertDensity, projectedJetEinsteinDensity,
    ContinuousMap.mul_apply, ContinuousMap.smul_apply, ContinuousMap.sub_apply, smul_eq_mul,
    frameFreeNativeProjectedScalar_eq_jet]
  rfl

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeNativeCurvatureJet4D
