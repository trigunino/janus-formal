import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2MobileMaxwellAction4D

/-! The native Maxwell action at a fixed completed metric is a genuine
continuous bilinear form on potential C² coefficients, evaluated diagonally. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeMaxwellBilinear4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff BigOperators

private def weightedProduct {E A : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedCommRing A] [NormedAlgebra Real A] (weight : A) (first second : E →L[Real] A) :
    E →L[Real] E →L[Real] A :=
  (ContinuousLinearMap.compL Real E A A (ContinuousLinearMap.mul Real A weight)).comp
    ((ContinuousLinearMap.mul Real A).bilinearComp first second)

open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusFiniteFrameScalarC2Derivatives4D P0EFTJanusFiniteFrameC2KoszulConnection4D
open P0EFTJanusFiniteFrameC2InverseMetricCoefficients4D P0EFTJanusFiniteFrameCovectorC2Projection4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D P0EFTJanusFiniteFrameC2MaxwellCurvature4D
open P0EFTJanusFiniteFrameC2MaxwellPairing4D P0EFTJanusFiniteFrameC2CanonicalVolume4D
open P0EFTJanusFiniteFrameC2MobileMaxwellAction4D P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
attribute [local instance 2000]
  NonUnitalNormedRing.toNormedAddCommGroup NormedAlgebra.toNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Q period hPeriod) := borel _
local instance : BorelSpace (Q period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance
variable (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "Gauge" => FiniteFrameAbelianGaugeC2Core period hPeriod frame
local notation "C0" => C(Q period hPeriod, Real)
local instance : NormedAddCommGroup Gauge := inferInstance
local instance : NormedSpace Real Gauge := inferInstance
local instance : NormedAddCommGroup (Gauge →L[Real] C0) := inferInstance
local instance : NormedSpace Real (Gauge →L[Real] C0) := inferInstance
local instance : NormedAddCommGroup (Gauge →L[Real] Gauge →L[Real] C0) := inferInstance
local instance : NormedSpace Real (Gauge →L[Real] Gauge →L[Real] C0) := inferInstance
local instance : NormedAddCommGroup (Gauge →L[Real] Real) := inferInstance
local instance : NormedSpace Real (Gauge →L[Real] Real) := inferInstance
local instance : NormedAddCommGroup (Gauge →L[Real] Gauge →L[Real] Real) := inferInstance
local instance : NormedSpace Real (Gauge →L[Real] Gauge →L[Real] Real) := inferInstance

def frameFreeMaxwellCurvatureCLM (component : Fin 2) (first second : Fin frame.count) : Gauge →L[Real] C0 :=
  (((finiteFrameScalarC2FirstDerivative period hPeriod metric frame first).comp
        (finiteFrameGaugePotentialCoefficientCLM period hPeriod frame component second) -
      (finiteFrameScalarC2FirstDerivative period hPeriod metric frame second).comp
        (finiteFrameGaugePotentialCoefficientCLM period hPeriod frame component first)) -
    ∑ upper : Fin frame.count,
      (ContinuousLinearMap.mul Real C0
        (finiteFrameStructureC0Coefficient period hPeriod frame metric first second upper)).comp
        ((canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod).comp
          (finiteFrameGaugePotentialCoefficientCLM period hPeriod frame component upper))).comp
    (finiteFrameGaugeC2Projection period hPeriod frame metric)

theorem frameFreeMaxwellCurvatureCLM_apply (component : Fin 2) (first second : Fin frame.count)
    (potential : FiniteFrameAbelianGaugeC2Core period hPeriod frame) :
    frameFreeMaxwellCurvatureCLM period hPeriod frame metric component first second potential =
      finiteFrameProjectedGaugeCurvatureC0Coefficient period hPeriod frame metric potential component first second := by
  simp only [frameFreeMaxwellCurvatureCLM, finiteFrameProjectedGaugeCurvatureC0Coefficient,
    finiteFrameGaugeCurvatureC0Coefficient, finiteFrameGaugePotentialCoefficientCLM,
    ContinuousLinearMap.comp_apply, sub_apply, sum_apply,
    ContinuousLinearMap.mul_apply', ContinuousLinearMap.proj_apply]

def frameFreeMaxwellContractionBilinear
    (variation : GeneralMetricRelativeC2Core period hPeriod frame metric) : Gauge →L[Real] Gauge →L[Real] C0 :=
  ∑ component : Fin 2, ∑ first : Fin frame.count, ∑ second : Fin frame.count,
    ∑ raisedFirst : Fin frame.count, ∑ raisedSecond : Fin frame.count,
      weightedProduct
        (finiteFrameInverseMetricC0Coefficient period hPeriod frame metric first raisedFirst variation *
          finiteFrameInverseMetricC0Coefficient period hPeriod frame metric second raisedSecond variation)
        (frameFreeMaxwellCurvatureCLM period hPeriod frame metric component first second)
        (frameFreeMaxwellCurvatureCLM period hPeriod frame metric component raisedFirst raisedSecond)

theorem frameFreeMaxwellContractionBilinear_diagonal
    (variation : GeneralMetricRelativeC2Core period hPeriod frame metric)
    (potential : FiniteFrameAbelianGaugeC2Core period hPeriod frame) :
    frameFreeMaxwellContractionBilinear period hPeriod frame metric variation potential potential =
      finiteFrameMaxwellPairingC0 period hPeriod frame metric variation potential := by
  simp only [frameFreeMaxwellContractionBilinear, finiteFrameMaxwellPairingC0, weightedProduct,
    sum_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    ContinuousLinearMap.bilinearComp_apply, ContinuousLinearMap.mul_apply',
    frameFreeMaxwellCurvatureCLM_apply, mul_assoc]

/-- The exact native factor `-1/4`, mobile metric density, and canonical integral. -/
def frameFreeMaxwellBilinear
    (variation : GeneralMetricRelativeC2Core period hPeriod frame metric) : Gauge →L[Real] Gauge →L[Real] Real :=
  (ContinuousLinearMap.compL Real Gauge C0 Real (finiteFrameBRSTCanonicalIntegralCLM period hPeriod)).comp
    ((ContinuousLinearMap.compL Real Gauge C0 C0
      (ContinuousLinearMap.mul Real C0 (finiteFrameCanonicalVolumeC0 period hPeriod frame metric variation))).comp
      ((-(1 / 4 : Real)) • frameFreeMaxwellContractionBilinear period hPeriod frame metric variation))

theorem frameFreeMobileMaxwellAction_eq_bilinear
    (variation : GeneralMetricRelativeC2Core period hPeriod frame metric)
    (potential : FiniteFrameAbelianGaugeC2Core period hPeriod frame) :
    finiteFrameC2MobileMaxwellAction period hPeriod frame metric (variation, potential) =
      frameFreeMaxwellBilinear period hPeriod frame metric variation potential potential := by
  change finiteFrameBRSTCanonicalIntegralCLM period hPeriod
      (finiteFrameCanonicalVolumeC0 period hPeriod frame metric variation *
        ((-(1 / 4 : Real)) • finiteFrameMaxwellPairingC0 period hPeriod frame metric variation potential)) = _
  simp only [frameFreeMaxwellBilinear, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.mul_apply', smul_apply,
    frameFreeMaxwellContractionBilinear_diagonal]

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeMaxwellBilinear4D
