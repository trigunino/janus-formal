import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeNativeEinsteinJetHessian4D

/-! Affine raw metric jets on the genuine redundant-frame C² core. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeNativeMetricJetVariation4D
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

open P0EFTJanusProgramPT12FrameFreeNativeCurvatureJet4D
open P0EFTJanusProgramPT12NonlinearHessianPullback4D
local instance : NormedAddCommGroup Model := inferInstance
local instance : NormedSpace Real Model := Submodule.normedSpace _

open P0EFTJanusFiniteFrameScalarC2Derivatives4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
local notation "RawJet" => MetricMatrix frame.count × MetricFirstJet frame.count × MetricSecondJet frame.count

private def tensorCoefficientReadout (row column : N) : Model →L[Real] C2Scalar period hPeriod :=
  (ContinuousLinearMap.proj column).comp
    ((ContinuousLinearMap.proj row).comp
      (finiteFrameRelativeC2ToTensorCoefficients period hPeriod frame baseMetric))

/-- The value, ordered first jets and ordered second jets of a metric variation. -/
def frameFreeMetricRawJetReadout (point : EffectiveQuotient period hPeriod) : Model →L[Real] RawJet :=
  let evaluation := ContinuousMap.evalCLM Real point
  let coefficient := tensorCoefficientReadout period hPeriod frame baseMetric
  let value := evaluation.comp (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod)
  let first := fun direction => evaluation.comp (finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame direction)
  let second := fun outer innerIndex => evaluation.comp (finiteFrameScalarC2SecondDerivative period hPeriod baseMetric frame outer innerIndex)
  (ContinuousLinearMap.pi fun row => ContinuousLinearMap.pi fun column => value.comp (coefficient row column)).prod
    ((ContinuousLinearMap.pi fun direction => ContinuousLinearMap.pi fun row => ContinuousLinearMap.pi
      fun column => (first direction).comp (coefficient row column)).prod
        (ContinuousLinearMap.pi fun outer => ContinuousLinearMap.pi fun innerIndex => ContinuousLinearMap.pi
          fun row => ContinuousLinearMap.pi fun column => (second outer innerIndex).comp (coefficient row column)))

def frameFreeNativeMetricRawJet (variation : Model) (point : EffectiveQuotient period hPeriod) : RawJet :=
  (fun row column => finiteFrameMetricC0Coefficient period hPeriod frame baseMetric row column variation point,
    (fun direction row column => finiteFrameMetricC0FirstDerivative period hPeriod frame baseMetric direction row column variation point),
    fun outer innerIndex row column => finiteFrameMetricC0SecondDerivative period hPeriod frame baseMetric outer innerIndex row column variation point)

variable (point : EffectiveQuotient period hPeriod)

private theorem scalarReadout_affine (readout : C2Scalar period hPeriod →L[Real] Real)
    (row column : N) (variation : Model) :
    readout (finiteFrameMetricC2Coefficients period hPeriod frame baseMetric variation row column) =
      readout (finiteFrameMetricC2Coefficients period hPeriod frame baseMetric 0 row column) +
        readout (tensorCoefficientReadout period hPeriod frame baseMetric row column variation) := by
  rw [finiteFrameMetricC2Coefficients_zero]
  change readout (_ + _) = _ + _
  exact readout.map_add _ _

theorem frameFreeNativeMetricRawJet_eq_affine (variation : Model) :
    frameFreeNativeMetricRawJet period hPeriod frame baseMetric variation point =
      frameFreeNativeMetricRawJet period hPeriod frame baseMetric 0 point +
        frameFreeMetricRawJetReadout period hPeriod frame baseMetric point variation := by
  apply Prod.ext
  · funext row column
    exact scalarReadout_affine period hPeriod frame baseMetric
      ((ContinuousMap.evalCLM Real point).comp (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod)) row column variation
  · apply Prod.ext
    · funext direction row column
      exact scalarReadout_affine period hPeriod frame baseMetric
        ((ContinuousMap.evalCLM Real point).comp (finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame direction)) row column variation
    · funext outer innerIndex row column
      exact scalarReadout_affine period hPeriod frame baseMetric
        ((ContinuousMap.evalCLM Real point).comp (finiteFrameScalarC2SecondDerivative period hPeriod baseMetric frame outer innerIndex)) row column variation

theorem frameFreeNativeMetricRawJet_fderiv (variation : Model) :
    fderiv Real (fun current => frameFreeNativeMetricRawJet period hPeriod frame baseMetric current point) variation =
      frameFreeMetricRawJetReadout period hPeriod frame baseMetric point := by
  have h := funext (frameFreeNativeMetricRawJet_eq_affine period hPeriod frame baseMetric point)
  rw [h]
  exact ((frameFreeMetricRawJetReadout period hPeriod frame baseMetric point).hasFDerivAt.const_add _).fderiv

theorem frameFreeNativeMetricRawJet_hessian_zero (variation : Model) :
    fderiv Real (fderiv Real (fun current => frameFreeNativeMetricRawJet period hPeriod frame baseMetric current point)) variation = 0 := by
  have h := funext (frameFreeNativeMetricRawJet_fderiv period hPeriod frame baseMetric point)
  rw [h]
  exact (hasFDerivAt_const (𝕜 := Real) (frameFreeMetricRawJetReadout period hPeriod frame baseMetric point) variation).fderiv

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeNativeMetricJetVariation4D
