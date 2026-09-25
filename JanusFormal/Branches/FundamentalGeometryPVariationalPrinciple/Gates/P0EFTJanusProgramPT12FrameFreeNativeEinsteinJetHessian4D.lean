import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeNativeCurvatureJet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NonlinearHessianPullback4D

/-! Genuine second variation of the native projected Einstein density.
The nonlinear volume, inverse metric and inverse-derivative accelerations are retained. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeNativeEinsteinJetHessian4D
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

def frameFreeNativeEinsteinFeatures (variation : Model) (point : EffectiveQuotient period hPeriod) : Real × Jet :=
  (finiteFrameCanonicalVolumeC0 period hPeriod frame baseMetric variation point,
    frameFreeNativeCurvatureJet period hPeriod frame baseMetric variation point)

variable (point : EffectiveQuotient period hPeriod)

private theorem eval_contDiffAt {order : ℕ∞ω} (field : Model → C0Scalar period hPeriod)
    (h : ContDiffAt Real order field 0) : ContDiffAt Real order (fun variation => field variation point) 0 := by
  let evaluation : C0Scalar period hPeriod →L[Real] Real := ContinuousMap.evalCLM Real point
  exact evaluation.contDiff.contDiffAt.comp 0 h

theorem frameFreeNativeCurvatureJet_contDiffAt_zero :
    ContDiffAt Real ∞ (fun variation => frameFreeNativeCurvatureJet period hPeriod frame baseMetric variation point) 0 := by
  have hOpen := (generalMetricRelativeC2OpenDomain_isOpen period hPeriod frame baseMetric).mem_nhds
    (zero_mem_generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric)
  have hValue (row column : N) := eval_contDiffAt period hPeriod frame baseMetric point _
    (finiteFrameMetricC0Coefficient_contDiff period hPeriod frame baseMetric row column).contDiffAt
  have hInverse (row column : N) := eval_contDiffAt period hPeriod frame baseMetric point _
    ((finiteFrameInverseMetricC0Coefficient_contDiffOn period hPeriod frame baseMetric row column).contDiffAt hOpen)
  have hFirst (direction row column : N) := eval_contDiffAt period hPeriod frame baseMetric point _
    (finiteFrameMetricC0FirstDerivative_contDiff period hPeriod frame baseMetric direction row column).contDiffAt
  have hSecond (outer innerIndex row column : N) := eval_contDiffAt period hPeriod frame baseMetric point _
    (finiteFrameMetricC0SecondDerivative_contDiff period hPeriod frame baseMetric outer innerIndex row column).contDiffAt
  have hInverseFirst (direction row column : N) := eval_contDiffAt period hPeriod frame baseMetric point _
    ((finiteFrameInverseMetricC0FirstDerivative_contDiffOn period hPeriod frame baseMetric direction row column).contDiffAt hOpen)
  exact (contDiffAt_pi.mpr fun row => contDiffAt_pi.mpr fun column => hValue row column).prodMk
    ((contDiffAt_pi.mpr fun row => contDiffAt_pi.mpr fun column => hInverse row column).prodMk
      ((contDiffAt_pi.mpr fun direction => contDiffAt_pi.mpr fun row => contDiffAt_pi.mpr
        fun column => hFirst direction row column).prodMk
        ((contDiffAt_pi.mpr fun outer => contDiffAt_pi.mpr fun innerIndex => contDiffAt_pi.mpr
          fun row => contDiffAt_pi.mpr fun column => hSecond outer innerIndex row column).prodMk
            (contDiffAt_pi.mpr fun direction => contDiffAt_pi.mpr fun row => contDiffAt_pi.mpr
              fun column => hInverseFirst direction row column))))

theorem frameFreeNativeEinsteinFeatures_contDiffAt_zero :
    ContDiffAt Real 2 (fun variation => frameFreeNativeEinsteinFeatures period hPeriod frame baseMetric variation point) 0 := by
  have hVolume := eval_contDiffAt period hPeriod frame baseMetric point _
    ((finiteFrameCanonicalVolumeC0_contDiffOn_two period hPeriod frame baseMetric).contDiffAt
      ((generalMetricRelativeC2VolumeDomain_isOpen period hPeriod frame baseMetric).mem_nhds
        (zero_mem_generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric)))
  exact hVolume.prodMk ((frameFreeNativeCurvatureJet_contDiffAt_zero period hPeriod frame baseMetric point).of_le (by decide))

variable (couplings : EinsteinHilbertCouplings)
local notation "features" => fun variation => frameFreeNativeEinsteinFeatures period hPeriod frame baseMetric variation point
local notation "symbol" => projectedJetEinsteinDensity
  (frameFreeNativeStructureJet period hPeriod frame baseMetric point)
  (frameFreeNativeStructureDerivativeJet period hPeriod frame baseMetric point)
  (frameFreeNativeTraceProjection period hPeriod frame baseMetric point)
  couplings.gravitationalCoupling couplings.cosmologicalConstant

/-- Exact chain rule for the physical second variation, including the feature acceleration term. -/
theorem frameFreeNativeEinsteinDensity_hessian_eq_jet (first second : Model) :
    fderiv Real (fderiv Real (fun variation =>
      finiteFrameC2EinsteinHilbertDensity period hPeriod frame baseMetric couplings variation point)) 0 first second =
      fderiv Real (fderiv Real symbol) (features 0)
        (fderiv Real features 0 first) (fderiv Real features 0 second) +
      fderiv Real symbol (features 0) (fderiv Real (fderiv Real features) 0 first second) := by
  have hAction : (fun variation => finiteFrameC2EinsteinHilbertDensity period hPeriod frame baseMetric couplings variation point) =
      symbol ∘ features := by
    funext variation
    exact frameFreeNativeEinsteinDensity_eq_jet period hPeriod frame baseMetric couplings variation point
  refine (congrArg (fun action : Model → Real => fderiv Real (fderiv Real action) 0 first second) hAction).trans ?_
  exact nonlinearHessian symbol features 0 first second
    ((projectedJetEinsteinDensity_contDiff _ _ _ _ _).contDiffAt.of_le (by decide))
    (frameFreeNativeEinsteinFeatures_contDiffAt_zero period hPeriod frame baseMetric point)

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeNativeEinsteinJetHessian4D
