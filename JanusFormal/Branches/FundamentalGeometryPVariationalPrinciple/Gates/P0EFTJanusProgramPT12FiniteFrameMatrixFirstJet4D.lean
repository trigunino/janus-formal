import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeNativeInverseVelocity4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2FirstJetLeibniz4D

/-! Exact first spatial jet algebra on an arbitrary generating frame. -/
namespace JanusFormal.P0EFTJanusProgramPT12FiniteFrameMatrixFirstJet4D
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

open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusProgramPT12C2InverseHessian4D
open P0EFTJanusProgramPT12VectorHessianPullback4D
local notation "Matrix" => C2FiniteMatrix period hPeriod frame.count
local notation "product" => c2FiniteMatrixProduct (period := period) (hPeriod := hPeriod) frame.count
local notation "projection" => generalMetricRelativeC2CoreToMatrix period hPeriod frame baseMetric
local notation "inverse" => generalMetricRelativeC2InverseMatrix period hPeriod frame baseMetric

open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverseDerivative4D
open P0EFTJanusProgramPT12FrameFreeNativeInverseJetVariation4D

open scoped BigOperators
open P0EFTJanusFiniteFrameC2FirstJetLeibniz4D

abbrev FiniteMatrixFirstJet (dimension : Nat) :=
  (Fin dimension → Fin dimension → Real) × (Fin dimension → Fin dimension → Fin dimension → Real)

def finiteMatrixFirstJetProduct {dimension : Nat}
    (first second : FiniteMatrixFirstJet dimension) : FiniteMatrixFirstJet dimension :=
  (fun row column => ∑ middle, first.1 row middle * second.1 middle column,
   fun direction row column =>
     (∑ middle, first.2 direction row middle * second.1 middle column) +
     (∑ middle, first.1 row middle * second.2 direction middle column))

theorem finiteMatrixFirstJetProduct_contDiff {dimension : Nat} :
    ContDiff Real ∞ (fun input : FiniteMatrixFirstJet dimension × FiniteMatrixFirstJet dimension =>
      finiteMatrixFirstJetProduct input.1 input.2) := by
  unfold finiteMatrixFirstJetProduct
  fun_prop

/-- Bounded readout of values and ordered first spatial derivatives. -/
def finiteFrameMatrixFirstJetReadout (point : EffectiveQuotient period hPeriod) :
    Matrix →L[Real] FiniteMatrixFirstJet frame.count :=
  let coefficient : Fin frame.count → Fin frame.count → Matrix →L[Real] C2Scalar period hPeriod :=
    fun row column =>
      (ContinuousLinearMap.proj (R := Real) (φ := fun _ : Fin frame.count => C2Scalar period hPeriod) column).comp
        (ContinuousLinearMap.proj (R := Real) (φ := fun _ : Fin frame.count => Fin frame.count → C2Scalar period hPeriod) row)
  let evaluation := ContinuousMap.evalCLM Real point
  let value := evaluation.comp (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod)
  let first := fun direction => evaluation.comp
    (finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame direction)
  (ContinuousLinearMap.pi fun row => ContinuousLinearMap.pi fun column =>
    value.comp (coefficient row column)).prod
    (ContinuousLinearMap.pi fun direction => ContinuousLinearMap.pi fun row => ContinuousLinearMap.pi
      fun column => (first direction).comp (coefficient row column))

variable (point : EffectiveQuotient period hPeriod)
local notation "jetReadout" => finiteFrameMatrixFirstJetReadout period hPeriod frame baseMetric point

theorem finiteFrameMatrixFirstJetReadout_product (first second : Matrix) :
    jetReadout (product first second) =
      finiteMatrixFirstJetProduct (jetReadout first) (jetReadout second) := by
  apply Prod.ext
  · funext row column
    change canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod (product first second row column) point = _
    rw [c2FiniteMatrixProduct_apply, map_sum, ContinuousMap.sum_apply]
    rfl
  · funext direction row column
    change finiteFrameScalarC2FirstDerivative period hPeriod baseMetric frame direction
      (product first second row column) point = _
    rw [c2FiniteMatrixProduct_apply, map_sum, ContinuousMap.sum_apply]
    simp only [finiteFrameScalarC2FirstDerivative_product, ContinuousMap.add_apply,
      ContinuousMap.mul_apply, Finset.sum_add_distrib]
    rfl

def finiteFrameSmoothMatrixFirstJet
    (matrix : SmoothFiniteMatrix period hPeriod frame.count) : FiniteMatrixFirstJet frame.count :=
  (fun row column => matrix row column point,
    fun direction row column => frameDerivative period hPeriod Real frame (matrix row column) point direction)

theorem finiteFrameMatrixFirstJetReadout_smooth
    (matrix : SmoothFiniteMatrix period hPeriod frame.count) :
    jetReadout (smoothFiniteMatrixToC2 period hPeriod frame.count matrix) =
      finiteFrameSmoothMatrixFirstJet period hPeriod frame point matrix := by
  apply Prod.ext
  · rfl
  · funext direction row column
    exact finiteFrameScalarC2FirstDerivative_smooth period hPeriod baseMetric frame direction (matrix row column) point

end
end JanusFormal.P0EFTJanusProgramPT12FiniteFrameMatrixFirstJet4D
