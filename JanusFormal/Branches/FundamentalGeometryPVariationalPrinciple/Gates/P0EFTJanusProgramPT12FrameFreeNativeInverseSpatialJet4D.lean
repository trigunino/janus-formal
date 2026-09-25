import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FiniteFrameMatrixFirstJet4D

/-! Finite first-jet formulas for both variations of the native inverse metric. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeNativeInverseSpatialJet4D
set_option autoImplicit false
noncomputable section
attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace
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

private theorem linearPostFirst {E F G : Type*}
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (linear : F →L[Real] G) (field : E → F) (point : E)
    (h : DifferentiableAt Real field point) :
    fderiv Real (linear ∘ field) point = linear.comp (fderiv Real field point) :=
  (linear.hasFDerivAt.comp point h.hasFDerivAt).fderiv

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

open P0EFTJanusProgramPT12FrameFreeNativeInverseVelocity4D
open P0EFTJanusProgramPT12FiniteFrameMatrixFirstJet4D
local notation "MatrixJet" => FiniteMatrixFirstJet frame.count

def frameFreeNativeInverseFirstJet (variation : Model) (point : EffectiveQuotient period hPeriod) : MatrixJet :=
  (fun row column => finiteFrameInverseMetricC0Coefficient period hPeriod frame baseMetric row column variation point,
    fun direction row column => finiteFrameInverseMetricC0FirstDerivative period hPeriod frame baseMetric direction row column variation point)

variable (point : EffectiveQuotient period hPeriod)
local notation "jetReadout" => finiteFrameMatrixFirstJetReadout period hPeriod frame baseMetric point
local notation "nativeInverse" => finiteFrameInverseMetricC2Coefficients period hPeriod frame baseMetric
local notation "jetProduct" => finiteMatrixFirstJetProduct (dimension := frame.count)
local notation "baseInverse" => smoothFiniteMatrixToC2 period hPeriod frame.count
  (smoothFiniteFrameInverseMetricMatrix period hPeriod frame baseMetric baseMetric)

theorem frameFreeNativeInverseFirstJet_eq_readout (variation : Model) :
    frameFreeNativeInverseFirstJet period hPeriod frame baseMetric variation point =
      jetReadout (nativeInverse variation) := rfl

private theorem nativeInverse_contDiffAt : ContDiffAt Real 2 nativeInverse 0 :=
  ((finiteFrameInverseMetricC2Coefficients_contDiffOn period hPeriod frame baseMetric).contDiffAt
    ((generalMetricRelativeC2OpenDomain_isOpen period hPeriod frame baseMetric).mem_nhds
      (zero_mem_generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric))).of_le (by decide)

theorem frameFreeNativeInverseFirstJet_fderiv (direction : Model) :
    fderiv Real (fun variation => frameFreeNativeInverseFirstJet period hPeriod frame baseMetric variation point) 0 direction =
      -(jetProduct (jetReadout direction.1) (jetReadout baseInverse)) := by
  change fderiv Real (jetReadout ∘ nativeInverse) 0 direction = _
  rw [linearPostFirst jetReadout nativeInverse 0
    ((nativeInverse_contDiffAt period hPeriod frame baseMetric).differentiableAt (by norm_num))]
  change jetReadout (fderiv Real nativeInverse 0 direction) = _
  rw [frameFreeNativeInverseMetric_fderiv, (jetReadout).map_neg,
    finiteFrameMatrixFirstJetReadout_product]

theorem frameFreeNativeInverseFirstJet_hessian (first second : Model) :
    fderiv Real (fderiv Real (fun variation => frameFreeNativeInverseFirstJet period hPeriod frame baseMetric variation point))
        0 first second =
      jetProduct (jetProduct (jetReadout second.1) (jetReadout first.1) +
        jetProduct (jetReadout first.1) (jetReadout second.1)) (jetReadout baseInverse) := by
  change fderiv Real (fderiv Real (jetReadout ∘ nativeInverse)) 0 first second = _
  rw [linearPostHessian jetReadout nativeInverse 0 first second
    (nativeInverse_contDiffAt period hPeriod frame baseMetric)]
  rw [frameFreeNativeInverseMetric_hessian, finiteFrameMatrixFirstJetReadout_product,
    (jetReadout).map_add, finiteFrameMatrixFirstJetReadout_product,
    finiteFrameMatrixFirstJetReadout_product]

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeNativeInverseSpatialJet4D
