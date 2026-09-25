import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeNativeVolumeJet4D

/-! First variations of the actual inverse on a redundant finite frame. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeNativeInverseVelocity4D
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

theorem frameFreeNativeRelativeInverse_fderiv :
    fderiv Real inverse 0 = -projection := by
  let identity := c2FiniteMatrixIdentity period hPeriod frame.count
  have hInverse : c2FiniteMatrixInverse period hPeriod frame.count identity = identity := by
    have h := c2FiniteMatrixProduct_inverse_right period hPeriod frame.count identity
      (c2FiniteMatrixIdentity_mem_unitSet period hPeriod frame.count)
    simpa only [identity, c2FiniteMatrixProduct_identity_left] using h
  have hDerivative : c2FiniteMatrixInverseDerivative period hPeriod frame.count identity =
      -ContinuousLinearMap.id Real Matrix := by
    apply ContinuousLinearMap.ext
    intro direction
    simp only [c2FiniteMatrixInverseDerivative_apply, hInverse, identity,
      c2FiniteMatrixProduct_identity_left, c2FiniteMatrixProduct_identity_right,
      neg_apply, ContinuousLinearMap.id_apply]
  have hInv := c2FiniteMatrixInverse_hasFDerivAt period hPeriod frame.count identity
    (c2FiniteMatrixIdentity_mem_unitSet period hPeriod frame.count)
  rw [hDerivative] at hInv
  have hOuter : HasFDerivAt (c2FiniteMatrixInverse period hPeriod frame.count)
      (-ContinuousLinearMap.id Real Matrix) (identity + projection 0) := by
    simpa only [(projection).map_zero, add_zero] using hInv
  have hInput : HasFDerivAt (fun variation : Model => identity + projection variation) projection 0 :=
    (projection).hasFDerivAt.const_add identity
  change fderiv Real (fun variation => c2FiniteMatrixInverse period hPeriod frame.count
    (identity + projection variation)) 0 = -projection
  have h := (hOuter.comp 0 hInput).fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.neg_comp, ContinuousLinearMap.id_comp] using h

theorem frameFreeNativeInverseMetric_fderiv (direction : Model) :
    fderiv Real (finiteFrameInverseMetricC2Coefficients period hPeriod frame baseMetric) 0 direction =
      -(product direction.1 (smoothFiniteMatrixToC2 period hPeriod frame.count
        (smoothFiniteFrameInverseMetricMatrix period hPeriod frame baseMetric baseMetric))) := by
  let linear := (product).flip (smoothFiniteMatrixToC2 period hPeriod frame.count
    (smoothFiniteFrameInverseMetricMatrix period hPeriod frame baseMetric baseMetric))
  have hC1 := ((generalMetricRelativeC2InverseMatrix_contDiffOn period hPeriod frame baseMetric).contDiffAt
    ((generalMetricRelativeC2OpenDomain_isOpen period hPeriod frame baseMetric).mem_nhds
      (zero_mem_generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric))).differentiableAt (by simp)
  change fderiv Real (linear ∘ inverse) 0 direction = _
  rw [linearPostFirst linear inverse 0 hC1, frameFreeNativeRelativeInverse_fderiv]
  simp only [ContinuousLinearMap.comp_apply, neg_apply, map_neg]
  rfl

theorem frameFreeNativeInverseMetricReadout_fderiv
    (readout : Matrix →L[Real] Real) (direction : Model) :
    fderiv Real (readout ∘ finiteFrameInverseMetricC2Coefficients period hPeriod frame baseMetric) 0 direction =
      readout (-(product direction.1 (smoothFiniteMatrixToC2 period hPeriod frame.count
        (smoothFiniteFrameInverseMetricMatrix period hPeriod frame baseMetric baseMetric)))) := by
  have hC1 := ((finiteFrameInverseMetricC2Coefficients_contDiffOn period hPeriod frame baseMetric).contDiffAt
    ((generalMetricRelativeC2OpenDomain_isOpen period hPeriod frame baseMetric).mem_nhds
      (zero_mem_generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric))).differentiableAt (by simp)
  rw [linearPostFirst readout _ 0 hC1]
  exact congrArg readout (frameFreeNativeInverseMetric_fderiv period hPeriod frame baseMetric direction)

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeNativeInverseVelocity4D
