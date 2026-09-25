import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeNativeMetricJetVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12C2InverseHessian4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12VectorHessianPullback4D

/-! Native inverse variations for a redundant generating frame. Only the
extended relative endomorphism is inverted, never the redundant Gram matrix. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeNativeInverseJetVariation4D
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

theorem frameFreeNativeRelativeInverse_hessian (first second : Model) :
    fderiv Real (fderiv Real inverse) 0 first second =
      product second.1 first.1 + product first.1 second.1 := by
  have hC2 : ContDiffAt Real 2 (c2FiniteMatrixInverse period hPeriod frame.count)
      (c2FiniteMatrixIdentity period hPeriod frame.count) :=
    ((c2FiniteMatrixInverse_contDiffOn period hPeriod frame.count).contDiffAt
      ((c2FiniteMatrixUnitSet_isOpen period hPeriod frame.count).mem_nhds
        (c2FiniteMatrixIdentity_mem_unitSet period hPeriod frame.count))).of_le (by decide)
  change fderiv Real (fderiv Real (fun variation => c2FiniteMatrixInverse period hPeriod frame.count
    (c2FiniteMatrixIdentity period hPeriod frame.count + projection variation))) 0 first second = _
  rw [affineHessian _ _ projection hC2]
  exact c2Inverse_hessian_identity period hPeriod frame.count first.1 second.1

private theorem nativeInverse_contDiffAt : ContDiffAt Real 2 inverse 0 :=
  ((generalMetricRelativeC2InverseMatrix_contDiffOn period hPeriod frame baseMetric).contDiffAt
    ((generalMetricRelativeC2OpenDomain_isOpen period hPeriod frame baseMetric).mem_nhds
      (zero_mem_generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric))).of_le (by decide)

/-- Exact second variation of the genuine inverse metric coefficients. -/
theorem frameFreeNativeInverseMetric_hessian (first second : Model) :
    fderiv Real (fderiv Real (finiteFrameInverseMetricC2Coefficients period hPeriod frame baseMetric)) 0 first second =
      product (product second.1 first.1 + product first.1 second.1)
        (smoothFiniteMatrixToC2 period hPeriod frame.count
          (smoothFiniteFrameInverseMetricMatrix period hPeriod frame baseMetric baseMetric)) := by
  let linear := (product).flip (smoothFiniteMatrixToC2 period hPeriod frame.count
    (smoothFiniteFrameInverseMetricMatrix period hPeriod frame baseMetric baseMetric))
  change fderiv Real (fderiv Real (linear ∘ inverse)) 0 first second = _
  rw [linearPostHessian linear inverse 0 first second (nativeInverse_contDiffAt period hPeriod frame baseMetric)]
  exact congrArg linear (frameFreeNativeRelativeInverse_hessian period hPeriod frame baseMetric first second)

/-- Covers coefficient evaluation and every ordered first spatial derivative. -/
theorem frameFreeNativeInverseMetricReadout_hessian
    (readout : Matrix →L[Real] Real) (first second : Model) :
    fderiv Real (fderiv Real (readout ∘ finiteFrameInverseMetricC2Coefficients period hPeriod frame baseMetric)) 0 first second =
      readout (product (product second.1 first.1 + product first.1 second.1)
        (smoothFiniteMatrixToC2 period hPeriod frame.count
          (smoothFiniteFrameInverseMetricMatrix period hPeriod frame baseMetric baseMetric))) := by
  have hC2 : ContDiffAt Real 2 (finiteFrameInverseMetricC2Coefficients period hPeriod frame baseMetric) 0 :=
    ((finiteFrameInverseMetricC2Coefficients_contDiffOn period hPeriod frame baseMetric).contDiffAt
      ((generalMetricRelativeC2OpenDomain_isOpen period hPeriod frame baseMetric).mem_nhds
        (zero_mem_generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric))).of_le (by decide)
  rw [linearPostHessian readout _ 0 first second hC2]
  exact congrArg readout (frameFreeNativeInverseMetric_hessian period hPeriod frame baseMetric first second)

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeNativeInverseJetVariation4D
