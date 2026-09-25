import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeNativeInverseJetVariation4D
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Matrix.Normed

/-! Pointwise finite-dimensional realization of the genuine canonical volume.
The absolute local C² root equals the nonnegative scalar square root. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeNativeVolumeJet4D
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

open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open Filter
open scoped Topology Matrix Matrix.Norms.Elementwise
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixDeterminant4D
open P0EFTJanusVariableMetricCanonicalVolumeSmoothAgreement4D
open P0EFTJanusVariableMetricCanonicalVolumeRatio4D
open P0EFTJanusProgramPT12VectorHessianPullback4D
local notation "MatrixAt" => Matrix (Fin frame.count) (Fin frame.count) Real

/-- Value of the extended relative variation; this is not a Gram inverse. -/
def frameFreeRelativeMatrixAt (point : EffectiveQuotient period hPeriod) : Model →L[Real] MatrixAt :=
  let evaluation := (ContinuousMap.evalCLM Real point).comp
    (canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod)
  ContinuousLinearMap.pi fun row => ContinuousLinearMap.pi fun column =>
    evaluation.comp ((ContinuousLinearMap.proj column).comp
      ((ContinuousLinearMap.proj row).comp (generalMetricRelativeC2CoreToMatrix period hPeriod frame baseMetric)))

def finiteVolumeSymbol {dimension : Nat} (baseVolume : Real)
    (matrix : Matrix (Fin dimension) (Fin dimension) Real) : Real :=
  baseVolume * Real.sqrt (Matrix.det matrix)

theorem finiteVolumeSymbol_contDiffAt_one {dimension : Nat} (baseVolume : Real) :
    ContDiffAt Real ∞ (finiteVolumeSymbol (dimension := dimension) baseVolume) 1 := by
  classical
  have hDet : ContDiff Real ∞ (fun matrix : Matrix (Fin dimension) (Fin dimension) Real => Matrix.det matrix) := by
    simp only [Matrix.det_apply']
    fun_prop
  exact contDiffAt_const.mul (hDet.contDiffAt.sqrt (by simp))

variable (point : EffectiveQuotient period hPeriod)
local notation "readout" => frameFreeRelativeMatrixAt period hPeriod frame baseMetric point
local notation "baseVolume" => globalSmoothMetricVolumeRatio period hPeriod baseMetric point
local notation "symbol" => finiteVolumeSymbol (dimension := frame.count) baseVolume

private theorem determinant_readout (variation : Model) :
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
      (generalMetricRelativeC2Determinant period hPeriod frame baseMetric variation) point =
        Matrix.det (1 + readout variation) := by
  rw [generalMetricRelativeC2Determinant, c2FiniteMatrixDeterminant_continuous_apply]
  congr 1

theorem frameFreeNativeVolume_eq_symbol (variation : Model)
    (hVariation : variation ∈ generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric) :
    finiteFrameCanonicalVolumeC0 period hPeriod frame baseMetric variation point =
      symbol (1 + readout variation) := by
  let root := canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod
    (generalMetricRelativeC2VolumeRatio period hPeriod frame baseMetric variation) point
  have hSquare := congrArg (fun value : C2Scalar period hPeriod =>
    canonicalPhysicalScalarC2JetCoreToContinuous period hPeriod value point)
      (generalMetricRelativeC2VolumeRatio_square period hPeriod frame baseMetric variation hVariation)
  have hRoot : root * root = Matrix.det (1 + readout variation) :=
    hSquare.trans (determinant_readout period hPeriod frame baseMetric point variation)
  change baseVolume * |root| = baseVolume * Real.sqrt _
  rw [← hRoot, Real.sqrt_mul_self_eq_abs]

theorem frameFreeNativeVolume_eventually_eq_symbol :
    (fun variation => finiteFrameCanonicalVolumeC0 period hPeriod frame baseMetric variation point) =ᶠ[𝓝 (0 : Model)]
      (fun variation => symbol (1 + readout variation)) := by
  filter_upwards [(generalMetricRelativeC2VolumeDomain_isOpen period hPeriod frame baseMetric).mem_nhds
    (zero_mem_generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric)] with variation hVariation
  exact frameFreeNativeVolume_eq_symbol period hPeriod frame baseMetric point variation hVariation

theorem frameFreeNativeVolume_hessian (first second : Model) :
    fderiv Real (fderiv Real (fun variation => finiteFrameCanonicalVolumeC0 period hPeriod frame baseMetric variation point))
        0 first second =
      fderiv Real (fderiv Real symbol) 1 (readout first) (readout second) := by
  have h := frameFreeNativeVolume_eventually_eq_symbol period hPeriod frame baseMetric point
  rw [(h.fderiv (𝕜 := Real)).fderiv_eq]
  exact affineHessian symbol 1 readout ((finiteVolumeSymbol_contDiffAt_one baseVolume).of_le (by decide)) first second

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeNativeVolumeJet4D
