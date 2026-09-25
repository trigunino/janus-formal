import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDiffeomorphismFullL2Core4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeMetricFlat4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDeDonderCore4D
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

/-! The complete native diffeomorphism BRST Hessian represented in physical L². -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeDiffeomorphismStrongSmooth4D
set_option autoImplicit false
noncomputable section
open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphPairing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusProgramPT12FPCanonicalFormalAdjoint4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D P0EFTJanusProgramPT12SmoothMatrixL24D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (Q period hPeriod) := borel _
local instance : BorelSpace (Q period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local notation "frame" => finiteSmoothTangentFrame period hPeriod
private abbrev FrameIndex := Fin (finiteSmoothTangentFrame period hPeriod).count
local notation "N" => FrameIndex period hPeriod
local notation "Ghost" => CInfinityDiffeomorphismGhost period hPeriod
local notation "Scalar" => SmoothQuotientField period hPeriod Real
local notation "H" => CanonicalPhysicalBulkL2 period hPeriod
local notation "Ambient" => GlobalDiffeomorphismVectorL2 period hPeriod
variable (metric : SmoothGeneralLorentzMetric period hPeriod)

open P0EFTJanusMappingTorusMetricCartanGlobalAction4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFrameC2CartanFirstJet4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusMappingTorusH1GraphTrace4D
local notation "Tensor" => SmoothSymmetricCovariantTwoTensor period hPeriod
local notation "h" => generalMetricFrameCoefficient period hPeriod frame
local notation "bracket" => finiteFrameStructureCoefficient period hPeriod frame metric
local notation "deriv" => canonicalFrameDerivativeSmooth period hPeriod frame
local notation "mul" => canonicalScalarMul period hPeriod

open P0EFTJanusProgramPT12FrameFreeGhostL2Core4D
open P0EFTJanusProgramPT12FrameFreeCartanScalar4D
open P0EFTJanusProgramPT12FrameFreeFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12FrameFreeDeDonderAdjoint4D
open P0EFTJanusProgramPT12FrameTensorL2Equiv4D
local notation "Core" => FrameFreeGhostL2 period hPeriod metric
local instance ghostGroup : NormedAddCommGroup Core := inferInstance
local instance : SeminormedAddCommGroup Core := (ghostGroup period hPeriod metric).toSeminormedAddCommGroup
local instance : NormedSpace Real Core := inferInstance
local instance : InnerProductSpace Real Core := Submodule.innerProductSpace (𝕜 := Real) _
local notation "q" => frameFreeGhostCoordinate period hPeriod metric
local notation "inc" => frameFreeGhostL2Smooth period hPeriod metric
local notation "incl" => smoothToCanonicalPhysicalBulkL2 period hPeriod

open P0EFTJanusProgramPT12FrameFreeCartanAdjoint4D
open P0EFTJanusProgramPT12FrameFreeDeDonderScalar4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusProgramPGlobalGeneralMetricDiffeomorphismFaddeevPopov4D
open P0EFTJanusFiniteFrameMetricContraction4D
local notation "g" => finiteFrameInverseMetricCoefficient period hPeriod frame metric metric
local notation "Γ" => finiteFrameKoszulChristoffelCoefficient period hPeriod frame metric metric
local notation "derivAdj" => frameFreeFrameDerivativeAdjoint period hPeriod metric frame
local notation "cartanAdj" => frameFreeCartanAdjointColumn period hPeriod metric metric.tensor

open P0EFTJanusProgramPT12FrameFreeDiffeomorphismFPAdjoint4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D
local instance ambientGroup : NormedAddCommGroup Ambient := inferInstance
local instance : SeminormedAddCommGroup Ambient := (ambientGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real Ambient := inferInstance
local instance : InnerProductSpace Real Ambient := inferInstance
local notation "action" => frameFreeDiffeomorphismFPSmoothL2 period hPeriod metric
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismFPSmoothAdjoint4D
open P0EFTJanusProgramPT12FrameFreeDeDonderClosed4D
local notation "TensorL2" => FrameTensorL2Completion period hPeriod frame
local instance tensorGroup : NormedAddCommGroup TensorL2 := inferInstance
local instance : SeminormedAddCommGroup TensorL2 := (tensorGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real TensorL2 := inferInstance
local instance : InnerProductSpace Real TensorL2 := Submodule.innerProductSpace (𝕜 := Real) _
local notation "minimal" => frameFreeDeDonderMinimal period hPeriod metric

open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
local notation "State" => GlobalDiffeomorphismBRSTState period hPeriod
local notation "tensorInc" => frameTensorL2Smooth period hPeriod frame

open P0EFTJanusProgramPT12FrameFreeDeDonderSmoothAdjoint4D
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismFullL2Core4D
open P0EFTJanusProgramPT12FrameFreeMetricFlat4D
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismFPClosed4D
local notation "Full" => FrameFreeDiffeomorphismFullL2 period hPeriod metric
local instance fullGroup : NormedAddCommGroup Full := inferInstance
local instance : SeminormedAddCommGroup Full := (fullGroup period hPeriod metric).toSeminormedAddCommGroup
local instance : NormedSpace Real Full := inferInstance
local instance : InnerProductSpace Real Full := inferInstance
private def ghostPhysicalProjection : Ambient →L[Real] Core :=
  (frameFreeGhostL2Space period hPeriod metric).subtypeL.adjoint
local notation "projection" => ghostPhysicalProjection period hPeriod metric
local notation "flat" => frameFreeMetricFlatPhysical period hPeriod metric
local notation "flatRaw" => frameFreeMetricFlatL2 period hPeriod metric
local notation "deDonder" => globalGeneralMetricDeDonderFrameL2LinearMap period hPeriod metric
local notation "deDonderAdj" => frameFreeDeDonderMultiplierAdjoint period hPeriod metric
local notation "fpMinimal" => frameFreeDiffeomorphismFPMinimal period hPeriod metric

private def fpAdj : Ghost →ₗ[Real] Core :=
  (fpMinimal).adjoint.toFun.comp
    ((globalNormalizedVectorFrameL2LinearMap period hPeriod metric).codRestrict
      (fpMinimal).adjoint.domain (frameFreeDiffeomorphismFPAntighost_mem_adjoint period hPeriod metric))

private theorem projection_pairing (value : Ambient) (vector : Core) :
    inner Real (projection value) vector = inner Real value vector.val :=
  ContinuousLinearMap.adjoint_inner_left (frameFreeGhostL2Space period hPeriod metric).subtypeL vector value

private theorem deDonderAdj_pairing (tensor : Tensor) (vector : Ghost) :
    inner Real (deDonderAdj vector) (tensorInc tensor) =
      inner Real (inc vector).val (deDonder tensor) := by
  have hGreen := frameFreeDeDonderSmoothAdjoint_pairing period hPeriod metric
    ⟨tensorInc tensor, frameFreeDeDonderMinimal_smooth_mem period hPeriod metric tensor⟩
    (globalNormalizedVectorCoordinate period hPeriod metric vector)
  rw [frameFreeDeDonderMinimal_smooth_apply] at hGreen
  rw [frameFreeDeDonderMultiplierAdjoint_apply]
  exact (real_inner_comm _ _).trans (hGreen.symm.trans (real_inner_comm _ _))

private theorem fpAdj_pairing (first second : Ghost) :
    inner Real (fpAdj period hPeriod metric first) (inc second) =
      inner Real (inc first).val (action second) := by
  have hGreen := frameFreeDiffeomorphismFPSmoothAdjoint_pairing period hPeriod metric
    ⟨inc second, frameFreeDiffeomorphismFPMinimal_smooth_mem period hPeriod metric second⟩
    (globalNormalizedVectorCoordinate period hPeriod metric first)
  rw [frameFreeDiffeomorphismFPMinimal_smooth_apply] at hGreen
  change inner Real ((fpMinimal).adjoint ⟨(inc first).val, _⟩) (inc second) = _
  rw [frameFreeDiffeomorphismFPAdjoint_antighost_apply]
  exact (real_inner_comm _ _).trans (hGreen.symm.trans (real_inner_comm _ _))

private theorem flatAdj_pairing (first second : Core) :
    inner Real ((flat).adjoint first) second = inner Real first.val (flatRaw second) :=
  (ContinuousLinearMap.adjoint_inner_left flat second first).trans
    ((real_inner_comm _ _).trans
      ((frameFreeMetricFlatPhysical_pairing period hPeriod metric second first).trans (real_inner_comm _ _)))

private def lpPair {S E F : Type*} [AddCommGroup S] [Module Real S]
    [NormedAddCommGroup E] [NormedSpace Real E] [NormedAddCommGroup F] [NormedSpace Real F]
    (first : S →ₗ[Real] E) (second : S →ₗ[Real] F) : S →ₗ[Real] WithLp 2 (E × F) :=
  (WithLp.prodContinuousLinearEquiv 2 Real E F).symm.toLinearMap.comp (first.prod second)

private def bProjection : State →ₗ[Real] Ghost where
  toFun state := state.nonminimal.nakanishiLautrup.field
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private def aProjection : State →ₗ[Real] Ghost where
  toFun state := state.nonminimal.antighost.field
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
private def cProjection : State →ₗ[Real] Ghost where
  toFun state := state.nonminimal.ghost.field
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Native columns retain the two negative ghost terms and the symmetric B-flat term. -/
def frameFreeDiffeomorphismStrongSmooth : State →ₗ[Real] Full :=
  lpPair
    (lpPair
      ((deDonderAdj).comp (bProjection period hPeriod))
      (((projection).toLinearMap.comp deDonder).comp
          (globalDiffeomorphismMetricPerturbationProjectionLinearMap period hPeriod) -
        (1 / 2 : Real) • (((flat + (flat).adjoint).toLinearMap.comp inc).comp (bProjection period hPeriod))))
    (lpPair
      (-((projection).toLinearMap.comp action).comp (cProjection period hPeriod))
      (-(fpAdj period hPeriod metric).comp (aProjection period hPeriod)))

/-- Equality with the original same-action BRST Hessian, without a graph-norm Riesz replacement. -/
theorem frameFreeDiffeomorphismStrongSmooth_pairing (first second : State) :
    inner Real (frameFreeDiffeomorphismStrongSmooth period hPeriod metric first)
      (frameFreeDiffeomorphismFullL2Smooth period hPeriod metric second) =
    globalDiffeomorphismOffShellHessian period hPeriod metric
      (globalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric first)
      (globalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric second) := by
  simp only [WithLp.prod_inner_apply, globalDiffeomorphismOffShellHessian_apply,
    globalDiffeomorphismOffShellDeDonderProjection_smooth, globalDiffeomorphismOffShellBProjection_smooth,
    globalDiffeomorphismOffShellBFlatProjection_smooth, globalDiffeomorphismOffShellAntighostProjection_smooth,
    globalDiffeomorphismOffShellFPProjection_smooth]
  change (inner Real (deDonderAdj first.nonminimal.nakanishiLautrup.field) (tensorInc second.metricPerturbation) +
    inner Real (projection (deDonder first.metricPerturbation) -
      (1 / 2 : Real) • (flat (inc first.nonminimal.nakanishiLautrup.field) +
        (flat).adjoint (inc first.nonminimal.nakanishiLautrup.field))) (inc second.nonminimal.nakanishiLautrup.field)) +
    (inner Real (-projection (action first.nonminimal.ghost.field)) (inc second.nonminimal.antighost.field) +
      inner Real (-(fpAdj period hPeriod metric first.nonminimal.antighost.field)) (inc second.nonminimal.ghost.field)) = _
  simp only [inner_sub_left, real_inner_smul_left, inner_add_left, inner_neg_left,
    deDonderAdj_pairing, projection_pairing, frameFreeMetricFlatPhysical_pairing,
    flatAdj_pairing, fpAdj_pairing, frameFreeMetricFlatL2_smooth]
  change (inner Real (globalNormalizedVectorFrameL2LinearMap period hPeriod metric first.nonminimal.nakanishiLautrup.field)
      (deDonder second.metricPerturbation) +
    (inner Real (deDonder first.metricPerturbation)
      (globalNormalizedVectorFrameL2LinearMap period hPeriod metric second.nonminimal.nakanishiLautrup.field) -
      (1 / 2 : Real) * (inner Real
        (globalSmoothMetricFlatFrameL2LinearMap period hPeriod metric first.nonminimal.nakanishiLautrup.field)
        (globalNormalizedVectorFrameL2LinearMap period hPeriod metric second.nonminimal.nakanishiLautrup.field) +
      inner Real (globalNormalizedVectorFrameL2LinearMap period hPeriod metric first.nonminimal.nakanishiLautrup.field)
        (globalSmoothMetricFlatFrameL2LinearMap period hPeriod metric second.nonminimal.nakanishiLautrup.field)))) +
    (-inner Real (globalDiffeomorphismFPL2LinearMap period hPeriod metric first.nonminimal.ghost)
      (globalNormalizedVectorFrameL2LinearMap period hPeriod metric second.nonminimal.antighost.field) +
     -inner Real (globalNormalizedVectorFrameL2LinearMap period hPeriod metric first.nonminimal.antighost.field)
       (globalDiffeomorphismFPL2LinearMap period hPeriod metric second.nonminimal.ghost)) = _
  ring

theorem frameFreeDiffeomorphismStrongSmooth_symmetric (first second : State) :
    inner Real (frameFreeDiffeomorphismStrongSmooth period hPeriod metric first)
      (frameFreeDiffeomorphismFullL2Smooth period hPeriod metric second) =
    inner Real (frameFreeDiffeomorphismFullL2Smooth period hPeriod metric first)
      (frameFreeDiffeomorphismStrongSmooth period hPeriod metric second) :=
  (frameFreeDiffeomorphismStrongSmooth_pairing period hPeriod metric first second).trans
    ((globalDiffeomorphismOffShellHessian_comm period hPeriod metric _ _).trans
      ((frameFreeDiffeomorphismStrongSmooth_pairing period hPeriod metric second first).symm.trans (real_inner_comm _ _)))

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeDiffeomorphismStrongSmooth4D
