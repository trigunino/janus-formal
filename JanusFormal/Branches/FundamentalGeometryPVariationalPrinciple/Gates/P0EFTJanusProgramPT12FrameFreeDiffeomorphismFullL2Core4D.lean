import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDeDonderSmoothAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDeDonderCore4D
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

/-! Physical tensor and three vector slots for the native diffeomorphism BRST Hessian. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeDiffeomorphismFullL2Core4D
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

abbrev FrameFreeDiffeomorphismFullL2 := WithLp 2 (WithLp 2 (TensorL2 × Core) × WithLp 2 (Core × Core))
local notation "Full" => FrameFreeDiffeomorphismFullL2 period hPeriod metric
local instance fullGroup : NormedAddCommGroup Full := inferInstance
local instance : SeminormedAddCommGroup Full := (fullGroup period hPeriod metric).toSeminormedAddCommGroup
local instance : NormedSpace Real Full := inferInstance
local instance : InnerProductSpace Real Full := inferInstance
instance frameFreeDiffeomorphismFullL2_complete : CompleteSpace Full := inferInstance

/-- The physical norm contains h, B, antighost and ghost, without derivative features. -/
def frameFreeDiffeomorphismFullL2Smooth : State →ₗ[Real] Full where
  toFun state := WithLp.toLp 2
    (WithLp.toLp 2 (tensorInc state.metricPerturbation, inc state.nonminimal.nakanishiLautrup.field),
     WithLp.toLp 2 (inc state.nonminimal.antighost.field, inc state.nonminimal.ghost.field))
  map_add' x y := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · apply WithLp.ofLp_injective 2
      exact Prod.ext ((tensorInc).map_add _ _) ((inc).map_add _ _)
    · apply WithLp.ofLp_injective 2
      exact Prod.ext ((inc).map_add _ _) ((inc).map_add _ _)
  map_smul' scalar state := by
    apply WithLp.ofLp_injective 2
    apply Prod.ext
    · apply WithLp.ofLp_injective 2
      exact Prod.ext ((tensorInc).map_smul scalar _) ((inc).map_smul scalar _)
    · apply WithLp.ofLp_injective 2
      exact Prod.ext ((inc).map_smul scalar _) ((inc).map_smul scalar _)

theorem frameFreeDiffeomorphismFullL2Smooth_injective :
    Function.Injective (frameFreeDiffeomorphismFullL2Smooth period hPeriod metric) := by
  intro first second hEqual
  have hT := globalGeneralMetricTensorFrameL2LinearMap_injective period hPeriod
    (congrArg (fun x : Full => x.fst.fst.val) hEqual)
  have hB := frameFreeGhostL2Smooth_injective period hPeriod metric (congrArg (fun x : Full => x.fst.snd) hEqual)
  have hA := frameFreeGhostL2Smooth_injective period hPeriod metric (congrArg (fun x : Full => x.snd.fst) hEqual)
  have hC := frameFreeGhostL2Smooth_injective period hPeriod metric (congrArg (fun x : Full => x.snd.snd) hEqual)
  apply GlobalDiffeomorphismBRSTState.ext hT
  exact GlobalDiffeomorphismNonminimalFields.ext
    (GlobalDiffeomorphismGhostField.ext hC) (GlobalDiffeomorphismAntighostField.ext hA)
    (GlobalDiffeomorphismNakanishiLautrupField.ext hB)

private theorem dense_withLp_pair {X Y P Q : Type*}
    [NormedAddCommGroup P] [NormedSpace Real P] [NormedAddCommGroup Q] [NormedSpace Real Q]
    {firstMap : X → P} {secondMap : Y → Q} (hf : DenseRange firstMap) (hg : DenseRange secondMap) :
    DenseRange (fun pair : X × Y => WithLp.toLp 2 (firstMap pair.1, secondMap pair.2)) :=
  (WithLp.prodContinuousLinearEquiv 2 Real P Q).symm.surjective.denseRange.comp
    (hf.prodMap hg) (WithLp.prodContinuousLinearEquiv 2 Real P Q).symm.continuous

theorem frameFreeDiffeomorphismFullL2Smooth_denseRange :
    DenseRange (frameFreeDiffeomorphismFullL2Smooth period hPeriod metric) := by
  have hDense := dense_withLp_pair
    (dense_withLp_pair (frameTensorL2Smooth_denseRange period hPeriod frame)
      (frameFreeGhostL2Smooth_denseRange period hPeriod metric))
    (dense_withLp_pair (frameFreeGhostL2Smooth_denseRange period hPeriod metric)
      (frameFreeGhostL2Smooth_denseRange period hPeriod metric))
  refine Dense.mono ?_ hDense
  rintro _ ⟨fields, rfl⟩
  exact ⟨⟨fields.1.1, ⟨⟨fields.2.2⟩, ⟨fields.2.1⟩, ⟨fields.1.2⟩⟩⟩, rfl⟩

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeDiffeomorphismFullL2Core4D
