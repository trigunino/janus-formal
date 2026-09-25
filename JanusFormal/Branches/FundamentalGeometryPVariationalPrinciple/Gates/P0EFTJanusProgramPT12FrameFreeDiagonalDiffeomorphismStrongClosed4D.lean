import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDiagonalDiffeomorphismStrongSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDeDonderCore4D
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

/-! Minimal closed native weighted diagonal BRST Hessian with a shared triplet. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeDiagonalDiffeomorphismStrongClosed4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusProgramPT12DenseAdjointGraphClosable4D
open P0EFTJanusProgramPT12ClosedFeatureOperator4D

private theorem closedFeature_symmetric {D H : Type*} [AddCommGroup D] [Module Real D]
    [NormedAddCommGroup H] [InnerProductSpace Real H] (inclusion operator : D →ₗ[Real] H)
    (hSingle : Function.Injective (fun point : linearFeatureGraphClosure inclusion operator => point.val.1))
    (hSym : ∀ first second, inner Real (operator first) (inclusion second) =
      inner Real (inclusion first) (operator second)) :
    (closedFeatureOperator inclusion operator).IsFormalAdjoint (closedFeatureOperator inclusion operator) := by
  let J := closedFeatureOperator inclusion operator
  have hGraph := closedFeatureOperator_graph inclusion operator hSingle
  intro first second
  have hFirst : (first.val, J first) ∈ linearFeatureGraphClosure inclusion operator := by
    rw [← hGraph]
    exact J.mem_graph first
  have hSecond : (second.val, J second) ∈ linearFeatureGraphClosure inclusion operator := by
    rw [← hGraph]
    exact J.mem_graph second
  have hClosed : IsClosed {pair : H × H |
      inner Real (J first) pair.1 = inner Real first.val pair.2} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hSubset : ((inclusion.prod operator).range : Set (H × H)) ⊆
      {pair | inner Real (J first) pair.1 = inner Real first.val pair.2} := by
    rintro _ ⟨field, rfl⟩
    exact linearFeatureGraphClosure_pairing inclusion operator operator hSym ⟨_, hFirst⟩ field
  exact closure_minimal hSubset hClosed hSecond

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
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismFullL2Core4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
variable (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
local notation "State" => GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod
local notation "Plus" => FrameFreeDiffeomorphismFullL2 period hPeriod (metric Sector.plus)
local notation "Minus" => FrameFreeDiffeomorphismFullL2 period hPeriod (metric Sector.minus)
local instance plusGroup : NormedAddCommGroup Plus := inferInstance
local instance : SeminormedAddCommGroup Plus := (plusGroup period hPeriod metric).toSeminormedAddCommGroup
local instance : NormedSpace Real Plus := inferInstance
local instance : InnerProductSpace Real Plus := inferInstance
local instance minusGroup : NormedAddCommGroup Minus := inferInstance
local instance : SeminormedAddCommGroup Minus := (minusGroup period hPeriod metric).toSeminormedAddCommGroup
local instance : NormedSpace Real Minus := inferInstance
local instance : InnerProductSpace Real Minus := inferInstance
local notation "Pair" => WithLp 2 (Plus × Minus)
local instance pairGroup : NormedAddCommGroup Pair := inferInstance
local instance : SeminormedAddCommGroup Pair := (pairGroup period hPeriod metric).toSeminormedAddCommGroup
local instance : NormedSpace Real Pair := inferInstance
local instance : InnerProductSpace Real Pair := inferInstance
local instance : ContinuousConstSMul Real Pair where
  continuous_const_smul scalar := (lipschitzWith_smul (β := Pair) scalar).continuous
local instance : CompleteSpace Pair := inferInstance
local notation "sector" => globalCandidateADiagonalDiffeomorphismSectorStateLinearMap period hPeriod

open P0EFTJanusProgramPT12FrameFreeDiagonalDiffeomorphismL2Core4D
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismStrongSmooth4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
local notation "Core" => FrameFreeDiagonalDiffeomorphismL2 period hPeriod metric
local instance coreGroup : NormedAddCommGroup Core := inferInstance
local instance : SeminormedAddCommGroup Core := (coreGroup period hPeriod metric).toSeminormedAddCommGroup
local instance coreNormedSpace : NormedSpace Real Core := inferInstance
local instance coreModule : Module Real Core := (coreNormedSpace period hPeriod metric).toModule
local instance : SMul Real Core := (coreModule period hPeriod metric).toSMul
local instance : InnerProductSpace Real Core := Submodule.innerProductSpace (𝕜 := Real) _
local instance coreTopology : IsTopologicalAddGroup Core := SeminormedAddCommGroup.toIsTopologicalAddGroup
local instance : ContinuousAdd Core := (coreTopology period hPeriod metric).toContinuousAdd
local instance : ContinuousConstSMul Real Core where
  continuous_const_smul scalar := (lipschitzWith_smul (β := Core) scalar).continuous
local notation "plus" => frameFreeDiagonalDiffeomorphismPlus period hPeriod metric
local notation "minus" => frameFreeDiagonalDiffeomorphismMinus period hPeriod metric
local notation "inc" => frameFreeDiagonalDiffeomorphismL2Smooth period hPeriod metric
variable (couplings : GlobalCandidateAActionCouplings)

open P0EFTJanusProgramPT12FrameFreeDiagonalDiffeomorphismStrongSmooth4D
open P0EFTJanusProgramPT12ClosedFeatureCore4D
local notation "strong" => frameFreeDiagonalDiffeomorphismStrongSmooth period hPeriod metric couplings

private theorem graph_single :
    Function.Injective (fun point : linearFeatureGraphClosure inc strong => point.val.1) :=
  linearFeatureGraphClosure_fst_injective inc strong strong
    (frameFreeDiagonalDiffeomorphismL2Smooth_denseRange period hPeriod metric)
    (frameFreeDiagonalDiffeomorphismStrongSmooth_symmetric period hPeriod metric couplings)

/-- The minimal closed realization of all native diffeomorphism BRST columns. -/
def frameFreeDiagonalDiffeomorphismStrongMinimal : Core →ₗ.[Real] Core :=
  closedFeatureOperator inc strong

theorem frameFreeDiagonalDiffeomorphismStrongMinimal_graph :
    (frameFreeDiagonalDiffeomorphismStrongMinimal period hPeriod metric couplings).graph =
      linearFeatureGraphClosure inc strong :=
  closedFeatureOperator_graph inc strong (graph_single period hPeriod metric couplings)

theorem frameFreeDiagonalDiffeomorphismStrongMinimal_isClosed :
    (frameFreeDiagonalDiffeomorphismStrongMinimal period hPeriod metric couplings).IsClosed :=
  closedFeatureOperator_isClosed inc strong (graph_single period hPeriod metric couplings)

theorem frameFreeDiagonalDiffeomorphismStrongMinimal_smooth_mem (potential : State) :
    inc potential ∈ (frameFreeDiagonalDiffeomorphismStrongMinimal period hPeriod metric couplings).domain :=
  closedFeatureOperator_smooth_mem inc strong potential

theorem frameFreeDiagonalDiffeomorphismStrongMinimal_smooth_apply (potential : State) :
    frameFreeDiagonalDiffeomorphismStrongMinimal period hPeriod metric couplings
      ⟨inc potential, frameFreeDiagonalDiffeomorphismStrongMinimal_smooth_mem period hPeriod metric couplings potential⟩ =
      strong potential :=
  closedFeatureOperator_smooth_apply inc strong (graph_single period hPeriod metric couplings) potential

theorem frameFreeDiagonalDiffeomorphismStrongMinimal_dense_domain :
    Dense ((frameFreeDiagonalDiffeomorphismStrongMinimal period hPeriod metric couplings).domain : Set Core) :=
  closedFeatureOperator_dense_domain inc strong (frameFreeDiagonalDiffeomorphismL2Smooth_denseRange period hPeriod metric)

theorem frameFreeDiagonalDiffeomorphismStrongMinimal_hasCore :
    (frameFreeDiagonalDiffeomorphismStrongMinimal period hPeriod metric couplings).HasCore (inc).range :=
  closedFeatureOperator_hasCore inc strong (graph_single period hPeriod metric couplings)

theorem frameFreeDiagonalDiffeomorphismStrongMinimal_le
    (extension : Core →ₗ.[Real] Core) (hClosed : extension.IsClosed)
    (hExtends : ∀ potential : State, (inc potential, strong potential) ∈ extension.graph) :
    frameFreeDiagonalDiffeomorphismStrongMinimal period hPeriod metric couplings ≤ extension :=
  closedFeatureOperator_minimal inc strong (graph_single period hPeriod metric couplings) extension hClosed hExtends

/-- Symmetry persists under closure; this does not claim self-adjointness. -/
theorem frameFreeDiagonalDiffeomorphismStrongMinimal_symmetric :
    (frameFreeDiagonalDiffeomorphismStrongMinimal period hPeriod metric couplings).IsFormalAdjoint
      (frameFreeDiagonalDiffeomorphismStrongMinimal period hPeriod metric couplings) :=
  closedFeature_symmetric inc strong (graph_single period hPeriod metric couplings)
    (frameFreeDiagonalDiffeomorphismStrongSmooth_symmetric period hPeriod metric couplings)

/-- The native weighted diagonal Hessian is unchanged on the certified smooth core. -/
theorem frameFreeDiagonalDiffeomorphismStrongMinimal_pairing (first second : State) :
    inner Real (frameFreeDiagonalDiffeomorphismStrongMinimal period hPeriod metric couplings
      ⟨inc first, frameFreeDiagonalDiffeomorphismStrongMinimal_smooth_mem period hPeriod metric couplings first⟩) (inc second) =
    globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod couplings metric
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric first)
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric second) :=
  (congrArg (fun value : Core => inner Real value (inc second))
    (frameFreeDiagonalDiffeomorphismStrongMinimal_smooth_apply period hPeriod metric couplings first)).trans
      (frameFreeDiagonalDiffeomorphismStrongSmooth_pairing period hPeriod metric couplings first second)

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeDiagonalDiffeomorphismStrongClosed4D
