import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDiffeomorphismStrongSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeMetricFlat4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDeDonderCore4D
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

/-! Minimal closed realization of the native diffeomorphism BRST Hessian. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeDiffeomorphismStrongClosed4D
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
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismStrongSmooth4D
open P0EFTJanusProgramPT12ClosedFeatureCore4D
local notation "fullInc" => frameFreeDiffeomorphismFullL2Smooth period hPeriod metric
local notation "fullAction" => frameFreeDiffeomorphismStrongSmooth period hPeriod metric

private theorem graph_single :
    Function.Injective (fun point : linearFeatureGraphClosure fullInc fullAction => point.val.1) :=
  linearFeatureGraphClosure_fst_injective fullInc fullAction fullAction
    (frameFreeDiffeomorphismFullL2Smooth_denseRange period hPeriod metric)
    (frameFreeDiffeomorphismStrongSmooth_symmetric period hPeriod metric)

/-- The minimal closed realization of all native diffeomorphism BRST columns. -/
def frameFreeDiffeomorphismStrongMinimal : Full →ₗ.[Real] Full :=
  closedFeatureOperator fullInc fullAction

theorem frameFreeDiffeomorphismStrongMinimal_graph :
    (frameFreeDiffeomorphismStrongMinimal period hPeriod metric).graph =
      linearFeatureGraphClosure fullInc fullAction :=
  closedFeatureOperator_graph fullInc fullAction (graph_single period hPeriod metric)

theorem frameFreeDiffeomorphismStrongMinimal_isClosed :
    (frameFreeDiffeomorphismStrongMinimal period hPeriod metric).IsClosed :=
  closedFeatureOperator_isClosed fullInc fullAction (graph_single period hPeriod metric)

theorem frameFreeDiffeomorphismStrongMinimal_smooth_mem (potential : State) :
    fullInc potential ∈ (frameFreeDiffeomorphismStrongMinimal period hPeriod metric).domain :=
  closedFeatureOperator_smooth_mem fullInc fullAction potential

theorem frameFreeDiffeomorphismStrongMinimal_smooth_apply (potential : State) :
    frameFreeDiffeomorphismStrongMinimal period hPeriod metric
      ⟨fullInc potential, frameFreeDiffeomorphismStrongMinimal_smooth_mem period hPeriod metric potential⟩ =
      fullAction potential :=
  closedFeatureOperator_smooth_apply fullInc fullAction (graph_single period hPeriod metric) potential

theorem frameFreeDiffeomorphismStrongMinimal_dense_domain :
    Dense ((frameFreeDiffeomorphismStrongMinimal period hPeriod metric).domain : Set Full) :=
  closedFeatureOperator_dense_domain fullInc fullAction (frameFreeDiffeomorphismFullL2Smooth_denseRange period hPeriod metric)

theorem frameFreeDiffeomorphismStrongMinimal_hasCore :
    (frameFreeDiffeomorphismStrongMinimal period hPeriod metric).HasCore (fullInc).range :=
  closedFeatureOperator_hasCore fullInc fullAction (graph_single period hPeriod metric)

theorem frameFreeDiffeomorphismStrongMinimal_le
    (extension : Full →ₗ.[Real] Full) (hClosed : extension.IsClosed)
    (hExtends : ∀ potential : State, (fullInc potential, fullAction potential) ∈ extension.graph) :
    frameFreeDiffeomorphismStrongMinimal period hPeriod metric ≤ extension :=
  closedFeatureOperator_minimal fullInc fullAction (graph_single period hPeriod metric) extension hClosed hExtends

/-- Symmetry persists under closure; this does not claim self-adjointness. -/
theorem frameFreeDiffeomorphismStrongMinimal_symmetric :
    (frameFreeDiffeomorphismStrongMinimal period hPeriod metric).IsFormalAdjoint
      (frameFreeDiffeomorphismStrongMinimal period hPeriod metric) :=
  closedFeature_symmetric fullInc fullAction (graph_single period hPeriod metric)
    (frameFreeDiffeomorphismStrongSmooth_symmetric period hPeriod metric)

/-- The certified smooth core retains the original native BRST Hessian. -/
theorem frameFreeDiffeomorphismStrongMinimal_pairing (first second : State) :
    inner Real (frameFreeDiffeomorphismStrongMinimal period hPeriod metric
      ⟨fullInc first, frameFreeDiffeomorphismStrongMinimal_smooth_mem period hPeriod metric first⟩) (fullInc second) =
    globalDiffeomorphismOffShellHessian period hPeriod metric
      (globalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric first)
      (globalDiffeomorphismOffShellSmoothEmbedding period hPeriod metric second) :=
  (congrArg (fun value : Full => inner Real value (fullInc second))
    (frameFreeDiffeomorphismStrongMinimal_smooth_apply period hPeriod metric first)).trans
      (frameFreeDiffeomorphismStrongSmooth_pairing period hPeriod metric first second)

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeDiffeomorphismStrongClosed4D
