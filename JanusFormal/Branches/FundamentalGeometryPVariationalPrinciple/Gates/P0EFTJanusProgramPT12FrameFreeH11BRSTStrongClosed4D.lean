import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeH11BRSTStrongSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDiffeomorphismStrongSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiffeomorphismL2Readouts4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDeDonderCore4D
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

/-! Closed native diagonal BRST realization on the existing H11 source L². -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeH11BRSTStrongClosed4D
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
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
local notation "State" => GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod
local notation "tensorInc" => frameTensorL2Smooth period hPeriod frame

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPT12DiffeomorphismL2Core4D
open P0EFTJanusProgramPT12DiffeomorphismL2Readouts4D
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismFullL2Core4D
local notation "Source" => DiffeomorphismL2 period hPeriod metric
local notation "Full" => FrameFreeDiffeomorphismFullL2 period hPeriod metric
local instance sourceGroup : NormedAddCommGroup Source := inferInstance
local instance : SeminormedAddCommGroup Source := (sourceGroup period hPeriod metric).toSeminormedAddCommGroup
local instance sourceNormedSpace : NormedSpace Real Source := inferInstance
local instance sourceModule : Module Real Source := (sourceNormedSpace period hPeriod metric).toModule
local instance : SMul Real Source := (sourceModule period hPeriod metric).toSMul
local instance sourceTopology : IsTopologicalAddGroup Source := SeminormedAddCommGroup.toIsTopologicalAddGroup
local instance : ContinuousAdd Source := (sourceTopology period hPeriod metric).toContinuousAdd
local instance : ContinuousConstSMul Real Source where
  continuous_const_smul scalar := (lipschitzWith_smul (β := Source) scalar).continuous
local instance : InnerProductSpace Real Source := Submodule.innerProductSpace (𝕜 := Real) _
local instance fullGroup : NormedAddCommGroup Full := inferInstance
local instance : SeminormedAddCommGroup Full := (fullGroup period hPeriod metric).toSeminormedAddCommGroup
local instance : NormedSpace Real Full := inferInstance
local instance : InnerProductSpace Real Full := inferInstance
local notation "smooth" => diffeomorphismL2Smooth period hPeriod metric

open P0EFTJanusProgramPT12FrameFreeDiffeomorphismH11Readouts4D
open P0EFTJanusProgramPT12FrameFreeDiffeomorphismStrongSmooth4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
local notation "sector" => globalCandidateADiagonalDiffeomorphismSectorStateLinearMap period hPeriod
local notation "readout" => frameFreeH11SectorReadout period hPeriod metric
variable (couplings : GlobalCandidateAActionCouplings)

open P0EFTJanusProgramPT12FrameFreeH11BRSTStrongSmooth4D
open P0EFTJanusProgramPT12ClosedFeatureCore4D
local notation "strong" => frameFreeH11BRSTStrongSmooth period hPeriod metric couplings

private theorem graph_single :
    Function.Injective (fun point : linearFeatureGraphClosure smooth strong => point.val.1) :=
  linearFeatureGraphClosure_fst_injective smooth strong strong
    (diffeomorphismL2Smooth_denseRange period hPeriod metric)
    (frameFreeH11BRSTStrongSmooth_symmetric period hPeriod metric couplings)

/-- The minimal closed realization of all native diffeomorphism BRST columns. -/
def frameFreeH11BRSTStrongMinimal : Source →ₗ.[Real] Source :=
  closedFeatureOperator smooth strong

theorem frameFreeH11BRSTStrongMinimal_graph :
    (frameFreeH11BRSTStrongMinimal period hPeriod metric couplings).graph =
      linearFeatureGraphClosure smooth strong :=
  closedFeatureOperator_graph smooth strong (graph_single period hPeriod metric couplings)

theorem frameFreeH11BRSTStrongMinimal_isClosed :
    (frameFreeH11BRSTStrongMinimal period hPeriod metric couplings).IsClosed :=
  closedFeatureOperator_isClosed smooth strong (graph_single period hPeriod metric couplings)

theorem frameFreeH11BRSTStrongMinimal_smooth_mem (potential : State) :
    smooth potential ∈ (frameFreeH11BRSTStrongMinimal period hPeriod metric couplings).domain :=
  closedFeatureOperator_smooth_mem smooth strong potential

theorem frameFreeH11BRSTStrongMinimal_smooth_apply (potential : State) :
    frameFreeH11BRSTStrongMinimal period hPeriod metric couplings
      ⟨smooth potential, frameFreeH11BRSTStrongMinimal_smooth_mem period hPeriod metric couplings potential⟩ =
      strong potential :=
  closedFeatureOperator_smooth_apply smooth strong (graph_single period hPeriod metric couplings) potential

theorem frameFreeH11BRSTStrongMinimal_dense_domain :
    Dense ((frameFreeH11BRSTStrongMinimal period hPeriod metric couplings).domain : Set Source) :=
  closedFeatureOperator_dense_domain smooth strong (diffeomorphismL2Smooth_denseRange period hPeriod metric)

theorem frameFreeH11BRSTStrongMinimal_hasCore :
    (frameFreeH11BRSTStrongMinimal period hPeriod metric couplings).HasCore (smooth).range :=
  closedFeatureOperator_hasCore smooth strong (graph_single period hPeriod metric couplings)

theorem frameFreeH11BRSTStrongMinimal_le
    (extension : Source →ₗ.[Real] Source) (hClosed : extension.IsClosed)
    (hExtends : ∀ potential : State, (smooth potential, strong potential) ∈ extension.graph) :
    frameFreeH11BRSTStrongMinimal period hPeriod metric couplings ≤ extension :=
  closedFeatureOperator_minimal smooth strong (graph_single period hPeriod metric couplings) extension hClosed hExtends

/-- Symmetry persists under closure; this does not claim self-adjointness. -/
theorem frameFreeH11BRSTStrongMinimal_symmetric :
    (frameFreeH11BRSTStrongMinimal period hPeriod metric couplings).IsFormalAdjoint
      (frameFreeH11BRSTStrongMinimal period hPeriod metric couplings) :=
  closedFeature_symmetric smooth strong (graph_single period hPeriod metric couplings)
    (frameFreeH11BRSTStrongSmooth_symmetric period hPeriod metric couplings)

/-- Pairing on the existing H11 source, with its unchanged normalization. -/
theorem frameFreeH11BRSTStrongMinimal_pairing (first second : State) :
    inner Real (frameFreeH11BRSTStrongMinimal period hPeriod metric couplings
      ⟨smooth first, frameFreeH11BRSTStrongMinimal_smooth_mem period hPeriod metric couplings first⟩) (smooth second) =
    globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod couplings (fun _ => metric)
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod (fun _ => metric) first)
      (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period hPeriod (fun _ => metric) second) :=
  (congrArg (fun value : Source => inner Real value (smooth second))
    (frameFreeH11BRSTStrongMinimal_smooth_apply period hPeriod metric couplings first)).trans
      (frameFreeH11BRSTStrongSmooth_pairing period hPeriod metric couplings first second)

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeH11BRSTStrongClosed4D
