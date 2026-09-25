import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDiffeomorphismFPAdjoint4D
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

/-! The native physical FP minimal closure, without a regular metric witness. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeDiffeomorphismFPClosed4D
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
def frameFreeDiffeomorphismFPClosedGraph : Submodule Real (Core × Ambient) :=
  ((inc).prod action).range.topologicalClosure

theorem frameFreeDiffeomorphismFPClosedGraph_pairing
    (point : frameFreeDiffeomorphismFPClosedGraph period hPeriod metric) (index : N) (test : Scalar) :
    inner Real (point.val.2 index) (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
      inner Real point.val.1 (frameFreeDiffeomorphismFPAdjointColumn period hPeriod metric index test) := by
  have hClosed : IsClosed {pair : Core × Ambient |
      inner Real (pair.2 index) (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
      inner Real pair.1 (frameFreeDiffeomorphismFPAdjointColumn period hPeriod metric index test)} := by
    apply isClosed_eq <;> fun_prop
  exact closure_minimal (by
    rintro _ ⟨tensor, rfl⟩
    exact frameFreeDiffeomorphismFPAdjointColumn_pairing period hPeriod metric tensor index test) hClosed point.property

/-- Native adjoint tests rule out every vertical output in the physical graph closure. -/
theorem frameFreeDiffeomorphismFPClosedGraph_fst_injective :
    Function.Injective (fun point : frameFreeDiffeomorphismFPClosedGraph period hPeriod metric => point.val.1) := by
  intro first second hInput
  apply Subtype.ext
  refine Prod.ext hInput ?_
  apply PiLp.ext
  intro index
  have hAll : (fun test : H => inner Real (first.val.2 index) test) =
      (fun test : H => inner Real (second.val.2 index) test) := by
    apply (smoothToCanonicalPhysicalBulkL2_denseRange period hPeriod).equalizer
    · fun_prop
    · fun_prop
    · funext test
      exact (frameFreeDiffeomorphismFPClosedGraph_pairing period hPeriod metric first index test).trans
        ((congrArg (fun field : Core => inner Real field
          (frameFreeDiffeomorphismFPAdjointColumn period hPeriod metric index test)) hInput).trans
          (frameFreeDiffeomorphismFPClosedGraph_pairing period hPeriod metric second index test).symm)
  exact ext_inner_right Real (congrFun hAll)

/-- The native minimal FP acts from physical ghost L² to covector L². -/
def frameFreeDiffeomorphismFPMinimal : Core →ₗ.[Real] Ambient :=
  (frameFreeDiffeomorphismFPClosedGraph period hPeriod metric).toLinearPMap

theorem frameFreeDiffeomorphismFPMinimal_graph :
    (frameFreeDiffeomorphismFPMinimal period hPeriod metric).graph = frameFreeDiffeomorphismFPClosedGraph period hPeriod metric := by
  apply Submodule.toLinearPMap_graph_eq
  intro pair hPair hZero
  exact congrArg (fun point => point.val.2)
    (frameFreeDiffeomorphismFPClosedGraph_fst_injective period hPeriod metric (a₁ := ⟨pair, hPair⟩) (a₂ := 0) hZero)

theorem frameFreeDiffeomorphismFPMinimal_isClosed : (frameFreeDiffeomorphismFPMinimal period hPeriod metric).IsClosed := by
  rw [LinearPMap.IsClosed, frameFreeDiffeomorphismFPMinimal_graph]
  exact ((inc).prod action).range.isClosed_topologicalClosure

theorem frameFreeDiffeomorphismFPMinimal_smooth_mem (tensor : Ghost) :
    inc tensor ∈ (frameFreeDiffeomorphismFPMinimal period hPeriod metric).domain :=
  ⟨(inc tensor, action tensor), ((inc).prod action).range.le_topologicalClosure ⟨tensor, rfl⟩, rfl⟩

theorem frameFreeDiffeomorphismFPMinimal_smooth_apply (tensor : Ghost) :
    frameFreeDiffeomorphismFPMinimal period hPeriod metric
      ⟨inc tensor, frameFreeDiffeomorphismFPMinimal_smooth_mem period hPeriod metric tensor⟩ = action tensor := by
  have hGraph := (frameFreeDiffeomorphismFPMinimal period hPeriod metric).mem_graph
    ⟨inc tensor, frameFreeDiffeomorphismFPMinimal_smooth_mem period hPeriod metric tensor⟩
  rw [frameFreeDiffeomorphismFPMinimal_graph] at hGraph
  exact congrArg (fun point => point.val.2)
    (frameFreeDiffeomorphismFPClosedGraph_fst_injective period hPeriod metric (a₁ := ⟨_, hGraph⟩)
      (a₂ := ⟨(inc tensor, action tensor), ((inc).prod action).range.le_topologicalClosure ⟨tensor, rfl⟩⟩) rfl)

theorem frameFreeDiffeomorphismFPMinimal_dense_domain :
    Dense ((frameFreeDiffeomorphismFPMinimal period hPeriod metric).domain : Set Core) :=
  (frameFreeGhostL2Smooth_denseRange period hPeriod metric).mono
    (by rintro _ ⟨tensor, rfl⟩; exact frameFreeDiffeomorphismFPMinimal_smooth_mem period hPeriod metric tensor)

theorem frameFreeDiffeomorphismFPMinimal_le (extension : Core →ₗ.[Real] Ambient)
    (hClosed : extension.IsClosed) (hExtends : ∀ tensor : Ghost, (inc tensor, action tensor) ∈ extension.graph) :
    frameFreeDiffeomorphismFPMinimal period hPeriod metric ≤ extension := by
  apply LinearPMap.le_of_le_graph
  rw [frameFreeDiffeomorphismFPMinimal_graph]
  exact closure_minimal (by rintro _ ⟨tensor, rfl⟩; exact hExtends tensor) hClosed

local notation "minimal" => frameFreeDiffeomorphismFPMinimal period hPeriod metric

private theorem smoothRestriction_graph {D E F : Type*}
    [AddCommGroup D] [Module Real D] [AddCommGroup E] [Module Real E]
    [AddCommGroup F] [Module Real F]
    (inclusion : D →ₗ[Real] E) (operator : D →ₗ[Real] F) (extension : E →ₗ.[Real] F)
    (hMem : ∀ field, inclusion field ∈ extension.domain)
    (hApply : ∀ field, extension ⟨inclusion field, hMem field⟩ = operator field) :
    (extension.domRestrict inclusion.range).graph = (inclusion.prod operator).range := by
  ext pair
  constructor
  · intro hPair
    obtain ⟨vector, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp hPair
    obtain ⟨field, hField⟩ := vector.property.1
    have hRestricted : extension.domRestrict inclusion.range vector = operator field :=
      (LinearPMap.domRestrict_apply (y := ⟨inclusion field, hMem field⟩) hField.symm).trans (hApply field)
    exact ⟨field, Prod.ext (hField.trans hInput) (hRestricted.symm.trans hOutput)⟩
  · rintro ⟨field, rfl⟩
    apply (LinearPMap.mem_graph_iff _).mpr
    refine ⟨⟨inclusion field, ⟨⟨field, rfl⟩, hMem field⟩⟩, rfl, ?_⟩
    exact (LinearPMap.domRestrict_apply (y := ⟨inclusion field, hMem field⟩) rfl).trans (hApply field)

theorem frameFreeDiffeomorphismFPMinimal_hasCore : (minimal).HasCore (inc).range := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨tensor, rfl⟩
    exact frameFreeDiffeomorphismFPMinimal_smooth_mem period hPeriod metric tensor
  · have hRestrict : (minimal).domRestrict (inc).range ≤ minimal := LinearPMap.domRestrict_le
    have hClosable := (frameFreeDiffeomorphismFPMinimal_isClosed period hPeriod metric).isClosable.leIsClosable hRestrict
    apply LinearPMap.eq_of_eq_graph
    rw [← hClosable.graph_closure_eq_closure_graph,
      smoothRestriction_graph inc action minimal
        (frameFreeDiffeomorphismFPMinimal_smooth_mem period hPeriod metric)
        (frameFreeDiffeomorphismFPMinimal_smooth_apply period hPeriod metric), frameFreeDiffeomorphismFPMinimal_graph]
    rfl

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeDiffeomorphismFPClosed4D
