import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDeDonderAdjoint4D
import Mathlib.Analysis.InnerProductSpace.LinearPMap
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D

/-! Closed physical de Donder with its actual smooth core, for any smooth metric. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeDeDonderClosed4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralMetricSmoothTrace4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusProgramPGlobalGeneralMetricDeDonderGraphCore4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusFiniteFrameMetricContraction4D P0EFTJanusFiniteFrameMetricTensorTrace4D
open P0EFTJanusFiniteFrameCovariantTensorDivergence4D P0EFTJanusFiniteFrameKoszulCoefficients4D
open P0EFTJanusProgramPT12CanonicalFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12CanonicalFirstOrderColumn4D
open P0EFTJanusMappingTorusCanonicalTotalR4BallParametrization4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
local notation "frame" => finiteSmoothTangentFrame period hPeriod
private abbrev FrameIndex := Fin (finiteSmoothTangentFrame period hPeriod).count
local notation "N" => FrameIndex period hPeriod
local notation "Tensor" => SmoothSymmetricCovariantTwoTensor period hPeriod
open MeasureTheory
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusProgramPT12FrameFreeFrameDerivativeAdjoint4D
open P0EFTJanusProgramPT12FrameTensorL2Transport4D P0EFTJanusProgramPT12FrameTensorL2Equiv4D
open P0EFTJanusProgramPT12FrameFreeDeDonderScalar4D
local instance : MeasurableSpace (Q period hPeriod) := borel _
local instance : BorelSpace (Q period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
local notation "Scalar" => SmoothQuotientField period hPeriod Real
local notation "H" => CanonicalPhysicalBulkL2 period hPeriod
local notation "TensorL2" => FrameTensorL2Completion period hPeriod frame
local instance tensorGroup : NormedAddCommGroup TensorL2 := inferInstance
local instance : SeminormedAddCommGroup TensorL2 := (tensorGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real TensorL2 := inferInstance
local instance : InnerProductSpace Real TensorL2 := Submodule.innerProductSpace (𝕜 := Real) _
local notation "inc" => frameTensorL2Smooth period hPeriod frame

open P0EFTJanusProgramPT12FrameFreeDeDonderAdjoint4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D
local notation "CovectorL2" => GlobalGeneralMetricDeDonderFrameL2 period hPeriod
local instance covectorGroup : NormedAddCommGroup CovectorL2 := inferInstance
local instance : SeminormedAddCommGroup CovectorL2 := (covectorGroup period hPeriod).toSeminormedAddCommGroup
local instance : NormedSpace Real CovectorL2 := inferInstance
local instance : InnerProductSpace Real CovectorL2 := inferInstance
variable (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "action" => globalGeneralMetricDeDonderFrameL2LinearMap period hPeriod metric

def frameFreeDeDonderClosedGraph : Submodule Real (TensorL2 × CovectorL2) :=
  ((inc).prod action).range.topologicalClosure

theorem frameFreeDeDonderClosedGraph_pairing
    (point : frameFreeDeDonderClosedGraph period hPeriod metric) (index : N) (test : Scalar) :
    inner Real (point.val.2 index) (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
      inner Real point.val.1 (frameFreeDeDonderAdjointColumn period hPeriod metric index test) := by
  have hClosed : IsClosed {pair : TensorL2 × CovectorL2 |
      inner Real (pair.2 index) (smoothToCanonicalPhysicalBulkL2 period hPeriod test) =
      inner Real pair.1 (frameFreeDeDonderAdjointColumn period hPeriod metric index test)} := by
    apply isClosed_eq <;> fun_prop
  exact closure_minimal (by
    rintro _ ⟨tensor, rfl⟩
    exact frameFreeDeDonderAdjointColumn_pairing period hPeriod metric tensor index test) hClosed point.property

/-- Native adjoint tests rule out every vertical output in the physical graph closure. -/
theorem frameFreeDeDonderClosedGraph_fst_injective :
    Function.Injective (fun point : frameFreeDeDonderClosedGraph period hPeriod metric => point.val.1) := by
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
      exact (frameFreeDeDonderClosedGraph_pairing period hPeriod metric first index test).trans
        ((congrArg (fun field : TensorL2 => inner Real field
          (frameFreeDeDonderAdjointColumn period hPeriod metric index test)) hInput).trans
          (frameFreeDeDonderClosedGraph_pairing period hPeriod metric second index test).symm)
  exact ext_inner_right Real (congrFun hAll)

/-- The genuine minimal de Donder acts from physical tensor L² to covector L². -/
def frameFreeDeDonderMinimal : TensorL2 →ₗ.[Real] CovectorL2 :=
  (frameFreeDeDonderClosedGraph period hPeriod metric).toLinearPMap

theorem frameFreeDeDonderMinimal_graph :
    (frameFreeDeDonderMinimal period hPeriod metric).graph = frameFreeDeDonderClosedGraph period hPeriod metric := by
  apply Submodule.toLinearPMap_graph_eq
  intro pair hPair hZero
  exact congrArg (fun point => point.val.2)
    (frameFreeDeDonderClosedGraph_fst_injective period hPeriod metric (a₁ := ⟨pair, hPair⟩) (a₂ := 0) hZero)

theorem frameFreeDeDonderMinimal_isClosed : (frameFreeDeDonderMinimal period hPeriod metric).IsClosed := by
  rw [LinearPMap.IsClosed, frameFreeDeDonderMinimal_graph]
  exact ((inc).prod action).range.isClosed_topologicalClosure

theorem frameFreeDeDonderMinimal_smooth_mem (tensor : Tensor) :
    inc tensor ∈ (frameFreeDeDonderMinimal period hPeriod metric).domain :=
  ⟨(inc tensor, action tensor), ((inc).prod action).range.le_topologicalClosure ⟨tensor, rfl⟩, rfl⟩

theorem frameFreeDeDonderMinimal_smooth_apply (tensor : Tensor) :
    frameFreeDeDonderMinimal period hPeriod metric
      ⟨inc tensor, frameFreeDeDonderMinimal_smooth_mem period hPeriod metric tensor⟩ = action tensor := by
  have hGraph := (frameFreeDeDonderMinimal period hPeriod metric).mem_graph
    ⟨inc tensor, frameFreeDeDonderMinimal_smooth_mem period hPeriod metric tensor⟩
  rw [frameFreeDeDonderMinimal_graph] at hGraph
  exact congrArg (fun point => point.val.2)
    (frameFreeDeDonderClosedGraph_fst_injective period hPeriod metric (a₁ := ⟨_, hGraph⟩)
      (a₂ := ⟨(inc tensor, action tensor), ((inc).prod action).range.le_topologicalClosure ⟨tensor, rfl⟩⟩) rfl)

theorem frameFreeDeDonderMinimal_dense_domain :
    Dense ((frameFreeDeDonderMinimal period hPeriod metric).domain : Set TensorL2) :=
  (frameTensorL2Smooth_denseRange period hPeriod frame).mono
    (by rintro _ ⟨tensor, rfl⟩; exact frameFreeDeDonderMinimal_smooth_mem period hPeriod metric tensor)

theorem frameFreeDeDonderMinimal_le (extension : TensorL2 →ₗ.[Real] CovectorL2)
    (hClosed : extension.IsClosed) (hExtends : ∀ tensor : Tensor, (inc tensor, action tensor) ∈ extension.graph) :
    frameFreeDeDonderMinimal period hPeriod metric ≤ extension := by
  apply LinearPMap.le_of_le_graph
  rw [frameFreeDeDonderMinimal_graph]
  exact closure_minimal (by rintro _ ⟨tensor, rfl⟩; exact hExtends tensor) hClosed

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeDeDonderClosed4D
