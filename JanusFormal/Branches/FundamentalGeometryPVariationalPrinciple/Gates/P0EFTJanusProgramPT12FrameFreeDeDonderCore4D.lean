import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeDeDonderClosed4D

/-! Native de Donder graph completion equals the physical closed domain. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeDeDonderCore4D
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

open P0EFTJanusProgramPT12FrameFreeDeDonderClosed4D

local notation "native" => GlobalGeneralMetricDeDonderGraphHilbert period hPeriod metric
local notation "raw" => GlobalGeneralMetricTensorFrameL2 period hPeriod
local instance nativeGroup : NormedAddCommGroup native := inferInstance
local instance : SeminormedAddCommGroup native := (nativeGroup period hPeriod metric).toSeminormedAddCommGroup
local instance : NormedSpace Real native := inferInstance
local notation "feature" => globalGeneralMetricDeDonderFeatureProjection period hPeriod metric
local notation "minimal" => frameFreeDeDonderMinimal period hPeriod metric

private def rawReadout : native →L[Real] raw :=
  (WithLp.fstL 2 Real raw CovectorL2).comp (globalGeneralMetricDeDonderGraphSubmodule period hPeriod metric).subtypeL

private theorem rawReadout_mem (point : native) :
    rawReadout period hPeriod metric point ∈ frameTensorL2Space period hPeriod frame := by
  have hClosed : IsClosed {point : native |
      rawReadout period hPeriod metric point ∈ frameTensorL2Space period hPeriod frame} :=
    (frameTensorL2 period hPeriod frame).range.isClosed_topologicalClosure.preimage
      (rawReadout period hPeriod metric).continuous
  apply closure_minimal (s := Set.range (globalGeneralMetricDeDonderSmoothEmbedding period hPeriod metric)) ?_ hClosed
    (by rw [(globalGeneralMetricDeDonderSmoothEmbedding_denseRange period hPeriod metric).closure_range]; trivial)
  rintro _ ⟨tensor, rfl⟩
  exact (frameTensorL2 period hPeriod frame).range.le_topologicalClosure ⟨tensor, rfl⟩

def frameFreeDeDonderTensorReadout : native →L[Real] TensorL2 :=
  (rawReadout period hPeriod metric).codRestrict (frameTensorL2Space period hPeriod frame)
    (rawReadout_mem period hPeriod metric)

theorem frameFreeDeDonderTensorReadout_smooth (tensor : Tensor) :
    frameFreeDeDonderTensorReadout period hPeriod metric
      (globalGeneralMetricDeDonderSmoothEmbedding period hPeriod metric tensor) = inc tensor := rfl

/-- Every vector of the original graph is an actual physical-domain vector. -/
theorem frameFreeDeDonderTensorReadout_graph (point : native) :
    (frameFreeDeDonderTensorReadout period hPeriod metric point, feature point) ∈ (minimal).graph := by
  let pair := (frameFreeDeDonderTensorReadout period hPeriod metric).prod feature
  have hClosed : IsClosed {point : native | pair point ∈ (minimal).graph} :=
    (frameFreeDeDonderMinimal_isClosed period hPeriod metric).preimage pair.continuous
  apply closure_minimal (s := Set.range (globalGeneralMetricDeDonderSmoothEmbedding period hPeriod metric)) ?_ hClosed
    (by rw [(globalGeneralMetricDeDonderSmoothEmbedding_denseRange period hPeriod metric).closure_range]; trivial)
  rintro _ ⟨tensor, rfl⟩
  change (inc tensor, action tensor) ∈ (minimal).graph
  rw [frameFreeDeDonderMinimal_graph]
  exact ((inc).prod action).range.le_topologicalClosure ⟨tensor, rfl⟩

/-- The native de Donder completion has no derivative modes invisible in tensor L². -/
theorem frameFreeDeDonderTensorReadout_injective :
    Function.Injective (frameFreeDeDonderTensorReadout period hPeriod metric) := by
  intro first second hInput
  have hFirst := frameFreeDeDonderTensorReadout_graph period hPeriod metric first
  have hSecond := frameFreeDeDonderTensorReadout_graph period hPeriod metric second
  rw [frameFreeDeDonderMinimal_graph] at hFirst hSecond
  have hPair := frameFreeDeDonderClosedGraph_fst_injective period hPeriod metric
    (a₁ := ⟨_, hFirst⟩) (a₂ := ⟨_, hSecond⟩) hInput
  apply Subtype.ext
  apply WithLp.ofLp_injective 2
  exact Prod.ext (congrArg Subtype.val hInput) (congrArg (fun point => point.val.2) hPair)

private theorem physicalGraph_native_mem (point : frameFreeDeDonderClosedGraph period hPeriod metric) :
    WithLp.toLp 2 (point.val.1.val, point.val.2) ∈ globalGeneralMetricDeDonderGraphSubmodule period hPeriod metric := by
  let toNative : TensorL2 × CovectorL2 → GlobalGeneralMetricDeDonderGraphAmbient period hPeriod :=
    fun pair => WithLp.toLp 2 (pair.1.val, pair.2)
  have hContinuous : Continuous toNative :=
    (WithLp.prodContinuousLinearEquiv 2 Real raw CovectorL2).symm.continuous.comp
      (((frameTensorL2Space period hPeriod frame).subtypeL.continuous.comp continuous_fst).prodMk continuous_snd)
  have hClosed : IsClosed {pair : TensorL2 × CovectorL2 |
      toNative pair ∈ globalGeneralMetricDeDonderGraphSubmodule period hPeriod metric} :=
    (globalGeneralMetricDeDonderGraphAmbientLinearMap period hPeriod metric).range.isClosed_topologicalClosure.preimage
      hContinuous
  exact closure_minimal (by
    rintro _ ⟨tensor, rfl⟩
    exact (globalGeneralMetricDeDonderGraphAmbientLinearMap period hPeriod metric).range.le_topologicalClosure
      ⟨tensor, rfl⟩) hClosed point.property

/-- The physical readout parametrizes precisely the closed operator's domain. -/
theorem frameFreeDeDonderTensorReadout_range :
    (frameFreeDeDonderTensorReadout period hPeriod metric).range = (minimal).domain := by
  apply Submodule.ext
  intro value
  constructor
  · rintro ⟨point, rfl⟩
    exact LinearPMap.mem_domain_iff.mpr ⟨feature point, frameFreeDeDonderTensorReadout_graph period hPeriod metric point⟩
  · intro hValue
    have hGraph := (minimal).mem_graph ⟨value, hValue⟩
    rw [frameFreeDeDonderMinimal_graph] at hGraph
    refine ⟨⟨WithLp.toLp 2 (value.val, minimal ⟨value, hValue⟩),
      physicalGraph_native_mem period hPeriod metric ⟨_, hGraph⟩⟩, ?_⟩
    apply Subtype.ext
    rfl

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

theorem frameFreeDeDonderMinimal_hasCore : (minimal).HasCore (inc).range := by
  refine ⟨?_, ?_⟩
  · rintro _ ⟨tensor, rfl⟩
    exact frameFreeDeDonderMinimal_smooth_mem period hPeriod metric tensor
  · have hRestrict : (minimal).domRestrict (inc).range ≤ minimal := LinearPMap.domRestrict_le
    have hClosable := (frameFreeDeDonderMinimal_isClosed period hPeriod metric).isClosable.leIsClosable hRestrict
    apply LinearPMap.eq_of_eq_graph
    rw [← hClosable.graph_closure_eq_closure_graph,
      smoothRestriction_graph inc action minimal
        (frameFreeDeDonderMinimal_smooth_mem period hPeriod metric)
        (frameFreeDeDonderMinimal_smooth_apply period hPeriod metric), frameFreeDeDonderMinimal_graph]
    rfl

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeDeDonderCore4D
