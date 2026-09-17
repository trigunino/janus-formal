import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFullJacobiZeroFluxBlock4D

/-! The closed three-slot L² Jacobi graph projects into the field-only graph at zero flux. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLFullJacobiZeroFluxClosedBridge4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000
noncomputable section

open scoped Manifold ContDiff ENNReal LinearPMap
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPT12LLStrongJacobiL2Core4D
open P0EFTJanusProgramPT12LLStrongJacobiClosure4D
open P0EFTJanusProgramPT12LLSmoothL2Density4D
open P0EFTJanusProgramPT12LLFullJacobiLinearMap4D
open P0EFTJanusProgramPT12LLFullJacobiClosure4D
open P0EFTJanusProgramPT12LLFullJacobiZeroFluxBlock4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance : BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

local instance :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

private abbrev AuxMeasureL2 :=
  WithLp 2
    (Lp LLMetricFiber (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) ×
     Lp Real (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod))

private abbrev FieldL2 :=
  Lp LLFieldFiber (2 : ENNReal)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

private theorem full_smooth_apply
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    fullLLJacobiSmoothPMap period hPeriod data analysis
        ⟨fullLLSmoothToHilbertLinearMap period hPeriod analysis direction,
          LinearMap.mem_range_self
            (fullLLSmoothToHilbertLinearMap period hPeriod analysis) direction⟩ =
      fullLLL2HilbertEquiv period hPeriod
        (llFullJacobiLinearMap period hPeriod data analysis direction) := by
  let e : GlobalFullLLSmooth period hPeriod analysis ≃ₗ[Real]
      fullLLJacobiSmoothDomain period hPeriod analysis :=
    LinearEquiv.ofInjective
      (fullLLSmoothToHilbertLinearMap period hPeriod analysis)
      ((fullLLL2HilbertEquiv period hPeriod).injective.comp
        (fullLLSmoothToL2LinearMap_injective period hPeriod analysis))
  have hInverse : e.symm
      ⟨fullLLSmoothToHilbertLinearMap period hPeriod analysis direction,
        LinearMap.mem_range_self
          (fullLLSmoothToHilbertLinearMap period hPeriod analysis) direction⟩ =
      direction := by
    change e.symm (e direction) = direction
    exact e.symm_apply_apply direction
  change fullLLL2HilbertEquiv period hPeriod
      (llFullJacobiLinearMap period hPeriod data analysis
        (e.symm
          ⟨fullLLSmoothToHilbertLinearMap period hPeriod analysis direction,
            LinearMap.mem_range_self
              (fullLLSmoothToHilbertLinearMap period hPeriod analysis) direction⟩)) =
    fullLLL2HilbertEquiv period hPeriod
      (llFullJacobiLinearMap period hPeriod data analysis direction)
  rw [hInverse]

private theorem field_smooth_pair_mem_closed_graph
    (fields : IndependentFields period hPeriod)
    (direction : LLWeakTestSpace period hPeriod) :
    (llSmoothToL2 period hPeriod direction,
      llStrongJacobiToL2 period hPeriod fields direction) ∈
      (llJacobiClosedPMap period hPeriod fields).graph := by
  let e : LLWeakTestSpace period hPeriod ≃ₗ[Real]
      llJacobiSmoothDomain period hPeriod :=
    LinearEquiv.ofInjective (llSmoothToL2LinearMap period hPeriod)
      (llSmoothToL2LinearMap_injective period hPeriod)
  have hDomain : llSmoothToL2 period hPeriod direction ∈
      (llJacobiSmoothPMap period hPeriod fields).domain :=
    LinearMap.mem_range_self (llSmoothToL2LinearMap period hPeriod) direction
  have hInverse : e.symm ⟨llSmoothToL2 period hPeriod direction, hDomain⟩ =
      direction := by
    change e.symm (e direction) = direction
    exact e.symm_apply_apply direction
  have hApply : llJacobiSmoothPMap period hPeriod fields
      ⟨llSmoothToL2 period hPeriod direction, hDomain⟩ =
      llStrongJacobiToL2 period hPeriod fields direction := by
    change llStrongJacobiLinearMap period hPeriod fields
        (e.symm ⟨llSmoothToL2 period hPeriod direction, hDomain⟩) = _
    rw [hInverse]
    rfl
  have hSmoothGraph :
      (llSmoothToL2 period hPeriod direction,
        llStrongJacobiToL2 period hPeriod fields direction) ∈
          (llJacobiSmoothPMap period hPeriod fields).graph := by
    rw [(llJacobiSmoothPMap period hPeriod fields).mem_graph_iff]
    exact ⟨⟨llSmoothToL2 period hPeriod direction, hDomain⟩, rfl, hApply⟩
  exact LinearPMap.le_graph_of_le
    (llJacobiSmoothPMap_le_closed period hPeriod fields) hSmoothGraph

private theorem outer_continuous :
    Continuous (fun value : FullLLHilbert period hPeriod => WithLp.ofLp value) :=
  (WithLp.homeomorphProd 2
    (AuxMeasureL2 period hPeriod) (FieldL2 period hPeriod)).continuous

private theorem auxProjection_continuous :
    Continuous (fun value : FullLLHilbert period hPeriod =>
      (WithLp.ofLp value).1) :=
  continuous_fst.comp (outer_continuous period hPeriod)

private theorem fieldProjection_continuous :
    Continuous (fun value : FullLLHilbert period hPeriod =>
      (WithLp.ofLp value).2) :=
  continuous_snd.comp (outer_continuous period hPeriod)

/-- At zero flux, the closed full LL graph has no auxiliary/measure output,
and its field input-output pair belongs to the closed field-only Jacobi graph. -/
theorem fullLLJacobiClosedPMap_zeroFlux_graph_reduction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (pair : FullLLHilbert period hPeriod × FullLLHilbert period hPeriod)
    (hPair : pair ∈ (fullLLJacobiClosedPMap period hPeriod data analysis).graph) :
    (WithLp.ofLp pair.2).1 = 0 ∧
      ((WithLp.ofLp pair.1).2, (WithLp.ofLp pair.2).2) ∈
        (llJacobiClosedPMap period hPeriod
          (data.boundary.llFields period hPeriod)).graph := by
  let T := fullLLJacobiSmoothPMap period hPeriod data analysis
  let C := fullLLJacobiClosedPMap period hPeriod data analysis
  let F := llJacobiClosedPMap period hPeriod
    (data.boundary.llFields period hPeriod)
  let S : Set (FullLLHilbert period hPeriod × FullLLHilbert period hPeriod) :=
    {pair | (WithLp.ofLp pair.2).1 = 0 ∧
      ((WithLp.ofLp pair.1).2, (WithLp.ofLp pair.2).2) ∈ F.graph}
  have hClosedAux : IsClosed
      {pair : FullLLHilbert period hPeriod × FullLLHilbert period hPeriod |
        (WithLp.ofLp pair.2).1 = 0} :=
    isClosed_eq
      ((auxProjection_continuous period hPeriod).comp continuous_snd)
      continuous_const
  have hFieldGraphClosed : IsClosed
      (F.graph : Set (FieldL2 period hPeriod × FieldL2 period hPeriod)) :=
    llJacobiClosedPMap_isClosed period hPeriod
      (data.boundary.llFields period hPeriod)
  have hProjectionContinuous : Continuous
      (fun pair : FullLLHilbert period hPeriod × FullLLHilbert period hPeriod =>
        ((WithLp.ofLp pair.1).2, (WithLp.ofLp pair.2).2)) :=
    ((fieldProjection_continuous period hPeriod).comp continuous_fst).prodMk
      ((fieldProjection_continuous period hPeriod).comp continuous_snd)
  have hClosedS : IsClosed S :=
    hClosedAux.inter (hFieldGraphClosed.preimage hProjectionContinuous)
  have hSubset : (T.graph : Set
      (FullLLHilbert period hPeriod × FullLLHilbert period hPeriod)) ⊆ S := by
    intro graphPair hGraphPair
    obtain ⟨input, hInput, hOutput⟩ := T.mem_graph_iff.mp hGraphPair
    obtain ⟨direction, hDirection⟩ := input.property
    have hInput' : graphPair.1 =
        fullLLSmoothToHilbertLinearMap period hPeriod analysis direction :=
      hInput.symm.trans hDirection.symm
    have hOutput' : graphPair.2 =
        fullLLL2HilbertEquiv period hPeriod
          (llFullJacobiLinearMap period hPeriod data analysis direction) := by
      rw [← hOutput]
      have hInputEq : input =
          ⟨fullLLSmoothToHilbertLinearMap period hPeriod analysis direction,
            LinearMap.mem_range_self
              (fullLLSmoothToHilbertLinearMap period hPeriod analysis) direction⟩ := by
        apply Subtype.ext
        exact hDirection.symm
      rw [hInputEq]
      exact full_smooth_apply period hPeriod data analysis direction
    change (WithLp.ofLp graphPair.2).1 = 0 ∧
      ((WithLp.ofLp graphPair.1).2, (WithLp.ofLp graphPair.2).2) ∈ F.graph
    rw [hInput', hOutput',
      llFullJacobiLinearMap_zeroFlux_block period hPeriod data analysis hZero direction]
    constructor
    · rfl
    · exact field_smooth_pair_mem_closed_graph period hPeriod
        (data.boundary.llFields period hPeriod) direction.2.toTest
  have hGraphClosure : T.graph.topologicalClosure = C.graph :=
    (fullLLJacobiSmoothPMap_isClosable period hPeriod data analysis).graph_closure_eq_closure_graph
  have hPairClosure : pair ∈ closure (T.graph : Set
      (FullLLHilbert period hPeriod × FullLLHilbert period hPeriod)) := by
    rw [← Submodule.topologicalClosure_coe, hGraphClosure]
    exact hPair
  exact (closure_minimal hSubset hClosedS) hPairClosure

end
end P0EFTJanusProgramPT12LLFullJacobiZeroFluxClosedBridge4D
end JanusFormal
