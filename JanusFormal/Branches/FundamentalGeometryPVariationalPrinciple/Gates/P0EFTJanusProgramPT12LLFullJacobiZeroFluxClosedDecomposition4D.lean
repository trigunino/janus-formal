import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFullJacobiZeroFluxClosedBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFullJacobiPureAuxMeasureL2Kernel4D

/-! Exact closed-graph decomposition of the LL Jacobi operator at zero flux. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLFullJacobiZeroFluxClosedDecomposition4D

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
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPT12LLStrongJacobiL2Core4D
open P0EFTJanusProgramPT12LLStrongJacobiClosure4D
open P0EFTJanusProgramPT12LLSmoothL2Density4D
open P0EFTJanusProgramPT12LLFullSmoothL2Density4D
open P0EFTJanusProgramPT12LLFullFieldJacobiSameActionPairing4D
open P0EFTJanusProgramPT12LLFullJacobiLinearMap4D
open P0EFTJanusProgramPT12LLFullJacobiClosure4D
open P0EFTJanusProgramPT12LLFullJacobiZeroFluxBlock4D
open P0EFTJanusProgramPT12LLFullJacobiZeroFluxClosedBridge4D
open P0EFTJanusProgramPT12LLFullJacobiPureAuxMeasureL2Kernel4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev FieldL2 :=
  Lp LLFieldFiber (2 : ENNReal)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)

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

/-- Insert the field L² slot into the full three-slot Hilbert space. -/
def pureFieldHilbert (field : FieldL2 period hPeriod) :
    FullLLHilbert period hPeriod :=
  fullLLL2HilbertEquiv period hPeriod
    (((0, 0), field) : FullLLL2 period hPeriod)

private theorem pureFieldHilbert_continuous :
    Continuous (fun pair : FieldL2 period hPeriod × FieldL2 period hPeriod =>
      (pureFieldHilbert period hPeriod pair.1,
        pureFieldHilbert period hPeriod pair.2)) := by
  change Continuous (fun pair : FieldL2 period hPeriod × FieldL2 period hPeriod =>
    (WithLp.toLp 2 (WithLp.toLp 2
      ((0 : Lp LLMetricFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)),
       (0 : Lp Real (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod))), pair.1),
     WithLp.toLp 2 (WithLp.toLp 2
      ((0 : Lp LLMetricFiber (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod)),
       (0 : Lp Real (2 : ENNReal)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod))), pair.2)))
  fun_prop

private theorem pureFieldHilbert_smooth
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (field : LLWeakTestSpace period hPeriod) :
    fullLLSmoothToHilbertLinearMap period hPeriod analysis
        (pureFieldTest period hPeriod
          (LLH1Smooth.ofTest period hPeriod
            (analysis.llH1Data period hPeriod) field)) =
      pureFieldHilbert period hPeriod (llSmoothToL2 period hPeriod field) := by
  have hZeroAux : smoothThroatToL2 period hPeriod LLMetricFiber 0 = 0 := by
    change (smoothThroatField_memLp period hPeriod LLMetricFiber
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      (0 : SmoothThroatField period hPeriod LLMetricFiber)).toLp 0 = 0
    exact MemLp.toLp_zero _
  have hZeroMeasure : smoothThroatToL2 period hPeriod Real 0 = 0 := by
    change (smoothThroatField_memLp period hPeriod Real
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
      (0 : SmoothThroatField period hPeriod Real)).toLp 0 = 0
    exact MemLp.toLp_zero _
  change fullLLL2HilbertEquiv period hPeriod
      (((smoothThroatToL2 period hPeriod LLMetricFiber 0,
          smoothThroatToL2 period hPeriod Real 0),
        llSmoothToL2 period hPeriod field) : FullLLL2 period hPeriod) =
    fullLLL2HilbertEquiv period hPeriod
      (((0, 0), llSmoothToL2 period hPeriod field) : FullLLL2 period hPeriod)
  rw [hZeroAux, hZeroMeasure]

/-- A smooth field graph pair lifts to the full closed graph at zero flux. -/
private theorem pureField_smooth_mem_full_graph
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (field : LLWeakTestSpace period hPeriod) :
    (pureFieldHilbert period hPeriod (llSmoothToL2 period hPeriod field),
      pureFieldHilbert period hPeriod
        (llStrongJacobiToL2 period hPeriod
          (data.boundary.llFields period hPeriod) field)) ∈
      (fullLLJacobiClosedPMap period hPeriod data analysis).graph := by
  let direction := pureFieldTest period hPeriod
    (LLH1Smooth.ofTest period hPeriod (analysis.llH1Data period hPeriod) field)
  have hInput := pureFieldHilbert_smooth period hPeriod analysis field
  have hOutput : llFullJacobiLinearMap period hPeriod data analysis direction =
      ((0, 0), llStrongJacobiToL2 period hPeriod
        (data.boundary.llFields period hPeriod) field) := by
    simpa only [direction, pureFieldTest, LLH1Smooth.ofTest] using
      llFullJacobiLinearMap_zeroFlux_block period hPeriod data analysis hZero
        direction
  have hSmooth :
      (fullLLSmoothToHilbertLinearMap period hPeriod analysis direction,
        fullLLL2HilbertEquiv period hPeriod
          (llFullJacobiLinearMap period hPeriod data analysis direction)) ∈
        (fullLLJacobiSmoothPMap period hPeriod data analysis).graph := by
    apply (fullLLJacobiSmoothPMap period hPeriod data analysis).mem_graph_iff.mpr
    refine ⟨⟨fullLLSmoothToHilbertLinearMap period hPeriod analysis direction,
      LinearMap.mem_range_self
        (fullLLSmoothToHilbertLinearMap period hPeriod analysis) direction⟩,
      rfl, ?_⟩
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
  have hClosed := LinearPMap.le_graph_of_le
    (fullLLJacobiSmoothPMap_le_closed period hPeriod data analysis) hSmooth
  rw [hInput, hOutput] at hClosed
  exact hClosed

/-- Every field-only closed Jacobi graph pair lifts into the full closed graph. -/
theorem fullLLJacobiClosedPMap_zeroFlux_pureField_graph
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (pair : FieldL2 period hPeriod × FieldL2 period hPeriod)
    (hPair : pair ∈ (llJacobiClosedPMap period hPeriod
      (data.boundary.llFields period hPeriod)).graph) :
    (pureFieldHilbert period hPeriod pair.1,
      pureFieldHilbert period hPeriod pair.2) ∈
      (fullLLJacobiClosedPMap period hPeriod data analysis).graph := by
  let F := llJacobiClosedPMap period hPeriod
    (data.boundary.llFields period hPeriod)
  let C := fullLLJacobiClosedPMap period hPeriod data analysis
  let S : Set (FieldL2 period hPeriod × FieldL2 period hPeriod) :=
    {pair | (pureFieldHilbert period hPeriod pair.1,
      pureFieldHilbert period hPeriod pair.2) ∈ C.graph}
  have hClosedS : IsClosed S :=
    (fullLLJacobiClosedPMap_isClosed period hPeriod data analysis).preimage
      (pureFieldHilbert_continuous period hPeriod)
  have hSmoothSubset : ((llJacobiSmoothPMap period hPeriod
      (data.boundary.llFields period hPeriod)).graph :
        Set (FieldL2 period hPeriod × FieldL2 period hPeriod)) ⊆ S := by
    intro smoothPair hSmoothPair
    obtain ⟨input, hInput, hOutput⟩ :=
      (llJacobiSmoothPMap period hPeriod
        (data.boundary.llFields period hPeriod)).mem_graph_iff.mp hSmoothPair
    obtain ⟨field, hField⟩ := input.property
    have hInput' : smoothPair.1 = llSmoothToL2 period hPeriod field :=
      hInput.symm.trans hField.symm
    have hOutput' : smoothPair.2 = llStrongJacobiToL2 period hPeriod
        (data.boundary.llFields period hPeriod) field := by
      rw [← hOutput]
      let e : LLWeakTestSpace period hPeriod ≃ₗ[Real]
          llJacobiSmoothDomain period hPeriod :=
        LinearEquiv.ofInjective (llSmoothToL2LinearMap period hPeriod)
          (llSmoothToL2LinearMap_injective period hPeriod)
      have hEq : input =
          ⟨llSmoothToL2 period hPeriod field,
            LinearMap.mem_range_self (llSmoothToL2LinearMap period hPeriod) field⟩ :=
        Subtype.ext hField.symm
      rw [hEq]
      change llStrongJacobiLinearMap period hPeriod
        (data.boundary.llFields period hPeriod)
        (e.symm (e field)) = _
      rw [e.symm_apply_apply]
      rfl
    change (pureFieldHilbert period hPeriod smoothPair.1,
      pureFieldHilbert period hPeriod smoothPair.2) ∈ C.graph
    rw [hInput', hOutput']
    exact pureField_smooth_mem_full_graph period hPeriod data analysis hZero field
  have hPairClosure : pair ∈ closure
      ((llJacobiSmoothPMap period hPeriod
        (data.boundary.llFields period hPeriod)).graph :
          Set (FieldL2 period hPeriod × FieldL2 period hPeriod)) := by
    rw [← Submodule.topologicalClosure_coe,
      (llJacobiSmoothPMap_isClosable period hPeriod
        (data.boundary.llFields period hPeriod)).graph_closure_eq_closure_graph]
    exact hPair
  exact (closure_minimal hSmoothSubset hClosedS) hPairClosure

/-- At zero flux the full closed LL Jacobi graph is exactly the field graph
with arbitrary auxiliary/measure input and zero auxiliary/measure output. -/
theorem fullLLJacobiClosedPMap_zeroFlux_graph_iff
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (pair : FullLLHilbert period hPeriod × FullLLHilbert period hPeriod) :
    pair ∈ (fullLLJacobiClosedPMap period hPeriod data analysis).graph ↔
      (WithLp.ofLp pair.2).1 = 0 ∧
        ((WithLp.ofLp pair.1).2, (WithLp.ofLp pair.2).2) ∈
          (llJacobiClosedPMap period hPeriod
            (data.boundary.llFields period hPeriod)).graph := by
  constructor
  · exact fullLLJacobiClosedPMap_zeroFlux_graph_reduction period hPeriod
      data analysis hZero pair
  · rintro ⟨hAuxZero, hField⟩
    let E := fullLLL2HilbertEquiv period hPeriod
    let rawInput : FullLLL2 period hPeriod := E.symm pair.1
    let rawOutput : FullLLL2 period hPeriod := E.symm pair.2
    have hField' : (rawInput.2, rawOutput.2) ∈
        (llJacobiClosedPMap period hPeriod
          (data.boundary.llFields period hPeriod)).graph := by
      exact hField
    obtain ⟨hDomain, hImage⟩ :=
      fullLLJacobiClosedPMap_pureAuxMeasureL2_zeroFlux period hPeriod
        data analysis hZero rawInput.1.1 rawInput.1.2
    let C := fullLLJacobiClosedPMap period hPeriod data analysis
    have hAuxGraph :
        (pureAuxMeasureHilbert period hPeriod rawInput.1.1 rawInput.1.2,
          (0 : FullLLHilbert period hPeriod)) ∈ C.graph := by
      exact C.mem_graph_iff.mpr
        ⟨⟨pureAuxMeasureHilbert period hPeriod rawInput.1.1 rawInput.1.2,
          hDomain⟩, rfl, hImage⟩
    have hFieldGraph :
        (pureFieldHilbert period hPeriod rawInput.2,
          pureFieldHilbert period hPeriod rawOutput.2) ∈ C.graph :=
      fullLLJacobiClosedPMap_zeroFlux_pureField_graph period hPeriod
        data analysis hZero (rawInput.2, rawOutput.2) hField'
    have hCombined := C.graph.add_mem hAuxGraph hFieldGraph
    have hInputReconstruction :
        pureAuxMeasureHilbert period hPeriod rawInput.1.1 rawInput.1.2 +
          pureFieldHilbert period hPeriod rawInput.2 = pair.1 := by
      change E ((rawInput.1, 0) : FullLLL2 period hPeriod) +
        E (((0, 0), rawInput.2) : FullLLL2 period hPeriod) = pair.1
      rw [← E.map_add]
      have hSum : ((rawInput.1, 0) : FullLLL2 period hPeriod) +
          (((0, 0), rawInput.2) : FullLLL2 period hPeriod) = rawInput := by
        rcases rawInput with ⟨⟨aux, measure⟩, field⟩
        simp
      rw [hSum]
      exact E.apply_symm_apply pair.1
    have hOutputRawZero : rawOutput.1 = 0 := by
      change WithLp.ofLp (WithLp.ofLp pair.2).1 = 0
      rw [hAuxZero]
      rfl
    have hOutputReconstruction :
        pureFieldHilbert period hPeriod rawOutput.2 = pair.2 := by
      change E (((0, 0), rawOutput.2) : FullLLL2 period hPeriod) = pair.2
      have hEq : (((0, 0), rawOutput.2) : FullLLL2 period hPeriod) =
          rawOutput := by
        calc
          (((0, 0), rawOutput.2) : FullLLL2 period hPeriod) =
              (rawOutput.1, rawOutput.2) := by simp [hOutputRawZero]
          _ = rawOutput := by cases rawOutput; rfl
      rw [hEq]
      exact E.apply_symm_apply pair.2
    change (pureAuxMeasureHilbert period hPeriod rawInput.1.1 rawInput.1.2 +
      pureFieldHilbert period hPeriod rawInput.2,
      (0 : FullLLHilbert period hPeriod) +
        pureFieldHilbert period hPeriod rawOutput.2) ∈ C.graph at hCombined
    rw [hInputReconstruction, zero_add, hOutputReconstruction] at hCombined
    exact hCombined

end
end P0EFTJanusProgramPT12LLFullJacobiZeroFluxClosedDecomposition4D
end JanusFormal
