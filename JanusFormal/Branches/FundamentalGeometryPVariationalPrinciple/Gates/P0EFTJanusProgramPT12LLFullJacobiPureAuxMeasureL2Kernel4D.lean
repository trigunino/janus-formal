import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFullJacobiZeroFluxKernel4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLStrongJacobiClosure4D

/-! At zero LL flux, both inactive L² slots belong to the closed Jacobi kernel. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLFullJacobiPureAuxMeasureL2Kernel4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal LinearPMap
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPT12LLAuxMeasureJacobiL2Core4D
open P0EFTJanusProgramPT12LLStrongJacobiClosure4D
open P0EFTJanusProgramPT12LLFullJacobiClosure4D
open P0EFTJanusProgramPT12LLFullSmoothL2Density4D
open P0EFTJanusProgramPT12LLSmoothL2Density4D
open P0EFTJanusProgramPT12LLFullJacobiZeroFluxKernel4D

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

/-- Insertion of the two inactive L² slots into the full LL Hilbert space. -/
def pureAuxMeasureHilbert
    (aux : Lp LLMetricFiber (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
    (measure : Lp Real (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) :
    FullLLHilbert period hPeriod :=
  fullLLL2HilbertEquiv period hPeriod
    (((aux, measure), 0) : FullLLL2 period hPeriod)

private theorem pureAuxMeasureHilbert_continuous :
    Continuous (fun pair :
      Lp LLMetricFiber (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) ×
        Lp Real (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) =>
      (pureAuxMeasureHilbert period hPeriod pair.1 pair.2,
        (0 : FullLLHilbert period hPeriod))) := by
  change Continuous (fun pair :
      Lp LLMetricFiber (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) ×
        Lp Real (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) =>
      (WithLp.toLp 2
        (WithLp.toLp 2 (pair.1, pair.2),
          (0 : Lp LLFieldFiber (2 : ENNReal)
            (intrinsicCanonicalThroatVolumeMeasure period hPeriod))),
        (0 : FullLLHilbert period hPeriod)))
  fun_prop

private theorem pureAuxMeasureHilbert_smooth
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (measure : SmoothThroatField period hPeriod Real) :
    fullLLSmoothToHilbertLinearMap period hPeriod analysis
        (pureAuxMeasureTest period hPeriod aux measure) =
      pureAuxMeasureHilbert period hPeriod
        (smoothThroatToL2 period hPeriod LLMetricFiber aux)
        (smoothThroatToL2 period hPeriod Real measure) := by
  have hZero : llSmoothToL2 period hPeriod
      (0 : LLWeakTestSpace period hPeriod) = 0 :=
    (llSmoothToL2LinearMap period hPeriod).map_zero
  change fullLLL2HilbertEquiv period hPeriod
      (((smoothThroatToL2 period hPeriod LLMetricFiber aux,
          smoothThroatToL2 period hPeriod Real measure),
        llSmoothToL2 period hPeriod (0 : LLWeakTestSpace period hPeriod)) :
        FullLLL2 period hPeriod) =
    fullLLL2HilbertEquiv period hPeriod
      (((smoothThroatToL2 period hPeriod LLMetricFiber aux,
          smoothThroatToL2 period hPeriod Real measure), 0) :
        FullLLL2 period hPeriod)
  rw [hZero]

/-- The closed full Jacobi operator kills every pure auxiliary-metric and
measure L² vector, including nonsmooth ones, at zero LL flux. -/
theorem fullLLJacobiClosedPMap_pureAuxMeasureL2_zeroFlux
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hZero : (data.boundary.llFields period hPeriod).llField = 0)
    (aux : Lp LLMetricFiber (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod))
    (measure : Lp Real (2 : ENNReal)
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod)) :
    ∃ hDomain : pureAuxMeasureHilbert period hPeriod aux measure ∈
        (fullLLJacobiClosedPMap period hPeriod data analysis).domain,
      fullLLJacobiClosedPMap period hPeriod data analysis
        ⟨pureAuxMeasureHilbert period hPeriod aux measure, hDomain⟩ = 0 := by
  let C := fullLLJacobiClosedPMap period hPeriod data analysis
  let S := {pair :
      Lp LLMetricFiber (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) ×
        Lp Real (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) |
        (pureAuxMeasureHilbert period hPeriod pair.1 pair.2,
          (0 : FullLLHilbert period hPeriod)) ∈ C.graph}
  have hClosed : IsClosed S :=
    (fullLLJacobiClosedPMap_isClosed period hPeriod data analysis).preimage
      (pureAuxMeasureHilbert_continuous period hPeriod)
  have hRange : Set.range (Prod.map
      (smoothThroatToL2 period hPeriod LLMetricFiber)
      (smoothThroatToL2 period hPeriod Real)) ⊆ S := by
    rintro pair ⟨⟨smoothAux, smoothMeasure⟩, rfl⟩
    obtain ⟨hDomain, hImage⟩ :=
      fullLLJacobiClosedPMap_pureAuxMeasure_zeroFlux period hPeriod
        data analysis hZero smoothAux smoothMeasure
    have hValue := pureAuxMeasureHilbert_smooth period hPeriod
      analysis smoothAux smoothMeasure
    have hDomain' : pureAuxMeasureHilbert period hPeriod
        (smoothThroatToL2 period hPeriod LLMetricFiber smoothAux)
        (smoothThroatToL2 period hPeriod Real smoothMeasure) ∈ C.domain := by
      rw [← hValue]
      exact hDomain
    have hSubtype :
        (⟨pureAuxMeasureHilbert period hPeriod
            (smoothThroatToL2 period hPeriod LLMetricFiber smoothAux)
            (smoothThroatToL2 period hPeriod Real smoothMeasure), hDomain'⟩ :
          C.domain) =
        ⟨fullLLSmoothToHilbertLinearMap period hPeriod analysis
          (pureAuxMeasureTest period hPeriod smoothAux smoothMeasure),
          hDomain⟩ := Subtype.ext hValue.symm
    have hImage' : C ⟨pureAuxMeasureHilbert period hPeriod
        (smoothThroatToL2 period hPeriod LLMetricFiber smoothAux)
        (smoothThroatToL2 period hPeriod Real smoothMeasure), hDomain'⟩ = 0 := by
      rw [hSubtype]
      exact hImage
    apply C.mem_graph_iff.mpr
    exact ⟨⟨pureAuxMeasureHilbert period hPeriod
      (smoothThroatToL2 period hPeriod LLMetricFiber smoothAux)
      (smoothThroatToL2 period hPeriod Real smoothMeasure), hDomain'⟩,
      rfl, hImage'⟩
  have hDense :=
    (smoothThroatToL2_denseRange period hPeriod LLMetricFiber).prodMap
      (smoothThroatToL2_denseRange period hPeriod Real)
  have hAll : (Set.univ : Set
      (Lp LLMetricFiber (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod) ×
        Lp Real (2 : ENNReal)
          (intrinsicCanonicalThroatVolumeMeasure period hPeriod))) ⊆ S := by
    calc
      Set.univ = closure (Set.range (Prod.map
          (smoothThroatToL2 period hPeriod LLMetricFiber)
          (smoothThroatToL2 period hPeriod Real))) :=
        hDense.closure_range.symm
      _ ⊆ S := closure_minimal hRange hClosed
  obtain ⟨value, hValue, hImage⟩ := C.mem_graph_iff.mp
    (hAll (Set.mem_univ (aux, measure)))
  have hValue' : (value : FullLLHilbert period hPeriod) =
      pureAuxMeasureHilbert period hPeriod aux measure := by
    simpa only [Prod.fst] using hValue
  have hDomain : pureAuxMeasureHilbert period hPeriod aux measure ∈ C.domain := by
    rw [← hValue']
    exact value.property
  refine ⟨hDomain, ?_⟩
  have hSubtype : value =
      ⟨pureAuxMeasureHilbert period hPeriod aux measure, hDomain⟩ :=
    Subtype.ext hValue'
  rw [← hSubtype]
  exact hImage

end
end P0EFTJanusProgramPT12LLFullJacobiPureAuxMeasureL2Kernel4D
end JanusFormal
