import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Compact.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalH1L2DenseRange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLCanonicalH1L2Injective4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLStrongJacobiClosure4D

/-!
# The closed reduced LL Jacobi graph in the canonical energy space

For the genuine positive LL energy embedding `I : V →L[ℝ] L²`, the smooth
same-action pairing gives `I† C₀ u = u` in the energy completion. Passing this
bounded identity to the actual graph closure gives `I (I† (C x)) = x`.
Consequently every vector in the closed reduced Jacobi domain has a canonical
energy lift, continuous for the graph norm.

This proves the direction `D(C) → H¹`. It does NOT identify `D(C)` with the
weak/Friedrichs domain, does not prove Rellich compactness, and does not assert
surjectivity or self-adjointness of `C`. All objects here concern the reduced
field block, never the full LL operator with its infinite auxiliary kernel.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open scoped Manifold ContDiff ENNReal LinearPMap
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPLL2EllipticNuclearHeatRegulator4D
open P0EFTJanusProgramPT12LLStrongJacobiL2Core4D
open P0EFTJanusProgramPT12LLStrongJacobiClosure4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Bridge4D
open P0EFTJanusProgramPT12LLCanonicalH1L2DenseRange4D
open P0EFTJanusProgramPT12LLCanonicalH1L2Injective4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)

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

abbrev CanonicalLLEnergy
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  LLH1Space period hPeriod (analysis.llH1Data period hPeriod)

abbrev CanonicalLLL2
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  LLFluxL2 period hPeriod (analysis.llH1Data period hPeriod)

/-- An abbreviation for the existing graph closure, not a new realization. -/
abbrev canonicalLLClosedJacobi
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    CanonicalLLL2 period hPeriod analysis →ₗ.[Real]
      CanonicalLLL2 period hPeriod analysis :=
  llJacobiClosedPMap period hPeriod (analysis.llH1Data period hPeriod).fields

/-- The smooth same-action pairing, extended to every completed energy test. -/
theorem canonicalLLH1ToFluxL2_strong_pairing
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (u : LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod))
    (v : CanonicalLLEnergy period hPeriod analysis) :
    inner Real (llH1SmoothEmbedding period hPeriod
        (analysis.llH1Data period hPeriod) u) v =
      inner Real (llStrongJacobiToL2 period hPeriod
        (analysis.llH1Data period hPeriod).fields u.toTest)
        (canonicalLLH1ToFluxL2 period hPeriod analysis v) := by
  let data := analysis.llH1Data period hPeriod
  let I := canonicalLLH1ToFluxL2 period hPeriod analysis
  have hCore (w : LLH1Smooth period hPeriod data) :
      weakLLJacobiH1Extension period hPeriod data u
          (llH1SmoothEmbedding period hPeriod data w) =
        inner Real (llStrongJacobiToL2 period hPeriod data.fields u.toTest)
          (I (llH1SmoothEmbedding period hPeriod data w)) := by
    rw [weakLLJacobiH1Extension_apply_smooth,
      canonicalLLH1ToFluxL2_agrees_on_smooth, L2.inner_def]
    calc
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
          data.frame data.fields u.toTest w.toTest data.mu =
        ∫ point, inner Real
          (llStrongJacobiToL2 period hPeriod data.fields u.toTest point)
          (w.toTest point)
          ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
            simpa only [data, GlobalAnalysisData.llH1Data] using
              (llStrongJacobiToL2_pairing_eq_hessian period hPeriod
                data.fields u.toTest w.toTest).symm
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [llH1SmoothToFluxL2_ae period hPeriod data w]
          with point hPoint
        -- Use congruence rather than rewriting across the two measure aliases.
        exact congrArg (fun value : LLFieldFiber =>
          inner Real (llStrongJacobiToL2 period hPeriod data.fields u.toTest point)
            value) hPoint.symm
  have hEq := (llH1SmoothEmbedding_denseRange period hPeriod data).equalizer
    (weakLLJacobiH1Extension period hPeriod data u).continuous
    (continuous_const.inner I.continuous)
    (by funext w; exact hCore w)
  exact congrFun hEq v

/-- Applying the adjoint embedding to the smooth strong Jacobi recovers its
energy vector. This is an operator identity, not merely a norm bound. -/
theorem canonicalLLH1ToFluxL2_adjoint_strongJacobi
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (u : LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod)) :
    (canonicalLLH1ToFluxL2 period hPeriod analysis).adjoint
        (llStrongJacobiToL2 period hPeriod
          (analysis.llH1Data period hPeriod).fields u.toTest) =
      llH1SmoothEmbedding period hPeriod (analysis.llH1Data period hPeriod) u := by
  apply ext_inner_right Real
  intro v
  rw [ContinuousLinearMap.adjoint_inner_left]
  exact (canonicalLLH1ToFluxL2_strong_pairing period hPeriod analysis u v).symm

/-- The zero-shift weak L² solution operator `I ∘ I†`. -/
def canonicalLLWeakL2Inverse
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    CanonicalLLL2 period hPeriod analysis →L[Real]
      CanonicalLLL2 period hPeriod analysis :=
  (canonicalLLH1ToFluxL2 period hPeriod analysis).comp
    (canonicalLLH1ToFluxL2 period hPeriod analysis).adjoint

/-- The bounded weak solution operator is a left inverse on the EXACT existing
closed Jacobi domain. The proof passes to the topological graph closure. -/
theorem canonicalLLWeakL2Inverse_closed_left_inverse
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (x : (canonicalLLClosedJacobi period hPeriod analysis).domain) :
    canonicalLLWeakL2Inverse period hPeriod analysis
        (canonicalLLClosedJacobi period hPeriod analysis x) =
      (x : CanonicalLLL2 period hPeriod analysis) := by
  let data := analysis.llH1Data period hPeriod
  -- Lp is an AddSubgroup: fix its carrier type and the concrete canonical measure.
  let H : Type := Lp LLFieldFiber (2 : ENNReal)
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)
  let T : H →ₗ.[Real] H := llJacobiSmoothPMap period hPeriod data.fields
  let C : H →ₗ.[Real] H := canonicalLLClosedJacobi period hPeriod analysis
  let R : H →L[Real] H := canonicalLLWeakL2Inverse period hPeriod analysis
  let e : LLWeakTestSpace period hPeriod ≃ₗ[Real] T.domain :=
    LinearEquiv.ofInjective (llSmoothToL2LinearMap period hPeriod)
      (llSmoothToL2LinearMap_injective period hPeriod)
  have hCore (z : T.domain) : R (T z) = (z : H) := by
    let u : LLH1Smooth period hPeriod data := ⟨e.symm z⟩
    calc
      R (T z) = canonicalLLH1ToFluxL2 period hPeriod analysis
          (llH1SmoothEmbedding period hPeriod data u) := by
        exact congrArg (canonicalLLH1ToFluxL2 period hPeriod analysis)
          (canonicalLLH1ToFluxL2_adjoint_strongJacobi period hPeriod analysis u)
      _ = llH1SmoothToFluxL2 period hPeriod data u :=
        canonicalLLH1ToFluxL2_agrees_on_smooth period hPeriod analysis u
      _ = (z : H) := congrArg Subtype.val (e.apply_symm_apply z)
  have hSubset : (T.graph : Set (H × H)) ⊆ {p : H × H | R p.2 = p.1} := by
    intro p hp
    obtain ⟨z, hz₁, hz₂⟩ := T.mem_graph_iff.mp hp
    change R p.2 = p.1
    rw [← hz₁, ← hz₂]
    exact hCore z
  have hClosed : IsClosed {p : H × H | R p.2 = p.1} :=
    isClosed_eq (R.continuous.comp continuous_snd) continuous_fst
  have hGraph : T.graph.topologicalClosure = C.graph :=
    (llJacobiSmoothPMap_isClosable period hPeriod data.fields).graph_closure_eq_closure_graph
  have hx : (x.1, C x) ∈ closure (T.graph : Set (H × H)) := by
    rw [← Submodule.topologicalClosure_coe, hGraph]
    exact C.mem_graph x
  exact (closure_minimal hSubset hClosed) hx

/-- Every closed-domain vector has a canonical completed-energy representative. -/
theorem canonicalLLClosedJacobi_domain_has_energy_lift
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (x : (canonicalLLClosedJacobi period hPeriod analysis).domain) :
    ∃ u : CanonicalLLEnergy period hPeriod analysis,
      canonicalLLH1ToFluxL2 period hPeriod analysis u =
        (x : CanonicalLLL2 period hPeriod analysis) ∧
      ∀ v : CanonicalLLEnergy period hPeriod analysis,
        inner Real u v = inner Real
          (canonicalLLClosedJacobi period hPeriod analysis x)
          (canonicalLLH1ToFluxL2 period hPeriod analysis v) := by
  refine ⟨(canonicalLLH1ToFluxL2 period hPeriod analysis).adjoint
    (canonicalLLClosedJacobi period hPeriod analysis x), ?_, ?_⟩
  · exact canonicalLLWeakL2Inverse_closed_left_inverse period hPeriod analysis x
  · intro v
    exact ContinuousLinearMap.adjoint_inner_left _ v _

/-- The graph-norm-continuous lift uses the output coordinate of the graph;
no continuity for the unbounded operator in the L² subspace norm is asserted. -/
def canonicalLLClosedGraphToH1
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    (canonicalLLClosedJacobi period hPeriod analysis).graph →L[Real]
      CanonicalLLEnergy period hPeriod analysis :=
  (canonicalLLH1ToFluxL2 period hPeriod analysis).adjoint.comp
    ((ContinuousLinearMap.snd Real _ _).comp
      (canonicalLLClosedJacobi period hPeriod analysis).graph.subtypeL)

def canonicalLLClosedGraphValue
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    (canonicalLLClosedJacobi period hPeriod analysis).graph →L[Real]
      CanonicalLLL2 period hPeriod analysis :=
  (ContinuousLinearMap.fst Real _ _).comp
    (canonicalLLClosedJacobi period hPeriod analysis).graph.subtypeL

/-- Exact factorization of the graph-to-L² inclusion through genuine H¹. -/
theorem canonicalLLClosedGraphValue_factorization
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    (canonicalLLH1ToFluxL2 period hPeriod analysis).comp
        (canonicalLLClosedGraphToH1 period hPeriod analysis) =
      canonicalLLClosedGraphValue period hPeriod analysis := by
  -- Stop at equality of L² vectors; recursive ext would enter Lp.ext.
  apply ContinuousLinearMap.ext
  intro p
  let C := canonicalLLClosedJacobi period hPeriod analysis
  obtain ⟨x, hx, hy⟩ := C.mem_graph_iff.mp p.property
  change canonicalLLWeakL2Inverse period hPeriod analysis p.1.2 = p.1.1
  rw [← hx, ← hy]
  exact canonicalLLWeakL2Inverse_closed_left_inverse period hPeriod analysis x

/-- Rellich compactness of the actual energy embedding suffices for compact
embedding of the closed reduced Jacobi graph. The Rellich premise is explicit. -/
theorem canonicalLLClosedGraphValue_compact_of_rellich
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (hRellich : IsCompactOperator (canonicalLLH1ToFluxL2 period hPeriod analysis)) :
    IsCompactOperator (canonicalLLClosedGraphValue period hPeriod analysis) := by
  rw [← canonicalLLClosedGraphValue_factorization]
  exact hRellich.comp_clm (canonicalLLClosedGraphToH1 period hPeriod analysis)

end
end P0EFTJanusProgramPT12LLCanonicalH1ClosedDomain4D
end JanusFormal
