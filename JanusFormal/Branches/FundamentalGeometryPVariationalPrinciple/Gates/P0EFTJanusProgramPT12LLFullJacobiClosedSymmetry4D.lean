import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LLFullJacobiClosure4D

/-! Symmetry of the closed three-slot LL Jacobi realization. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12LLFullJacobiClosedSymmetry4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal LinearPMap
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
open P0EFTJanusProgramPT12LLFullJacobiClosure4D

private theorem symmetric_closure
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    (T : E →ₗ.[Real] E)
    (hClosable : T.IsClosable) (hSym : T.IsFormalAdjoint T) :
    T.closure.IsFormalAdjoint T.closure := by
  let C := T.closure
  have hGraph : T.graph.topologicalClosure = C.graph :=
    hClosable.graph_closure_eq_closure_graph
  have hFirst (x : C.domain) (y : T.domain) :
      inner Real (C x) (y : E) = inner Real (x : E) (T y) := by
    have hSubset : (T.graph : Set (E × E)) ⊆
        {p | inner Real p.2 (y : E) = inner Real p.1 (T y)} := by
      intro p hp
      obtain ⟨z, hz₁, hz₂⟩ := T.mem_graph_iff.mp hp
      change inner Real p.2 (y : E) = inner Real p.1 (T y)
      rw [← hz₁, ← hz₂]
      exact hSym z y
    have hClosed : IsClosed
        {p : E × E | inner Real p.2 (y : E) = inner Real p.1 (T y)} :=
      isClosed_eq (by fun_prop) (by fun_prop)
    have hx : ((x : E), C x) ∈ closure (T.graph : Set (E × E)) := by
      rw [← Submodule.topologicalClosure_coe, hGraph]
      exact C.mem_graph x
    exact (closure_minimal hSubset hClosed) hx
  intro x y
  have hSubset : (T.graph : Set (E × E)) ⊆
      {p | inner Real (C x) p.1 = inner Real (x : E) p.2} := by
    intro p hp
    obtain ⟨z, hz₁, hz₂⟩ := T.mem_graph_iff.mp hp
    change inner Real (C x) p.1 = inner Real (x : E) p.2
    rw [← hz₁, ← hz₂]
    exact hFirst x z
  have hClosed : IsClosed
      {p : E × E | inner Real (C x) p.1 = inner Real (x : E) p.2} :=
    isClosed_eq (by fun_prop) (by fun_prop)
  have hy : ((y : E), C y) ∈ closure (T.graph : Set (E × E)) := by
    rw [← Submodule.topologicalClosure_coe, hGraph]
    exact C.mem_graph y
  exact (closure_minimal hSubset hClosed) hy

variable (period : Real) (hPeriod : period ≠ 0)

/-- The canonical closed full LL Jacobi realization remains symmetric. -/
theorem fullLLJacobiClosedPMap_symmetric
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    (fullLLJacobiClosedPMap period hPeriod data analysis).IsFormalAdjoint
      (fullLLJacobiClosedPMap period hPeriod data analysis) := by
  exact symmetric_closure
    (fullLLJacobiSmoothPMap period hPeriod data analysis)
    (fullLLJacobiSmoothPMap_isClosable period hPeriod data analysis)
    (fullLLJacobiSmoothPMap_symmetric period hPeriod data analysis)

end
end P0EFTJanusProgramPT12LLFullJacobiClosedSymmetry4D
end JanusFormal
