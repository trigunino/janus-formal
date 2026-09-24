import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedNullPMapQuotient4D

/-! A closed null quotient preserves the full self-adjoint realization. -/
namespace JanusFormal.P0EFTJanusProgramPT12ClosedNullPMapSelfAdjoint4D
set_option autoImplicit false
noncomputable section
open Set
open P0EFTJanusProgramPT12ClosedNullQuotient4D
open P0EFTJanusProgramPT12ClosedNullPMapQuotient4D
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
variable (nullSpace : Submodule Real E) [IsClosed (nullSpace : Set E)]

theorem inner_mk_quotientLift (vector : E) (test : E ⧸ nullSpace) :
    inner Real (nullSpace.mkQ vector) test = inner Real vector (quotientLift nullSpace test) := by
  have hOrth : quotientLift nullSpace test ∈ nullSpaceᗮ :=
    (nullSpace.quotientEquivOrthogonal test).property
  calc
    _ = inner Real test (nullSpace.mkQ vector) := real_inner_comm _ _
    _ = inner Real (nullSpace.mkQ (quotientLift nullSpace test)) (nullSpace.mkQ vector) := by
      rw [mk_quotientLift]
    _ = inner Real (quotientLift nullSpace test) vector := inner_mk_of_left_orthogonal nullSpace _ _ hOrth
    _ = _ := real_inner_comm _ _

variable (operator : E →ₗ.[Real] E) (hSelf : IsSelfAdjoint operator)
variable (hNull : ∀ vector ∈ nullSpace, (vector, (0 : E)) ∈ operator.graph)
include hSelf hNull

/-- No assumption about finite-dimensional kernel or closed range is needed here. -/
theorem quotientPMap_selfAdjoint : IsSelfAdjoint (quotientPMap operator nullSpace) := by
  have hSym : operator.IsFormalAdjoint operator := by
    have h := LinearPMap.adjoint_isFormalAdjoint hSelf.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hSelf] at h
  have hDense := quotientPMap_denseDomain operator nullSpace hSym hNull hSelf.dense_domain
  have hLe := (quotientPMap_symmetric operator nullSpace hSym).le_adjoint hDense
  rw [LinearPMap.isSelfAdjoint_def]
  apply LinearPMap.eq_of_eq_graph
  apply le_antisymm
  · rintro ⟨input, output⟩ hGraph
    rw [LinearPMap.adjoint_graph_eq_graph_adjoint hDense, Submodule.mem_adjoint_iff] at hGraph
    have hLift : (quotientLift nullSpace input, quotientLift nullSpace output) ∈ operator.adjoint.graph := by
      rw [LinearPMap.adjoint_graph_eq_graph_adjoint hSelf.dense_domain, Submodule.mem_adjoint_iff]
      intro first second hPair
      obtain ⟨state, hInput, hOutput⟩ := operator.mem_graph_iff.mp hPair
      have hProjected := quotientPMap_graph_project operator nullSpace hSym hNull state
      change state.val = first at hInput
      change operator state = second at hOutput
      rw [hInput, hOutput] at hProjected
      have h := hGraph _ _ hProjected
      simpa only [inner_mk_quotientLift] using h
    rw [LinearPMap.isSelfAdjoint_def.mp hSelf] at hLift
    rw [quotientPMap_graph]
    exact hLift
  · exact LinearPMap.le_graph_of_le hLe

end
end JanusFormal.P0EFTJanusProgramPT12ClosedNullPMapSelfAdjoint4D
