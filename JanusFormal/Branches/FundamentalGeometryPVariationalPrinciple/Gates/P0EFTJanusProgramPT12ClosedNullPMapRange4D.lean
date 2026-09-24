import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedNullPMapSelfAdjoint4D

/-! The null quotient preserves the actual range and its closedness. -/
namespace JanusFormal.P0EFTJanusProgramPT12ClosedNullPMapRange4D
set_option autoImplicit false
noncomputable section
open Set
open P0EFTJanusProgramPT12ClosedNullPMapQuotient4D
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
variable (operator : E →ₗ.[Real] E) (nullSpace : Submodule Real E) [IsClosed (nullSpace : Set E)]
variable (hSym : operator.IsFormalAdjoint operator)
variable (hNull : ∀ vector ∈ nullSpace, (vector, (0 : E)) ∈ operator.graph)
include hSym hNull

theorem quotientPMap_mem_range_iff (output : E ⧸ nullSpace) :
    output ∈ LinearMap.range (quotientPMap operator nullSpace).toFun ↔
      quotientLift nullSpace output ∈ LinearMap.range operator.toFun := by
  change output ∈ Set.range (quotientPMap operator nullSpace) ↔
    quotientLift nullSpace output ∈ Set.range operator
  rw [LinearPMap.mem_range_iff, LinearPMap.mem_range_iff]
  constructor
  · rintro ⟨input, hGraph⟩
    rw [quotientPMap_graph] at hGraph
    exact ⟨quotientLift nullSpace input, hGraph⟩
  · rintro ⟨input, hGraph⟩
    obtain ⟨state, hInput, hOutput⟩ := operator.mem_graph_iff.mp hGraph
    have h := quotientPMap_graph_project operator nullSpace hSym hNull state
    change state.val = input at hInput
    change operator state = quotientLift nullSpace output at hOutput
    rw [hInput, hOutput, mk_quotientLift] at h
    exact ⟨nullSpace.mkQ input, h⟩

theorem mem_range_iff_orthogonal_and_quotient (output : E) :
    output ∈ LinearMap.range operator.toFun ↔
      output ∈ nullSpaceᗮ ∧ nullSpace.mkQ output ∈ LinearMap.range (quotientPMap operator nullSpace).toFun := by
  constructor
  · rintro ⟨state, rfl⟩
    have hOrth := output_mem_orthogonal operator nullSpace hSym hNull state
    refine ⟨hOrth, (quotientPMap_mem_range_iff operator nullSpace hSym hNull _).mpr ?_⟩
    change quotientLift nullSpace (nullSpace.mkQ (operator state)) ∈ LinearMap.range operator.toFun
    rw [quotientLift_mk nullSpace _ hOrth]
    exact ⟨state, rfl⟩
  · rintro ⟨hOrth, hRange⟩
    have h := (quotientPMap_mem_range_iff operator nullSpace hSym hNull _).mp hRange
    rwa [quotientLift_mk nullSpace _ hOrth] at h

/-- Removing true null modes cannot repair a nonclosed range. -/
theorem quotientPMap_range_isClosed_iff :
    IsClosed (LinearMap.range (quotientPMap operator nullSpace).toFun : Set (E ⧸ nullSpace)) ↔
      IsClosed (LinearMap.range operator.toFun : Set E) := by
  constructor
  · intro hClosed
    have hSet : (LinearMap.range operator.toFun : Set E) =
        (nullSpaceᗮ : Set E) ∩ nullSpace.mkQ ⁻¹' (LinearMap.range (quotientPMap operator nullSpace).toFun : Set (E ⧸ nullSpace)) := by
      ext output
      exact mem_range_iff_orthogonal_and_quotient operator nullSpace hSym hNull output
    rw [hSet]
    exact nullSpace.isClosed_orthogonal.inter (hClosed.preimage nullSpace.mkQL.continuous)
  · intro hClosed
    have hSet : (LinearMap.range (quotientPMap operator nullSpace).toFun : Set (E ⧸ nullSpace)) =
        quotientLift nullSpace ⁻¹' (LinearMap.range operator.toFun : Set E) := by
      ext output
      exact quotientPMap_mem_range_iff operator nullSpace hSym hNull output
    rw [hSet]
    exact hClosed.preimage (quotientLift nullSpace).continuous

end
end JanusFormal.P0EFTJanusProgramPT12ClosedNullPMapRange4D
