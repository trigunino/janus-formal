import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedNullPMapKernel4D

/-! Fredholm equivalence for an unbounded self-adjoint operator and its finite null quotient. -/
namespace JanusFormal.P0EFTJanusProgramPT12NullQuotientFredholm4D
set_option autoImplicit false
noncomputable section
open Set
open P0EFTJanusProgramPT12ClosedNullPMapQuotient4D
open P0EFTJanusProgramPT12ClosedNullPMapSelfAdjoint4D
open P0EFTJanusProgramPT12ClosedNullPMapRange4D
open P0EFTJanusProgramPT12ClosedNullPMapKernel4D
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
variable (operator : E →ₗ.[Real] E)

theorem rangeOrthogonal_iff_adjoint_graph (hDense : Dense (operator.domain : Set E)) (vector : E) :
    vector ∈ (LinearMap.range operator.toFun)ᗮ ↔ (vector, 0) ∈ operator.adjoint.graph := by
  rw [Submodule.mem_orthogonal, LinearPMap.adjoint_graph_eq_graph_adjoint hDense, Submodule.mem_adjoint_iff]
  simp only [inner_zero_right, sub_zero]
  constructor
  · intro h input output hGraph
    obtain ⟨state, _, hOutput⟩ := operator.mem_graph_iff.mp hGraph
    exact h output ⟨state, hOutput⟩
  · intro h output hRange
    obtain ⟨state, rfl⟩ := hRange
    exact h state.val (operator state) (operator.mem_graph state)

variable (hSelf : IsSelfAdjoint operator)

def selfAdjointKernelOrthogonalEquiv : LinearMap.ker operator.toFun ≃ₗ[Real] (LinearMap.range operator.toFun)ᗮ where
  toFun vector := ⟨vector.val.val, by
    rw [rangeOrthogonal_iff_adjoint_graph operator hSelf.dense_domain,
      LinearPMap.isSelfAdjoint_def.mp hSelf]
    have h := operator.mem_graph vector.val
    have hZero : operator vector.val = 0 := vector.property
    rwa [hZero] at h⟩
  invFun vector := by
    have h := (rangeOrthogonal_iff_adjoint_graph operator hSelf.dense_domain vector.val).mp vector.property
    rw [LinearPMap.isSelfAdjoint_def.mp hSelf] at h
    exact ⟨⟨vector.val, LinearPMap.mem_domain_of_mem_graph h⟩,
      operator.mem_graph_snd_inj (operator.mem_graph _) h rfl⟩
  left_inv _ := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv _ := by apply Subtype.ext; rfl
  map_add' _ _ := by apply Subtype.ext; rfl
  map_smul' _ _ := by apply Subtype.ext; rfl

def selfAdjointCokernelKernelEquiv (hClosed : IsClosed (LinearMap.range operator.toFun : Set E)) :
    (E ⧸ LinearMap.range operator.toFun) ≃ₗ[Real] LinearMap.ker operator.toFun := by
  letI : CompleteSpace (LinearMap.range operator.toFun) := hClosed.completeSpace_coe
  exact (LinearMap.range operator.toFun).quotientEquivOrthogonal.toLinearEquiv.trans
    (selfAdjointKernelOrthogonalEquiv operator hSelf).symm

include hSelf in
theorem selfAdjoint_fredholm_iff :
    (IsClosed (LinearMap.range operator.toFun : Set E) ∧
      FiniteDimensional Real (LinearMap.ker operator.toFun) ∧
      FiniteDimensional Real (E ⧸ LinearMap.range operator.toFun)) ↔
    IsClosed (LinearMap.range operator.toFun : Set E) ∧ FiniteDimensional Real (LinearMap.ker operator.toFun) := by
  constructor
  · exact fun h => ⟨h.1, h.2.1⟩
  · rintro ⟨hClosed, hKernel⟩
    letI := hKernel
    exact ⟨hClosed, hKernel, (selfAdjointCokernelKernelEquiv operator hSelf hClosed).symm.finiteDimensional⟩

variable (nullSpace : Submodule Real E) [IsClosed (nullSpace : Set E)] [FiniteDimensional Real nullSpace]
variable (hNull : ∀ vector ∈ nullSpace, (vector, (0 : E)) ∈ operator.graph)
include hSelf hNull

/-- All three Fredholm obligations are preserved, not postulated. -/
theorem quotientPMap_fredholm_iff :
    (IsClosed (LinearMap.range (quotientPMap operator nullSpace).toFun : Set (E ⧸ nullSpace)) ∧
      FiniteDimensional Real (LinearMap.ker (quotientPMap operator nullSpace).toFun) ∧
      FiniteDimensional Real ((E ⧸ nullSpace) ⧸ LinearMap.range (quotientPMap operator nullSpace).toFun)) ↔
    (IsClosed (LinearMap.range operator.toFun : Set E) ∧
      FiniteDimensional Real (LinearMap.ker operator.toFun) ∧
      FiniteDimensional Real (E ⧸ LinearMap.range operator.toFun)) := by
  have hSym : operator.IsFormalAdjoint operator := by
    have h := LinearPMap.adjoint_isFormalAdjoint hSelf.dense_domain
    rwa [LinearPMap.isSelfAdjoint_def.mp hSelf] at h
  rw [selfAdjoint_fredholm_iff _ (quotientPMap_selfAdjoint nullSpace operator hSelf hNull),
    selfAdjoint_fredholm_iff operator hSelf,
    quotientPMap_range_isClosed_iff operator nullSpace hSym hNull,
    quotientKernel_finite_iff operator nullSpace hSym hNull]

end
end JanusFormal.P0EFTJanusProgramPT12NullQuotientFredholm4D
