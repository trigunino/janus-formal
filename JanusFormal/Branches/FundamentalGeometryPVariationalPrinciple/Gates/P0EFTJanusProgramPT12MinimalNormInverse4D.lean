import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedRangeAdjoint4D

/-! The unshifted inverse on the actual range, with output orthogonal to the full kernel. -/
namespace JanusFormal.P0EFTJanusProgramPT12MinimalNormInverse4D
set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace
open P0EFTJanusProgramPT12ClosedRangeAdjoint4D
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H]
variable (A : H →ₗ.[Real] H)

def minimalNormInverseGraph : Submodule Real (H × H) :=
  A.graph.comap (LinearEquiv.prodComm Real H H).toLinearMap ⊓
    (operatorNullSpace A)ᗮ.comap (LinearMap.snd Real H H)

def minimalNormInverse : H →ₗ.[Real] H :=
  (minimalNormInverseGraph A).toLinearPMap

theorem minimalNormInverse_graph : (minimalNormInverse A).graph = minimalNormInverseGraph A := by
  apply Submodule.toLinearPMap_graph_eq
  intro pair hPair hZero
  have hNull : pair.2 ∈ operatorNullSpace A := by
    change (pair.2, 0) ∈ A.graph
    have h : (pair.2, pair.1) ∈ A.graph := hPair.1
    rwa [hZero] at h
  have hOrth : pair.2 ∈ (operatorNullSpace A)ᗮ := hPair.2
  exact inner_self_eq_zero.mp (((operatorNullSpace A).mem_orthogonal pair.2).mp hOrth _ hNull)

theorem minimalNormInverse_mem_graph_iff (y x : H) :
    (y, x) ∈ (minimalNormInverse A).graph ↔
      (x, y) ∈ A.graph ∧ x ∈ (operatorNullSpace A)ᗮ := by
  rw [minimalNormInverse_graph]
  rfl

theorem operatorNullSpace_isClosed (hClosed : A.IsClosed) :
    IsClosed (operatorNullSpace A : Set H) :=
  hClosed.preimage (continuous_id.prodMk continuous_const)

theorem minimalNormInverse_isClosed (hClosed : A.IsClosed) : (minimalNormInverse A).IsClosed := by
  rw [LinearPMap.IsClosed, minimalNormInverse_graph]
  exact (hClosed.preimage continuous_swap).inter
    ((operatorNullSpace A).isClosed_orthogonal.preimage continuous_snd)

theorem minimalNormInverse_solves (y : (minimalNormInverse A).domain) :
    (minimalNormInverse A y, y.val) ∈ A.graph ∧
      minimalNormInverse A y ∈ (operatorNullSpace A)ᗮ :=
  (minimalNormInverse_mem_graph_iff A _ _).mp ((minimalNormInverse A).mem_graph y)

section Closed
variable [CompleteSpace H] (hClosed : A.IsClosed)
include hClosed

theorem minimalNormInverse_projected_graph (u : A.domain) :
    (A u, (operatorNullSpace A)ᗮ.starProjection u.val) ∈ (minimalNormInverse A).graph := by
  letI : CompleteSpace (operatorNullSpace A) :=
    (operatorNullSpace_isClosed A hClosed).completeSpace_coe
  rw [minimalNormInverse_mem_graph_iff, Submodule.starProjection_orthogonal_val]
  refine ⟨?_, (operatorNullSpace A).sub_starProjection_mem_orthogonal u.val⟩
  have hNull : ((operatorNullSpace A).starProjection u.val, 0) ∈ A.graph :=
    ((operatorNullSpace A).orthogonalProjectionOnto u.val).property
  have h := A.graph.sub_mem (A.mem_graph u) hNull
  simpa only [Prod.mk_sub_mk, sub_zero] using h

theorem minimalNormInverse_domain : (minimalNormInverse A).domain = LinearMap.range A.toFun := by
  apply le_antisymm
  · intro y hy
    obtain ⟨u, _, hu⟩ := A.mem_graph_iff.mp (minimalNormInverse_solves A ⟨y, hy⟩).1
    exact ⟨u, hu⟩
  · rintro y ⟨u, rfl⟩
    exact LinearPMap.mem_domain_of_mem_graph (minimalNormInverse_projected_graph A hClosed u)

theorem minimalNormInverse_apply_of_solution
    (y : (minimalNormInverse A).domain) (u : A.domain) (hu : A u = y.val) :
    minimalNormInverse A y = (operatorNullSpace A)ᗮ.starProjection u.val := by
  have h := minimalNormInverse_projected_graph A hClosed u
  rw [hu] at h
  exact (minimalNormInverse A).mem_graph_snd_inj ((minimalNormInverse A).mem_graph y) h rfl

theorem minimalNormInverse_norm_le_solution
    (y : (minimalNormInverse A).domain) (u : A.domain) (hu : A u = y.val) :
    ‖minimalNormInverse A y‖ ≤ ‖u.val‖ := by
  rw [minimalNormInverse_apply_of_solution A hClosed y u hu]
  exact (operatorNullSpace A)ᗮ.norm_starProjection_apply_le u.val

end Closed
end
end JanusFormal.P0EFTJanusProgramPT12MinimalNormInverse4D
