import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ProductClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12OffDiagonalCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureCore4D

namespace JanusFormal.P0EFTJanusProgramPT12ProductCore4D
set_option autoImplicit false
noncomputable section
open Set Topology
open P0EFTJanusProgramPT12ProductClosedOperator4D
open P0EFTJanusProgramPT12ProductClosure4D
open P0EFTJanusProgramPT12OffDiagonalCore4D
open P0EFTJanusProgramPT12ClosedFeatureCore4D
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H]
  [NormedAddCommGroup K] [InnerProductSpace Real K]

def productCore (S : Submodule Real H) (T : Submodule Real K) : Submodule Real (WithLp 2 (H × K)) :=
  (S.prod T).comap (WithLp.linearEquiv 2 Real (H × K)).toLinearMap

theorem productOperator_restriction (A : H →ₗ.[Real] H) (B : K →ₗ.[Real] K)
    (S : Submodule Real H) (T : Submodule Real K) :
    (productOperator A B).domRestrict (productCore S T) =
      productOperator (A.domRestrict S) (B.domRestrict T) := by
  apply LinearPMap.eq_of_eq_graph
  ext pair
  rw [restriction_mem_graph_iff, productOperator_mem_graph_iff,
    productOperator_mem_graph_iff, restriction_mem_graph_iff, restriction_mem_graph_iff]
  change ((pair.1.fst ∈ S ∧ pair.1.snd ∈ T) ∧
    (pair.1.fst, pair.2.fst) ∈ A.graph ∧ (pair.1.snd, pair.2.snd) ∈ B.graph) ↔ _
  tauto

theorem productOperator_hasCore (A : H →ₗ.[Real] H) (B : K →ₗ.[Real] K)
    (hA : A.IsClosed) (hB : B.IsClosed) (S : Submodule Real H) (T : Submodule Real K)
    (hS : A.HasCore S) (hT : B.HasCore T) :
    (productOperator A B).HasCore (productCore S T) := by
  refine ⟨fun x hx => (productOperator_domain_iff A B x).mpr ⟨hS.le_domain hx.1, hT.le_domain hx.2⟩, ?_⟩
  rw [productOperator_restriction, productOperator_closure _ _
    (hA.isClosable.leIsClosable (show A.domRestrict S ≤ A from LinearPMap.domRestrict_le))
    (hB.isClosable.leIsClosable (show B.domRestrict T ≤ B from LinearPMap.domRestrict_le)),
    hS.closure_eq, hT.closure_eq]

theorem bounded_range_hasCore {D : Type*} [AddCommGroup D] [Module Real D]
    (B : H →L[Real] H) (hClosed : (B.toPMap ⊤).IsClosed)
    (i : D →ₗ[Real] H) (hDense : DenseRange i) : (B.toPMap ⊤).HasCore i.range := by
  let A := B.toPMap ⊤
  let o := B.toLinearMap.comp i
  have hMem : ∀ x, i x ∈ A.domain := fun _ => Submodule.mem_top
  have hApply : ∀ x, A ⟨i x, hMem x⟩ = o x := fun _ => rfl
  have hClosable := hClosed.isClosable.leIsClosable (show A.domRestrict i.range ≤ A from LinearPMap.domRestrict_le)
  refine ⟨fun _ _ => Submodule.mem_top, ?_⟩
  apply LinearPMap.eq_of_eq_graph
  rw [← hClosable.graph_closure_eq_closure_graph, smoothRestriction_graph i o A hMem hApply]
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨x, rfl⟩
      exact A.mem_graph ⟨i x, hMem x⟩
    · exact hClosed
  · intro p hp
    obtain ⟨x, hx, hy⟩ := A.mem_graph_iff.mp hp
    have hp' : p = (x.val, B x.val) := Prod.ext hx.symm hy.symm
    rw [hp']
    exact hDense.induction_on x.val
      ((i.prod o).range.isClosed_topologicalClosure.preimage
        (by fun_prop : Continuous (fun x : H => (x, B x))))
      (fun d => Submodule.le_topologicalClosure _ ⟨d, rfl⟩)

theorem productOperator_mono (A A' : H →ₗ.[Real] H) (B B' : K →ₗ.[Real] K)
    (hA : A ≤ A') (hB : B ≤ B') : productOperator A B ≤ productOperator A' B' := by
  apply LinearPMap.le_of_le_graph
  intro p hp
  have h := (productOperator_mem_graph_iff A B p.1 p.2).mp hp
  exact (productOperator_mem_graph_iff A' B' p.1 p.2).mpr
    ⟨LinearPMap.le_graph_of_le hA h.1, LinearPMap.le_graph_of_le hB h.2⟩

end
end JanusFormal.P0EFTJanusProgramPT12ProductCore4D
