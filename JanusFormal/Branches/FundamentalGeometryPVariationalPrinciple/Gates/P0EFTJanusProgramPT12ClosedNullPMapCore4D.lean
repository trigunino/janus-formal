import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedNullPMapQuotient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12OffDiagonalCore4D

/-! Smooth operator cores survive quotienting a closed null subspace. -/
namespace JanusFormal.P0EFTJanusProgramPT12ClosedNullPMapCore4D
set_option autoImplicit false
noncomputable section
open Set
open P0EFTJanusProgramPT12ClosedNullPMapQuotient4D
open P0EFTJanusProgramPT12OffDiagonalCore4D
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

theorem quotientPMap_hasCore (A : E →ₗ.[Real] E) (N : Submodule Real E)
    [IsClosed (N : Set E)] (hClosed : A.IsClosed) (hSym : A.IsFormalAdjoint A)
    (hNull : ∀ x ∈ N, (x, (0 : E)) ∈ A.graph) (S : Submodule Real E) (hS : A.HasCore S) :
    (quotientPMap A N).HasCore (S.map N.mkQ) := by
  let B := quotientPMap A N
  let T := S.map N.mkQ
  have hB : B.IsClosed := quotientPMap_isClosed A N hClosed
  have hR := hB.isClosable.leIsClosable (show B.domRestrict T ≤ B from LinearPMap.domRestrict_le)
  have hAR := hClosed.isClosable.leIsClosable (show A.domRestrict S ≤ A from LinearPMap.domRestrict_le)
  have hGraph : (A.domRestrict S).graph.topologicalClosure = A.graph := by
    rw [hAR.graph_closure_eq_closure_graph, hS.closure_eq]
  refine ⟨?_, LinearPMap.eq_of_eq_graph ?_⟩
  · rw [quotientPMap_domain A N hSym hNull]
    exact Submodule.map_mono hS.le_domain
  · rw [← hR.graph_closure_eq_closure_graph]
    apply le_antisymm
    · exact Submodule.topologicalClosure_minimal _
        (LinearPMap.le_graph_of_le LinearPMap.domRestrict_le) hB
    · let q := N.mkQL.prodMap N.mkQL
      let C := (B.domRestrict T).graph.topologicalClosure
      have hPre : A.graph ≤ C.comap q.toLinearMap := by
        rw [← hGraph]
        apply Submodule.topologicalClosure_minimal
        · intro p hp
          have hr := (restriction_mem_graph_iff A S p.1 p.2).mp hp
          obtain ⟨x, hx, hy⟩ := A.mem_graph_iff.mp hr.2
          have hProjected : (N.mkQ p.1, N.mkQ p.2) ∈ B.graph := by
            rw [← hx, ← hy]
            exact quotientPMap_graph_project A N hSym hNull x
          exact Submodule.le_topologicalClosure _
            ((restriction_mem_graph_iff B T _ _).mpr ⟨⟨p.1, hr.1, rfl⟩, hProjected⟩)
        · exact (B.domRestrict T).graph.isClosed_topologicalClosure.preimage q.continuous
      intro p hp
      have hLift : (quotientLift N p.1, quotientLift N p.2) ∈ A.graph := by
        change p ∈ (quotientPMap A N).graph at hp
        rw [quotientPMap_graph] at hp
        exact hp
      have h := hPre hLift
      change (N.mkQ (quotientLift N p.1), N.mkQ (quotientLift N p.2)) ∈ C at h
      simpa only [mk_quotientLift] using h

omit [CompleteSpace E] in
/-- An extension has the same smooth restriction as an operator with that core. -/
theorem extension_restriction_closure (A B : E →ₗ.[Real] E) (hAB : A ≤ B)
    (S : Submodule Real E) (hS : A.HasCore S) : (B.domRestrict S).closure = A := by
  have hRestrict : B.domRestrict S = A.domRestrict S := by
    apply LinearPMap.eq_of_eq_graph
    ext p
    rw [restriction_mem_graph_iff, restriction_mem_graph_iff]
    constructor
    · rintro ⟨hs, hb⟩
      let x : A.domain := ⟨p.1, hS.le_domain hs⟩
      have ha := A.mem_graph x
      have hValue : A x = p.2 := B.mem_graph_snd_inj (LinearPMap.le_graph_of_le hAB ha) hb rfl
      exact ⟨hs, hValue ▸ ha⟩
    · rintro ⟨hs, ha⟩
      exact ⟨hs, LinearPMap.le_graph_of_le hAB ha⟩
  rw [hRestrict, hS.closure_eq]

end
end JanusFormal.P0EFTJanusProgramPT12ClosedNullPMapCore4D
