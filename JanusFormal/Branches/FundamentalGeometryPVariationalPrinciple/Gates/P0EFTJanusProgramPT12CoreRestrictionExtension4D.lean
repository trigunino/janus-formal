import Mathlib.Analysis.InnerProductSpace.LinearPMap

namespace JanusFormal.P0EFTJanusProgramPT12CoreRestrictionExtension4D
set_option autoImplicit false
noncomputable section
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H]

theorem restrictionClosure_le (A : H →ₗ.[Real] H) (hA : A.IsClosed) (S : Submodule Real H) :
    (A.domRestrict S).closure ≤ A := by
  apply LinearPMap.le_of_le_graph
  rw [← (hA.isClosable.leIsClosable
    (show A.domRestrict S ≤ A from LinearPMap.domRestrict_le)).graph_closure_eq_closure_graph]
  exact Submodule.topologicalClosure_minimal _
    (LinearPMap.le_graph_of_le LinearPMap.domRestrict_le) hA

variable [CompleteSpace H]

theorem formalAdjoint_of_le_selfAdjoint (A B : H →ₗ.[Real] H) (hAB : A ≤ B)
    (hB : IsSelfAdjoint B) : A.IsFormalAdjoint A := by
  have hFormal := LinearPMap.adjoint_isFormalAdjoint hB.dense_domain
  rw [LinearPMap.isSelfAdjoint_def.mp hB] at hFormal
  intro x y
  let xB : B.domain := ⟨x.val, hAB.1 x.property⟩
  let yB : B.domain := ⟨y.val, hAB.1 y.property⟩
  have hx := hAB.2 (x := x) (y := xB) rfl
  have hy := hAB.2 (x := y) (y := yB) rfl
  exact (congrArg (fun v => inner Real v y.val) hx).trans
    ((hFormal xB yB).trans (congrArg (fun v => inner Real x.val v) hy.symm))

end
end JanusFormal.P0EFTJanusProgramPT12CoreRestrictionExtension4D
