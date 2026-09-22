import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12BoundedSelfAdjointPerturbation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12OffDiagonalCore4D

namespace JanusFormal.P0EFTJanusProgramPT12BoundedPerturbationCore4D
set_option autoImplicit false
noncomputable section
open Set Topology
open P0EFTJanusProgramPT12BoundedSelfAdjointPerturbation4D
open P0EFTJanusProgramPT12OffDiagonalCore4D
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H]

def perturbationGraphShear (B : H →L[Real] H) : (H × H) ≃L[Real] (H × H) where
  toFun p := (p.1, p.2 - B p.1)
  invFun p := (p.1, p.2 + B p.1)
  left_inv p := by simp
  right_inv p := by simp
  map_add' p q := by simp; abel
  map_smul' r p := by simp [smul_sub]
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

theorem boundedPerturbation_isClosed (A : H →ₗ.[Real] H) (B : H →L[Real] H) (hA : A.IsClosed) :
    (boundedPerturbation A B).IsClosed := by
  have hg : ((boundedPerturbation A B).graph : Set (H × H)) =
      (perturbationGraphShear B) ⁻¹' (A.graph : Set (H × H)) := by
    ext p
    exact boundedPerturbation_mem_graph_iff A B p.1 p.2
  change IsClosed _
  rw [hg]
  exact hA.preimage (perturbationGraphShear B).continuous

theorem boundedPerturbation_graph_closure (A : H →ₗ.[Real] H) (B : H →L[Real] H) (hA : A.IsClosable) :
    (boundedPerturbation A B).graph.topologicalClosure = (boundedPerturbation A.closure B).graph := by
  apply SetLike.ext'
  have hg (T : H →ₗ.[Real] H) : ((boundedPerturbation T B).graph : Set (H × H)) =
      (perturbationGraphShear B).toHomeomorph ⁻¹' (T.graph : Set (H × H)) := by
    ext p
    exact boundedPerturbation_mem_graph_iff T B p.1 p.2
  rw [Submodule.topologicalClosure_coe, hg,
    ← (perturbationGraphShear B).toHomeomorph.preimage_closure]
  change (perturbationGraphShear B).toHomeomorph ⁻¹' (A.graph.topologicalClosure : Set (H × H)) = _
  rw [hA.graph_closure_eq_closure_graph, hg]

theorem boundedPerturbation_isClosable (A : H →ₗ.[Real] H) (B : H →L[Real] H) (hA : A.IsClosable) :
    (boundedPerturbation A B).IsClosable :=
  ⟨boundedPerturbation A.closure B, boundedPerturbation_graph_closure A B hA⟩

theorem boundedPerturbation_closure (A : H →ₗ.[Real] H) (B : H →L[Real] H) (hA : A.IsClosable) :
    (boundedPerturbation A B).closure = boundedPerturbation A.closure B := by
  apply LinearPMap.eq_of_eq_graph
  rw [← (boundedPerturbation_isClosable A B hA).graph_closure_eq_closure_graph,
    boundedPerturbation_graph_closure A B hA]

theorem boundedPerturbation_restriction (A : H →ₗ.[Real] H) (B : H →L[Real] H) (S : Submodule Real H) :
    (boundedPerturbation A B).domRestrict S = boundedPerturbation (A.domRestrict S) B := by
  apply LinearPMap.eq_of_eq_graph
  ext p
  rw [restriction_mem_graph_iff, boundedPerturbation_mem_graph_iff,
    boundedPerturbation_mem_graph_iff, restriction_mem_graph_iff]

theorem boundedPerturbation_hasCore (A : H →ₗ.[Real] H) (B : H →L[Real] H)
    (hA : A.IsClosable) (S : Submodule Real H) (hS : A.HasCore S) :
    (boundedPerturbation A B).HasCore S := by
  refine ⟨hS.le_domain, ?_⟩
  rw [boundedPerturbation_restriction, boundedPerturbation_closure _ _
    (hA.leIsClosable (show A.domRestrict S ≤ A from LinearPMap.domRestrict_le)), hS.closure_eq]

end
end JanusFormal.P0EFTJanusProgramPT12BoundedPerturbationCore4D
