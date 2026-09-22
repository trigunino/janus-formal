import Mathlib.Analysis.InnerProductSpace.LinearPMap
import Mathlib.Tactic

/-! Bounded symmetric perturbations preserve the full self-adjoint domain. -/
namespace JanusFormal.P0EFTJanusProgramPT12BoundedSelfAdjointPerturbation4D
set_option autoImplicit false
noncomputable section
open Set
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H]

def boundedPerturbation (A : H →ₗ.[Real] H) (B : H →L[Real] H) : H →ₗ.[Real] H :=
  B.toLinearMap +ᵥ A

theorem boundedPerturbation_domain (A : H →ₗ.[Real] H) (B : H →L[Real] H) :
    (boundedPerturbation A B).domain = A.domain := rfl

theorem boundedPerturbation_apply (A : H →ₗ.[Real] H) (B : H →L[Real] H)
    (x : (boundedPerturbation A B).domain) : boundedPerturbation A B x = B x.val + A x := rfl

theorem boundedPerturbation_mem_graph_iff (A : H →ₗ.[Real] H) (B : H →L[Real] H) (x y : H) :
    (x, y) ∈ (boundedPerturbation A B).graph ↔ (x, y - B x) ∈ A.graph := by
  rw [LinearPMap.mem_graph_iff, LinearPMap.mem_graph_iff]
  constructor
  · rintro ⟨a, ha, hv⟩
    refine ⟨a, ha, ?_⟩
    change B a.val + A a = y at hv
    change a.val = x at ha
    change A a = y - B x
    rw [← hv, ← ha]
    abel
  · rintro ⟨a, ha, hv⟩
    refine ⟨a, ha, ?_⟩
    change a.val = x at ha
    change A a = y - B x at hv
    change B a.val + A a = y
    rw [hv, ha]
    abel

variable [CompleteSpace H]

theorem boundedPerturbation_adjoint (A : H →ₗ.[Real] H) (B : H →L[Real] H)
    (hA : Dense (A.domain : Set H)) :
    (boundedPerturbation A B).adjoint = boundedPerturbation A.adjoint B.adjoint := by
  apply LinearPMap.eq_of_eq_graph
  ext pair
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint (T := boundedPerturbation A B) hA,
    Submodule.mem_adjoint_iff, boundedPerturbation_mem_graph_iff,
    LinearPMap.adjoint_graph_eq_graph_adjoint hA, Submodule.mem_adjoint_iff]
  constructor
  · intro h a b hab
    have ht := h a (b + B a) ((boundedPerturbation_mem_graph_iff A B a _).mpr (by simpa using hab))
    rw [inner_add_left] at ht
    rw [inner_sub_right, B.adjoint_inner_right]
    linarith
  · intro h a b hab
    have ht := h a (b - B a) ((boundedPerturbation_mem_graph_iff A B a b).mp hab)
    rw [inner_sub_left, inner_sub_right, B.adjoint_inner_right] at ht
    linarith

theorem boundedPerturbation_selfAdjoint (A : H →ₗ.[Real] H) (B : H →L[Real] H)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) : IsSelfAdjoint (boundedPerturbation A B) := by
  rw [LinearPMap.isSelfAdjoint_def, boundedPerturbation_adjoint A B hA.dense_domain,
    LinearPMap.isSelfAdjoint_def.mp hA, ContinuousLinearMap.isSelfAdjoint_iff'.mp hB]

end
end JanusFormal.P0EFTJanusProgramPT12BoundedSelfAdjointPerturbation4D
