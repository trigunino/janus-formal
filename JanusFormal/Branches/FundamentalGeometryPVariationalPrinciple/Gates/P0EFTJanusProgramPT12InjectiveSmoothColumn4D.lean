import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! A faithful smooth column and its Hilbert adjoint, without assuming closability. -/
namespace JanusFormal.P0EFTJanusProgramPT12InjectiveSmoothColumn4D
set_option autoImplicit false
noncomputable section
open Set
variable {D E F : Type*} [AddCommGroup D] [Module Real D]
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [NormedAddCommGroup F] [InnerProductSpace Real F]
variable (inclusion : D →ₗ[Real] E) (operator : D →ₗ[Real] F)
  (hInjective : Function.Injective inclusion)

def injectiveSmoothColumn : E →ₗ.[Real] F where
  domain := inclusion.range
  toFun := operator.comp (LinearEquiv.ofInjective inclusion hInjective).symm.toLinearMap

theorem injectiveSmoothColumn_domain :
    (injectiveSmoothColumn inclusion operator hInjective).domain = inclusion.range := rfl

theorem injectiveSmoothColumn_smooth (field : D) :
    injectiveSmoothColumn inclusion operator hInjective ⟨inclusion field, ⟨field, rfl⟩⟩ = operator field := by
  change operator ((LinearEquiv.ofInjective inclusion hInjective).symm
    ((LinearEquiv.ofInjective inclusion hInjective) field)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem injectiveSmoothColumn_graph :
    (injectiveSmoothColumn inclusion operator hInjective).graph = (inclusion.prod operator).range := by
  ext pair
  constructor
  · intro h
    obtain ⟨value, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp h
    obtain ⟨field, hField⟩ := value.property
    have hAction : injectiveSmoothColumn inclusion operator hInjective value = operator field := by
      have heq : value = ⟨inclusion field, ⟨field, rfl⟩⟩ := Subtype.ext hField.symm
      rw [heq, injectiveSmoothColumn_smooth]
    exact ⟨field, Prod.ext (hField.trans hInput) (hAction.symm.trans hOutput)⟩
  · rintro ⟨field, rfl⟩
    exact (LinearPMap.mem_graph_iff _).mpr
      ⟨⟨inclusion field, ⟨field, rfl⟩⟩, rfl, injectiveSmoothColumn_smooth inclusion operator hInjective field⟩

theorem injectiveSmoothColumn_denseDomain (hDense : DenseRange inclusion) :
    Dense ((injectiveSmoothColumn inclusion operator hInjective).domain : Set E) := hDense

theorem injectiveSmoothColumn_le (extension : E →ₗ.[Real] F)
    (hExtends : ∀ field, (inclusion field, operator field) ∈ extension.graph) :
    injectiveSmoothColumn inclusion operator hInjective ≤ extension := by
  apply LinearPMap.le_of_le_graph
  rw [injectiveSmoothColumn_graph]
  rintro _ ⟨field, rfl⟩
  exact hExtends field

variable [CompleteSpace E]

theorem injectiveSmoothColumn_adjoint_graph_iff (hDense : DenseRange inclusion) (input : F) (output : E) :
    (input, output) ∈ (injectiveSmoothColumn inclusion operator hInjective).adjoint.graph ↔
      ∀ field, inner Real (operator field) input = inner Real (inclusion field) output := by
  rw [LinearPMap.adjoint_graph_eq_graph_adjoint
    (injectiveSmoothColumn_denseDomain inclusion operator hInjective hDense),
    injectiveSmoothColumn_graph, Submodule.mem_adjoint_iff]
  constructor
  · intro h field
    exact sub_eq_zero.mp (h (inclusion field) (operator field) ⟨field, rfl⟩)
  · intro h first second hPair
    obtain ⟨field, hField⟩ := hPair
    cases hField
    exact sub_eq_zero.mpr (h field)

theorem injectiveSmoothColumn_adjoint_isClosed (hDense : DenseRange inclusion) :
    (injectiveSmoothColumn inclusion operator hInjective).adjoint.IsClosed :=
  LinearPMap.adjoint_isClosed (injectiveSmoothColumn_denseDomain inclusion operator hInjective hDense)

end
end JanusFormal.P0EFTJanusProgramPT12InjectiveSmoothColumn4D
