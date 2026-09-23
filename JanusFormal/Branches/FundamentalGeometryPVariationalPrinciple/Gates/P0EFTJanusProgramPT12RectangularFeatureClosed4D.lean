import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! The closed L2 operator determined by a single-valued feature graph. -/
namespace JanusFormal.P0EFTJanusProgramPT12RectangularFeatureClosed4D
set_option autoImplicit false
noncomputable section
open Set Topology


variable {D E F : Type*} [AddCommGroup D] [Module Real D]
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [NormedAddCommGroup F] [InnerProductSpace Real F]
variable (inclusion : D →ₗ[Real] E) (operator : D →ₗ[Real] F)

def rectangularFeatureGraphClosure : Submodule Real (E × F) :=
  (inclusion.prod operator).range.topologicalClosure

def rectangularFeatureOperator : E →ₗ.[Real] F :=
  (rectangularFeatureGraphClosure inclusion operator).toLinearPMap

theorem rectangularFeatureOperator_graph
    (hSingle : Function.Injective
      (fun graph : rectangularFeatureGraphClosure inclusion operator => graph.val.1)) :
    (rectangularFeatureOperator inclusion operator).graph =
      rectangularFeatureGraphClosure inclusion operator := by
  apply Submodule.toLinearPMap_graph_eq
  intro pair hPair hZero
  exact congrArg (fun graph => graph.val.2)
    (hSingle (a₁ := ⟨pair, hPair⟩) (a₂ := 0) hZero)

theorem rectangularFeatureOperator_isClosed
    (hSingle : Function.Injective
      (fun graph : rectangularFeatureGraphClosure inclusion operator => graph.val.1)) :
    (rectangularFeatureOperator inclusion operator).IsClosed := by
  rw [LinearPMap.IsClosed, rectangularFeatureOperator_graph inclusion operator hSingle]
  exact (inclusion.prod operator).range.isClosed_topologicalClosure

theorem rectangularFeatureOperator_smooth_mem (field : D) :
    inclusion field ∈ (rectangularFeatureOperator inclusion operator).domain :=
  ⟨(inclusion field, operator field),
    (inclusion.prod operator).range.le_topologicalClosure ⟨field, rfl⟩, rfl⟩

theorem rectangularFeatureOperator_smooth_apply
    (hSingle : Function.Injective
      (fun graph : rectangularFeatureGraphClosure inclusion operator => graph.val.1)) (field : D) :
    rectangularFeatureOperator inclusion operator
      ⟨inclusion field, rectangularFeatureOperator_smooth_mem inclusion operator field⟩ = operator field := by
  have hGraph := (rectangularFeatureOperator inclusion operator).mem_graph
    ⟨inclusion field, rectangularFeatureOperator_smooth_mem inclusion operator field⟩
  rw [rectangularFeatureOperator_graph inclusion operator hSingle] at hGraph
  exact congrArg (fun graph => graph.val.2)
    (hSingle (a₁ := ⟨_, hGraph⟩) (a₂ := ⟨(inclusion field, operator field),
      (inclusion.prod operator).range.le_topologicalClosure ⟨field, rfl⟩⟩) rfl)

theorem rectangularFeatureOperator_dense_domain (hDense : DenseRange inclusion) :
    Dense ((rectangularFeatureOperator inclusion operator).domain : Set E) :=
  hDense.mono (by rintro _ ⟨field, rfl⟩; exact rectangularFeatureOperator_smooth_mem inclusion operator field)

/-- Every closed extension of the smooth action contains this operator. -/
theorem rectangularFeatureOperator_minimal
    (hSingle : Function.Injective
      (fun graph : rectangularFeatureGraphClosure inclusion operator => graph.val.1))
    (extension : E →ₗ.[Real] F) (hClosed : extension.IsClosed)
    (hExtends : ∀ field, (inclusion field, operator field) ∈ extension.graph) :
    rectangularFeatureOperator inclusion operator ≤ extension := by
  apply LinearPMap.le_of_le_graph
  rw [rectangularFeatureOperator_graph inclusion operator hSingle]
  exact closure_minimal (by rintro pair ⟨field, rfl⟩; exact hExtends field) hClosed

theorem rectangularFeatureClosure_injective_of_closed_extension
    (extension : E →ₗ.[Real] F) (hClosed : extension.IsClosed)
    (hExtends : ∀ field, (inclusion field, operator field) ∈ extension.graph) :
    Function.Injective (fun graph : rectangularFeatureGraphClosure inclusion operator => graph.val.1) := by
  have hSubset : rectangularFeatureGraphClosure inclusion operator ≤ extension.graph :=
    closure_minimal (by rintro pair ⟨field, rfl⟩; exact hExtends field) hClosed
  intro first second hInput
  have hDifference := extension.graph.sub_mem (hSubset first.property) (hSubset second.property)
  have hZero := extension.graph_fst_eq_zero_snd hDifference (sub_eq_zero.mpr hInput)
  exact Subtype.ext (Prod.ext hInput (sub_eq_zero.mp hZero))

theorem rectangularSmoothRestriction_graph (extension : E →ₗ.[Real] F)
    (hMem : ∀ field, inclusion field ∈ extension.domain)
    (hApply : ∀ field, extension ⟨inclusion field, hMem field⟩ = operator field) :
    (extension.domRestrict inclusion.range).graph = (inclusion.prod operator).range := by
  ext pair
  constructor
  · intro hPair
    obtain ⟨vector, hInput, hOutput⟩ := (LinearPMap.mem_graph_iff _).mp hPair
    obtain ⟨field, hField⟩ := vector.property.1
    have hRestricted : extension.domRestrict inclusion.range vector = operator field :=
      (LinearPMap.domRestrict_apply (y := ⟨inclusion field, hMem field⟩) hField.symm).trans
        (hApply field)
    exact ⟨field, Prod.ext (hField.trans hInput) (hRestricted.symm.trans hOutput)⟩
  · rintro ⟨field, rfl⟩
    apply (LinearPMap.mem_graph_iff _).mpr
    refine ⟨⟨inclusion field, ⟨⟨field, rfl⟩, hMem field⟩⟩, rfl, ?_⟩
    exact (LinearPMap.domRestrict_apply (y := ⟨inclusion field, hMem field⟩) rfl).trans
      (hApply field)

theorem rectangularSmoothRestriction_closure_eq
    (hSingle : Function.Injective
      (fun graph : rectangularFeatureGraphClosure inclusion operator => graph.val.1))
    (extension : E →ₗ.[Real] F) (hClosed : extension.IsClosed)
    (hMem : ∀ field, inclusion field ∈ extension.domain)
    (hApply : ∀ field, extension ⟨inclusion field, hMem field⟩ = operator field) :
    (extension.domRestrict inclusion.range).closure = rectangularFeatureOperator inclusion operator := by
  have hRestrict : extension.domRestrict inclusion.range ≤ extension := LinearPMap.domRestrict_le
  have hClosable := hClosed.isClosable.leIsClosable hRestrict
  apply LinearPMap.eq_of_eq_graph
  rw [← hClosable.graph_closure_eq_closure_graph,
    rectangularSmoothRestriction_graph inclusion operator extension hMem hApply,
    rectangularFeatureOperator_graph inclusion operator hSingle]
  rfl

theorem rectangularSmoothRange_hasCore_iff
    (hSingle : Function.Injective
      (fun graph : rectangularFeatureGraphClosure inclusion operator => graph.val.1))
    (extension : E →ₗ.[Real] F) (hClosed : extension.IsClosed)
    (hMem : ∀ field, inclusion field ∈ extension.domain)
    (hApply : ∀ field, extension ⟨inclusion field, hMem field⟩ = operator field) :
    extension.HasCore inclusion.range ↔ rectangularFeatureOperator inclusion operator = extension := by
  constructor
  · intro hCore
    exact (rectangularSmoothRestriction_closure_eq inclusion operator hSingle extension hClosed hMem hApply).symm.trans
      hCore.closure_eq
  · intro hEqual
    refine ⟨?_, ?_⟩
    · rintro _ ⟨field, rfl⟩
      exact hMem field
    · exact (rectangularSmoothRestriction_closure_eq inclusion operator hSingle extension hClosed hMem hApply).trans hEqual

theorem rectangularFeatureOperator_hasCore
    (hSingle : Function.Injective
      (fun graph : rectangularFeatureGraphClosure inclusion operator => graph.val.1)) :
    (rectangularFeatureOperator inclusion operator).HasCore inclusion.range :=
  (rectangularSmoothRange_hasCore_iff inclusion operator hSingle _
    (rectangularFeatureOperator_isClosed inclusion operator hSingle)
    (rectangularFeatureOperator_smooth_mem inclusion operator)
    (rectangularFeatureOperator_smooth_apply inclusion operator hSingle)).mpr rfl


end
end JanusFormal.P0EFTJanusProgramPT12RectangularFeatureClosed4D
