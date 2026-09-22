import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureOperator4D

/-! The genuine smooth range is a core of its minimal closed realization. -/
namespace JanusFormal.P0EFTJanusProgramPT12ClosedFeatureCore4D
set_option autoImplicit false
noncomputable section
open Set Topology
open P0EFTJanusProgramPT12DenseAdjointGraphClosable4D
open P0EFTJanusProgramPT12ClosedFeatureOperator4D
variable {D H : Type*} [AddCommGroup D] [Module Real D]
  [NormedAddCommGroup H] [InnerProductSpace Real H]
variable (inclusion operator : D →ₗ[Real] H)

theorem featureClosure_injective_of_closed_extension
    (extension : H →ₗ.[Real] H) (hClosed : extension.IsClosed)
    (hExtends : ∀ field, (inclusion field, operator field) ∈ extension.graph) :
    Function.Injective (fun graph : linearFeatureGraphClosure inclusion operator => graph.val.1) := by
  have hSubset : linearFeatureGraphClosure inclusion operator ≤ extension.graph :=
    closure_minimal (by rintro pair ⟨field, rfl⟩; exact hExtends field) hClosed
  intro first second hInput
  have hDifference := extension.graph.sub_mem (hSubset first.property) (hSubset second.property)
  have hZero := extension.graph_fst_eq_zero_snd hDifference (sub_eq_zero.mpr hInput)
  exact Subtype.ext (Prod.ext hInput (sub_eq_zero.mp hZero))

theorem smoothRestriction_graph (extension : H →ₗ.[Real] H)
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

theorem smoothRestriction_closure_eq
    (hSingle : Function.Injective
      (fun graph : linearFeatureGraphClosure inclusion operator => graph.val.1))
    (extension : H →ₗ.[Real] H) (hClosed : extension.IsClosed)
    (hMem : ∀ field, inclusion field ∈ extension.domain)
    (hApply : ∀ field, extension ⟨inclusion field, hMem field⟩ = operator field) :
    (extension.domRestrict inclusion.range).closure = closedFeatureOperator inclusion operator := by
  have hRestrict : extension.domRestrict inclusion.range ≤ extension := LinearPMap.domRestrict_le
  have hClosable := hClosed.isClosable.leIsClosable hRestrict
  apply LinearPMap.eq_of_eq_graph
  rw [← hClosable.graph_closure_eq_closure_graph,
    smoothRestriction_graph inclusion operator extension hMem hApply,
    closedFeatureOperator_graph inclusion operator hSingle]
  rfl

theorem smoothRange_hasCore_iff
    (hSingle : Function.Injective
      (fun graph : linearFeatureGraphClosure inclusion operator => graph.val.1))
    (extension : H →ₗ.[Real] H) (hClosed : extension.IsClosed)
    (hMem : ∀ field, inclusion field ∈ extension.domain)
    (hApply : ∀ field, extension ⟨inclusion field, hMem field⟩ = operator field) :
    extension.HasCore inclusion.range ↔ closedFeatureOperator inclusion operator = extension := by
  constructor
  · intro hCore
    exact (smoothRestriction_closure_eq inclusion operator hSingle extension hClosed hMem hApply).symm.trans
      hCore.closure_eq
  · intro hEqual
    refine ⟨?_, ?_⟩
    · rintro _ ⟨field, rfl⟩
      exact hMem field
    · exact (smoothRestriction_closure_eq inclusion operator hSingle extension hClosed hMem hApply).trans hEqual

theorem closedFeatureOperator_hasCore
    (hSingle : Function.Injective
      (fun graph : linearFeatureGraphClosure inclusion operator => graph.val.1)) :
    (closedFeatureOperator inclusion operator).HasCore inclusion.range :=
  (smoothRange_hasCore_iff inclusion operator hSingle _
    (closedFeatureOperator_isClosed inclusion operator hSingle)
    (closedFeatureOperator_smooth_mem inclusion operator)
    (closedFeatureOperator_smooth_apply inclusion operator hSingle)).mpr rfl

end
end JanusFormal.P0EFTJanusProgramPT12ClosedFeatureCore4D
