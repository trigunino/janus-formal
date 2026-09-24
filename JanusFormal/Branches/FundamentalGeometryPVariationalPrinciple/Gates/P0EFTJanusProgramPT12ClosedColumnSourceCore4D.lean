import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedColumnSourceQuotient4D

/-! Source null reduction preserves the minimal smooth graph and its core. -/
namespace JanusFormal.P0EFTJanusProgramPT12ClosedColumnSourceCore4D
set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace
open P0EFTJanusProgramPT12ClosedNullPMapQuotient4D
open P0EFTJanusProgramPT12ClosedColumnSourceQuotient4D

variable {D E F : Type*} [AddCommGroup D] [Module Real D]
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
  [NormedAddCommGroup F] [NormedSpace Real F]
variable (inclusion : D →ₗ[Real] E) (column : D →ₗ[Real] F) (operator : E →ₗ.[Real] F)

omit [CompleteSpace E] in
theorem hasCore_of_smooth_graph_closure
    (hClosed : operator.IsClosed)
    (hGraph : operator.graph = (inclusion.prod column).range.topologicalClosure) :
    operator.HasCore inclusion.range := by
  have hSmooth : ∀ field, (inclusion field, column field) ∈ operator.graph := by
    intro field
    rw [hGraph]
    exact Submodule.le_topologicalClosure _ ⟨field, rfl⟩
  have hDomain : inclusion.range ≤ operator.domain := by
    rintro _ ⟨field, rfl⟩
    exact LinearPMap.mem_domain_of_mem_graph (hSmooth field)
  have hRestrict : (operator.domRestrict inclusion.range).graph = (inclusion.prod column).range := by
    ext ⟨input, output⟩
    constructor
    · intro hPair
      have hOriginal := LinearPMap.le_graph_of_le LinearPMap.domRestrict_le hPair
      have hInput : input ∈ inclusion.range := (LinearPMap.mem_domain_of_mem_graph hPair).1
      obtain ⟨field, hField⟩ := hInput
      exact ⟨field, Prod.ext hField (operator.mem_graph_snd_inj (hSmooth field) hOriginal hField)⟩
    · rintro ⟨field, hField⟩
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj hField
      have hInput := hDomain (show inclusion field ∈ inclusion.range from ⟨field, rfl⟩)
      have hValue : operator ⟨inclusion field, hInput⟩ = column field :=
        operator.mem_graph_snd_inj (operator.mem_graph ⟨inclusion field, hInput⟩) (hSmooth field) rfl
      exact (LinearPMap.mem_graph_iff _).mpr
        ⟨⟨inclusion field, ⟨⟨field, rfl⟩, hInput⟩⟩, rfl,
          (LinearPMap.domRestrict_apply (f := operator) rfl).trans hValue⟩
  refine ⟨hDomain, LinearPMap.eq_of_eq_graph ?_⟩
  rw [← (hClosed.isClosable.leIsClosable LinearPMap.domRestrict_le).graph_closure_eq_closure_graph,
    hRestrict, hGraph]

variable (nullSpace : Submodule Real E) [IsClosed (nullSpace : Set E)]
  (hNull : ∀ input ∈ nullSpace, (input, (0 : F)) ∈ operator.graph)
  (hClosed : operator.IsClosed)
  (hGraph : operator.graph = (inclusion.prod column).range.topologicalClosure)

include hNull hClosed hGraph in
theorem sourceQuotient_graph_closure :
    (sourceQuotient operator nullSpace).graph =
      ((nullSpace.mkQ.comp inclusion).prod column).range.topologicalClosure := by
  apply le_antisymm
  · rintro ⟨input, output⟩ hPair
    have hOriginal := (sourceQuotient_graph_iff operator nullSpace input output).mp hPair
    rw [hGraph] at hOriginal
    have hClosedPreimage : IsClosed {pair : E × F |
        (nullSpace.mkQ pair.1, pair.2) ∈ ((nullSpace.mkQ.comp inclusion).prod column).range.topologicalClosure} :=
      ((nullSpace.mkQ.comp inclusion).prod column).range.isClosed_topologicalClosure.preimage
        ((nullSpace.mkQL.continuous.comp continuous_fst).prodMk continuous_snd)
    have hProjected := closure_minimal (by
      rintro _ ⟨field, rfl⟩
      exact Submodule.le_topologicalClosure _ ⟨field, rfl⟩) hClosedPreimage hOriginal
    change (nullSpace.mkQ (quotientLift nullSpace input), output) ∈ ((nullSpace.mkQ.comp inclusion).prod column).range.topologicalClosure at hProjected
    simpa only [mk_quotientLift] using hProjected
  · apply Submodule.topologicalClosure_minimal
    · rintro _ ⟨field, rfl⟩
      apply (sourceQuotient_graph_mk_iff operator nullSpace hNull _ _).mpr
      rw [hGraph]
      exact Submodule.le_topologicalClosure _ ⟨field, rfl⟩
    · exact sourceQuotient_isClosed operator nullSpace hClosed

include hNull hClosed hGraph in
theorem sourceQuotient_hasSmoothCore :
    (sourceQuotient operator nullSpace).HasCore (nullSpace.mkQ.comp inclusion).range :=
  hasCore_of_smooth_graph_closure _ _ _ (sourceQuotient_isClosed operator nullSpace hClosed)
    (sourceQuotient_graph_closure inclusion column operator nullSpace hNull hClosed hGraph)

end
end JanusFormal.P0EFTJanusProgramPT12ClosedColumnSourceCore4D
