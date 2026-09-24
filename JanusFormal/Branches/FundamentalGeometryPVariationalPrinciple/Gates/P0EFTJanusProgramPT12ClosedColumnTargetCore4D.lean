import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedColumnTargetQuotient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12InjectiveSmoothColumn4D

/-! Orthogonal target reduction commutes with the minimal smooth graph closure. -/
namespace JanusFormal.P0EFTJanusProgramPT12ClosedColumnTargetCore4D
set_option autoImplicit false
noncomputable section
open Set
open scoped InnerProductSpace
open P0EFTJanusProgramPT12ClosedNullPMapQuotient4D
open P0EFTJanusProgramPT12ClosedColumnTargetQuotient4D
open P0EFTJanusProgramPT12InjectiveSmoothColumn4D

private theorem closure_range_map
    {D E F G : Type*} [AddCommGroup D] [Module Real D]
    [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup F] [NormedSpace Real F]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (inclusion : D →ₗ[Real] E) (source : D →ₗ[Real] F) (target : D →ₗ[Real] G)
    (map : F →L[Real] G) (hMap : ∀ field, map (source field) = target field)
    (pair : E × F) (hPair : pair ∈ (inclusion.prod source).range.topologicalClosure) :
    (pair.1, map pair.2) ∈ (inclusion.prod target).range.topologicalClosure := by
  have hClosed : IsClosed {pair : E × F | (pair.1, map pair.2) ∈ (inclusion.prod target).range.topologicalClosure} :=
    (inclusion.prod target).range.isClosed_topologicalClosure.preimage
      (continuous_fst.prodMk (map.continuous.comp continuous_snd))
  apply closure_minimal _ hClosed hPair
  rintro _ ⟨field, rfl⟩
  apply (inclusion.prod target).range.le_topologicalClosure
  exact ⟨field, Prod.ext rfl (hMap field).symm⟩

variable {D E F : Type*} [AddCommGroup D] [Module Real D]
  [NormedAddCommGroup E] [InnerProductSpace Real E]
  [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]
variable (inclusion : D →ₗ[Real] E) (column : D →ₗ[Real] F)
  (operator : E →ₗ.[Real] F) (nullSpace : Submodule Real F) [IsClosed (nullSpace : Set F)]
  (hGraph : operator.graph = (inclusion.prod column).range.topologicalClosure)
  (hOrth : ∀ field, column field ∈ nullSpaceᗮ)

include hGraph hOrth in
theorem targetQuotient_graph_closure :
    (targetQuotient operator nullSpace).graph =
      (inclusion.prod (nullSpace.mkQ.comp column)).range.topologicalClosure := by
  ext ⟨input, output⟩
  rw [targetQuotient_graph_iff, hGraph]
  constructor
  · intro hPair
    have h := closure_range_map inclusion column (nullSpace.mkQ.comp column) nullSpace.mkQL
      (fun _ => rfl) (input, quotientLift nullSpace output) hPair
    change (input, nullSpace.mkQ (quotientLift nullSpace output)) ∈ _ at h
    simpa only [mk_quotientLift] using h
  · intro hPair
    exact closure_range_map inclusion (nullSpace.mkQ.comp column) column (quotientLift nullSpace)
      (fun field => quotientLift_mk nullSpace (column field) (hOrth field)) (input, output) hPair

variable (hInjective : Function.Injective inclusion)

include hGraph hOrth in
theorem quotientSmoothColumn_le :
    injectiveSmoothColumn inclusion (nullSpace.mkQ.comp column) hInjective ≤
      targetQuotient operator nullSpace := by
  apply LinearPMap.le_of_le_graph
  rw [injectiveSmoothColumn_graph, targetQuotient_graph_closure inclusion column operator nullSpace hGraph hOrth]
  exact Submodule.le_topologicalClosure _

include hGraph hOrth in
theorem quotientSmoothColumn_isClosable (hClosed : operator.IsClosed) :
    (injectiveSmoothColumn inclusion (nullSpace.mkQ.comp column) hInjective).IsClosable :=
  (targetQuotient_isClosed operator nullSpace hClosed).isClosable.leIsClosable
    (quotientSmoothColumn_le inclusion column operator nullSpace hGraph hOrth hInjective)

include hGraph hOrth in
theorem targetQuotient_eq_smoothClosure (hClosed : operator.IsClosed) :
    targetQuotient operator nullSpace =
      (injectiveSmoothColumn inclusion (nullSpace.mkQ.comp column) hInjective).closure := by
  apply LinearPMap.eq_of_eq_graph
  rw [targetQuotient_graph_closure inclusion column operator nullSpace hGraph hOrth,
    ← (quotientSmoothColumn_isClosable inclusion column operator nullSpace hGraph hOrth hInjective hClosed).graph_closure_eq_closure_graph,
    injectiveSmoothColumn_graph]

include hGraph hOrth hInjective in
theorem targetQuotient_hasSmoothCore (hClosed : operator.IsClosed) :
    (targetQuotient operator nullSpace).HasCore inclusion.range := by
  rw [targetQuotient_eq_smoothClosure inclusion column operator nullSpace hGraph hOrth hInjective hClosed]
  exact (injectiveSmoothColumn inclusion (nullSpace.mkQ.comp column) hInjective).closureHasCore

end
end JanusFormal.P0EFTJanusProgramPT12ClosedColumnTargetCore4D
