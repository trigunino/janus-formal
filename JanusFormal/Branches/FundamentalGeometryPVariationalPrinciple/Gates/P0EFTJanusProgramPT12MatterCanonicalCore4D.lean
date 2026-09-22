import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MatterCanonicalOperator4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedFeatureCore4D

namespace JanusFormal.P0EFTJanusProgramPT12MatterCanonicalCore4D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Topology
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT12MatterCanonicalOperator4D
open P0EFTJanusProgramPT12ClosedFeatureCore4D
attribute [local instance] programPPrimitiveSpinCMatterHilbertRealInnerProductSpace
variable (period : Real) (hPeriod : period ≠ 0) (massSquared : Real)

/-- Finite signed modes are a genuine operator core in canonical L². -/
theorem matterCanonicalOperator_hasCore :
    (matterCanonicalOperator period hPeriod massSquared).HasCore matterCanonicalFiniteEmbedding.range := by
  let A := matterCanonicalOperator period hPeriod massSquared
  let i := matterCanonicalFiniteEmbedding
  let o := i.comp ((programPPrimitiveSpinCMatterFiniteHessian period hPeriod massSquared).restrictScalars Real)
  have hMem : ∀ x, i x ∈ A.domain := fun x => (matterCanonicalFiniteDomain period hPeriod massSquared x).property
  have hApply : ∀ x, A ⟨i x, hMem x⟩ = o x := matterCanonicalOperator_finite_apply period hPeriod massSquared
  have hClosed : A.IsClosed := (matterCanonicalOperator_selfAdjoint period hPeriod massSquared).isClosed
  have hRestrict : A.domRestrict i.range ≤ A := LinearPMap.domRestrict_le
  have hClosable := hClosed.isClosable.leIsClosable hRestrict
  refine ⟨?_, ?_⟩
  · rintro _ ⟨x, rfl⟩
    exact hMem x
  · apply LinearPMap.eq_of_eq_graph
    rw [← hClosable.graph_closure_eq_closure_graph, smoothRestriction_graph i o A hMem hApply]
    apply le_antisymm
    · apply Submodule.topologicalClosure_minimal
      · rintro _ ⟨x, rfl⟩
        exact A.mem_graph_iff.mpr ⟨⟨i x, hMem x⟩, rfl, hApply x⟩
      · exact hClosed
    · intro p hp
      have hGraph := (matterCanonicalOperator_graph_iff period hPeriod massSquared p.1 p.2).mp hp
      exact (programPPrimitiveSpinCMatterGraphFiniteLinearMap_denseRange period hPeriod massSquared).induction_on
        (p := fun g => g.val ∈ (i.prod o).range.topologicalClosure) ⟨p, hGraph⟩
        ((i.prod o).range.isClosed_topologicalClosure.preimage continuous_subtype_val)
        (fun x => Submodule.le_topologicalClosure _ ⟨x, rfl⟩)

end
end JanusFormal.P0EFTJanusProgramPT12MatterCanonicalCore4D
