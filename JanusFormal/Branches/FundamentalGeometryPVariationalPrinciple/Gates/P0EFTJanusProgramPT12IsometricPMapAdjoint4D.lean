import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IsometricPMapTransport4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DenseL2AdjointGraph4D

/-! Isometric transport preserves the Hilbert adjoint without an operator surjectivity assumption. -/
namespace JanusFormal.P0EFTJanusProgramPT12IsometricPMapAdjoint4D
set_option autoImplicit false
noncomputable section
open Set
open P0EFTJanusProgramPT12IsometricPMapTransport4D
open P0EFTJanusProgramPT12DenseL2AdjointGraph4D

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]
variable (equiv : E ≃ₗᵢ[Real] F) (operator : F →ₗ.[Real] F)

theorem transportedPMap_adjoint (hDense : Dense (operator.domain : Set F)) :
    (transportedPMap equiv operator).adjoint = transportedPMap equiv operator.adjoint := by
  apply LinearPMap.eq_of_eq_graph
  ext pair
  rw [adjoint_graph_iff _ (transportedPMap_denseDomain equiv operator hDense),
    transportedPMap_graph_iff, adjoint_graph_iff _ hDense]
  constructor
  · intro h test
    have hPair := h ((transportedDomainEquiv equiv operator).symm test)
    rw [← equiv.inner_map_map, ← equiv.inner_map_map, transportedPMap_action,
      LinearEquiv.apply_symm_apply] at hPair
    change inner Real (equiv pair.2) (equiv (equiv.symm test.val)) =
      inner Real (equiv pair.1) (operator test) at hPair
    simpa only [equiv.apply_symm_apply] using hPair
  · intro h test
    have hPair := h (transportedDomainEquiv equiv operator test)
    change inner Real (equiv pair.2) (equiv test.val) =
      inner Real (equiv pair.1) (operator (transportedDomainEquiv equiv operator test)) at hPair
    rw [← transportedPMap_action, equiv.inner_map_map, equiv.inner_map_map] at hPair
    exact hPair

theorem transportedPMap_selfAdjoint (hSelf : IsSelfAdjoint operator) :
    IsSelfAdjoint (transportedPMap equiv operator) := by
  rw [LinearPMap.isSelfAdjoint_def, transportedPMap_adjoint equiv operator hSelf.dense_domain,
    LinearPMap.isSelfAdjoint_def.mp hSelf]

end
end JanusFormal.P0EFTJanusProgramPT12IsometricPMapAdjoint4D
