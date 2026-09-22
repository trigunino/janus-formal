import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ProductClosedOperator4D

namespace JanusFormal.P0EFTJanusProgramPT12ProductOperatorPairing4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusProgramPT12ProductClosedOperator4D
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H]
  [NormedAddCommGroup K] [InnerProductSpace Real K]

theorem productOperator_pairing (A : H →ₗ.[Real] H) (B : K →ₗ.[Real] K)
    (x : (productOperator A B).domain) (y : WithLp 2 (H × K)) :
    inner Real (productOperator A B x) y =
      inner Real (A ⟨x.val.fst, ((productOperator_domain_iff A B _).mp x.property).1⟩) y.fst +
      inner Real (B ⟨x.val.snd, ((productOperator_domain_iff A B _).mp x.property).2⟩) y.snd := by
  rw [productOperator_apply]
  rfl

end
end JanusFormal.P0EFTJanusProgramPT12ProductOperatorPairing4D
