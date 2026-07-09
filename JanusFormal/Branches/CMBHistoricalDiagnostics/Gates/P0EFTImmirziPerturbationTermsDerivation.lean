namespace JanusFormal
namespace P0EFTImmirziPerturbationTermsDerivation

set_option autoImplicit false

structure ImmirziPerturbationTerms where
  momentumTermEncoded : Prop
  shearTermEncoded : Prop
  slipTermEncoded : Prop
  momentumCoefficientDerived : Prop
  shearCoefficientDerived : Prop
  slipCoefficientDerived : Prop

def perturbationTermsEncoded (t : ImmirziPerturbationTerms) : Prop :=
  t.momentumTermEncoded /\
  t.shearTermEncoded /\
  t.slipTermEncoded

def perturbationTermsDerived (t : ImmirziPerturbationTerms) : Prop :=
  perturbationTermsEncoded t /\
  t.momentumCoefficientDerived /\
  t.shearCoefficientDerived /\
  t.slipCoefficientDerived

theorem encoded_targets_do_not_imply_derived_coefficients
    (t : ImmirziPerturbationTerms)
    (_hEncoded : perturbationTermsEncoded t)
    (hMissing : Not t.momentumCoefficientDerived) :
    Not (perturbationTermsDerived t) := by
  intro h
  exact hMissing h.right.left

theorem all_coefficients_close_terms
    (t : ImmirziPerturbationTerms)
    (hEncoded : perturbationTermsEncoded t)
    (hQ : t.momentumCoefficientDerived)
    (hPi : t.shearCoefficientDerived)
    (hSlip : t.slipCoefficientDerived) :
    perturbationTermsDerived t := by
  exact And.intro hEncoded (And.intro hQ (And.intro hPi hSlip))

end P0EFTImmirziPerturbationTermsDerivation
end JanusFormal
