import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatHolonomyGraphInverseC1_4D

/-!
# C3 Fredholm certificate for the real-holonomy product family

The fixed common graph domain carries a globally invertible index-zero family.
Both the forward family and its canonical inverse are `C³` in operator norm.
This remains the separated fixed-geometry product model, not the global Janus
geometric family.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatHolonomyC3FredholmCertificate4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProductThroatHolonomyGraphFamily4D
open P0EFTJanusProductThroatHolonomyGraphSecondDerivative4D
open P0EFTJanusProductThroatHolonomyGraphRealFredholmFamily4D
open P0EFTJanusProductThroatHolonomyGraphInverseRegularity4D
open P0EFTJanusProductThroatHolonomyGraphInverseC1_4D

/-- Consolidated certificate for the fixed-geometry real-holonomy Fredholm
family. -/
structure ProductThroatHolonomyC3FredholmCertificate
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference : CircleTwist) where
  forward_contDiff_three :
    ContDiff ℝ 3 (productThroatCommonGraphDiracReal data fold reference)
  inverse_contDiff_three :
    ContDiff ℝ 3
      (productThroatCommonGraphDiracInverseCanonical data fold reference)
  right_inverse : ∀ (holonomy : ℝ) (state : ProductThroatHeatHilbert data),
    productThroatCommonGraphDiracCLM data fold reference holonomy
        (productThroatCommonGraphDiracInverseCanonical
          data fold reference holonomy state) = state
  left_inverse : ∀ (holonomy : ℝ)
      (state : ProductThroatCommonGraphDomain data fold reference),
    productThroatCommonGraphDiracInverseCanonical
        data fold reference holonomy
        (productThroatCommonGraphDiracCLM
          data fold reference holonomy state) = state
  index_zero : ∀ holonomy : ℝ,
    (productThroatCommonGraphDiracCLM
      data fold reference holonomy).toLinearMap.index = 0

def productThroatHolonomyC3FredholmCertificate
    (data : ProductThroatSpectralData) (fold : Fold)
    (reference : CircleTwist) :
    ProductThroatHolonomyC3FredholmCertificate data fold reference where
  forward_contDiff_three :=
    productThroatCommonGraphDirac_contDiff_three data fold reference
  inverse_contDiff_three :=
    productThroatCommonGraphDiracInverseCanonical_contDiff_three
      data fold reference
  right_inverse := by
    intro holonomy state
    rw [productThroatCommonGraphDiracInverseCanonical_eq_restricted,
      productThroatCommonGraphDiracInverse_eq_equiv_symm]
    exact (productThroatCommonGraphDiracContinuousLinearEquiv_real
      data fold reference holonomy).apply_symm_apply state
  left_inverse := by
    intro holonomy state
    rw [productThroatCommonGraphDiracInverseCanonical_eq_restricted,
      productThroatCommonGraphDiracInverse_eq_equiv_symm]
    exact (productThroatCommonGraphDiracContinuousLinearEquiv_real
      data fold reference holonomy).symm_apply_apply state
  index_zero :=
    productThroatCommonGraphDiracIndex_real_zero data fold reference

end

end P0EFTJanusProductThroatHolonomyC3FredholmCertificate4D
end JanusFormal
