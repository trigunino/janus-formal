import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProductThroatUnboundedDiracFredholm4D

/-!
# Exact sign scope of the product-throat Dirac model

For a fixed fold every spectral value has the fold sign, independently of the
mode.  Thus this signed positive square root has no within-fold spectral
crossing and is not, by itself, a construction of the signed geometric Janus
Dirac operator.
-/

namespace JanusFormal
namespace P0EFTJanusProductThroatDiracSignScope4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProductThroatHeatOperator4D
open P0EFTJanusProductThroatUnboundedDiracSquared4D
open P0EFTJanusProductThroatUnboundedDirac4D
open P0EFTJanusProductThroatUnboundedDiracFredholm4D

theorem productThroatDiracSquaredEigenvalue_positive
    (data : ProductThroatSpectralData) (fold : Fold) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    0 < productThroatDiracSquaredEigenvalue data fold twist mode := by
  unfold productThroatDiracSquaredEigenvalue
  exact add_pos_of_pos_of_nonneg
    (sphere_eigenvalue_squared_positive data mode.1.1)
    (by
      rw [circleOperatorSquaredEigenvalue_eq_eigenvalueSq]
      exact eigenvalueSq_nonnegative fold twist mode.2)

theorem productThroatDiracEigenvalue_positive_fold_pos
    (data : ProductThroatSpectralData) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    0 < productThroatDiracEigenvalue data Fold.positive twist mode := by
  rw [productThroatDiracEigenvalue, Fold.positive_spectralSign, one_mul]
  exact Real.sqrt_pos.2
    (productThroatDiracSquaredEigenvalue_positive data Fold.positive twist mode)

theorem productThroatDiracEigenvalue_pt_fold_neg
    (data : ProductThroatSpectralData) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    productThroatDiracEigenvalue data Fold.pt twist mode < 0 := by
  rw [productThroatDiracEigenvalue, Fold.pt_spectralSign, neg_one_mul]
  exact neg_lt_zero.mpr (Real.sqrt_pos.2
    (productThroatDiracSquaredEigenvalue_positive data Fold.pt twist mode))

theorem productThroatDiracEigenvalue_pt_eq_neg_positive
    (data : ProductThroatSpectralData) (twist : CircleTwist)
    (mode : ProductThroatHeatMode data) :
    productThroatDiracEigenvalue data Fold.pt twist mode =
      -productThroatDiracEigenvalue data Fold.positive twist mode := by
  have hSquared :
      productThroatDiracSquaredEigenvalue data Fold.pt twist mode =
        productThroatDiracSquaredEigenvalue data Fold.positive twist mode := by
    unfold productThroatDiracSquaredEigenvalue
    rw [circleOperatorSquaredEigenvalue_eq_eigenvalueSq,
      circleOperatorSquaredEigenvalue_eq_eigenvalueSq,
      pt_eigenvalueSq_eq_positive]
  simp [productThroatDiracEigenvalue, Fold.positive_spectralSign,
    Fold.pt_spectralSign, hSquared]

/-- A mode-sign crossing would require two modes of one fixed fold to lie on
opposite sides of zero. -/
def ProductThroatDiracHasModeSignCrossing
    (data : ProductThroatSpectralData) (fold : Fold)
    (twist : CircleTwist) : Prop :=
  ∃ negativeMode positiveMode : ProductThroatHeatMode data,
    productThroatDiracEigenvalue data fold twist negativeMode < 0 ∧
      0 < productThroatDiracEigenvalue data fold twist positiveMode

theorem productThroatDirac_has_no_mode_sign_crossing
    (data : ProductThroatSpectralData) (fold : Fold)
    (twist : CircleTwist) :
    ¬ ProductThroatDiracHasModeSignCrossing data fold twist := by
  rintro ⟨negativeMode, positiveMode, hNegative, hPositive⟩
  cases fold with
  | positive =>
      exact (not_lt_of_ge
        (productThroatDiracEigenvalue_positive_fold_pos
          data twist negativeMode).le) hNegative
  | pt =>
      exact (not_lt_of_ge
        (productThroatDiracEigenvalue_pt_fold_neg
          data twist positiveMode).le) hPositive

end

end P0EFTJanusProductThroatDiracSignScope4D
end JanusFormal
