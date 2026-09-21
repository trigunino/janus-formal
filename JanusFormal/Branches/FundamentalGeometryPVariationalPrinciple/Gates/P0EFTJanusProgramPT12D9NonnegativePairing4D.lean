import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusComplexDiagonalRealFredholm4D

/-! The installed D9 multiplier has nonnegative real quadratic form. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12D9NonnegativePairing4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusComplexDiagonalRealFredholm4D
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D

attribute [local instance] complexDiagonalHilbertRealInnerProductSpace

theorem complexDiagonalRealOperator_pairing_nonneg
    {Mode : Type*} [DecidableEq Mode] (weight : Mode → Real)
    (hWeight : ∀ mode, 0 ≤ weight mode)
    (state : (complexDiagonalRealOperator Mode weight).domain) :
    0 ≤ inner Real (complexDiagonalRealOperator Mode weight state)
      (state : ComplexDiagonalHilbert Mode) := by
  have hScalar (r : Real) (z : Complex) (hr : 0 ≤ r) :
      0 ≤ (inner Complex ((r : Complex) * z) z).re := by
    change 0 ≤ (inner Complex ((r : Complex) • z) z).re
    rw [inner_smul_left]
    simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg hr (inner_self_nonneg (𝕜 := Complex) (x := z))
  change 0 ≤ (inner Complex (complexDiagonalRealOperator Mode weight state)
    (state : ComplexDiagonalHilbert Mode)).re
  rw [lp.inner_eq_tsum, Complex.re_tsum (lp.summable_inner _ _)]
  apply tsum_nonneg
  intro mode
  rw [complexDiagonalRealOperator_apply]
  exact hScalar (weight mode) (state.1 mode) (hWeight mode)

/-- No choice of modes or covectors changes the sign of the D9 form. -/
theorem d9Real_pairing_nonneg
    {iota : Type*} [DecidableEq iota]
    (covector : iota → TangentVector3)
    (state : (complexDiagonalRealOperator (iota × Fin 8)
      (d9GaugeGhostUnboundedWeight covector)).domain) :
    0 ≤ inner Real
      (complexDiagonalRealOperator (iota × Fin 8)
        (d9GaugeGhostUnboundedWeight covector) state)
      (state : D9GaugeGhostUnboundedHilbert iota) := by
  apply complexDiagonalRealOperator_pairing_nonneg
  intro mode
  dsimp [d9GaugeGhostUnboundedWeight, normSquared, tangentDot]
  nlinarith [sq_nonneg (covector mode.1).x, sq_nonneg (covector mode.1).y,
    sq_nonneg (covector mode.1).z]

end
end P0EFTJanusProgramPT12D9NonnegativePairing4D
end JanusFormal
