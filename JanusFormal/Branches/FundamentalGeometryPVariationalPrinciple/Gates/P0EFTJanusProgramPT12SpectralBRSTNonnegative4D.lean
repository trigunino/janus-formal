import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12D9NonnegativePairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D

/-! Positivity of the installed spectral target on states with zero matter component. -/
namespace JanusFormal.P0EFTJanusProgramPT12SpectralBRSTNonnegative4D
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusComplexDiagonalMaximalOperator4D
open P0EFTJanusComplexDiagonalRealFredholm4D
open P0EFTJanusGaugeGhostBlockD9UnboundedFredholm4D
open P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
attribute [local instance] complexDiagonalHilbertRealInnerProductSpace

theorem complexDiagonalRealOperator_pairing_nonneg_on_support
    {Mode : Type*} [DecidableEq Mode] (weight : Mode → Real)
    (state : (complexDiagonalRealOperator Mode weight).domain)
    (hWeight : ∀ mode, state.1 mode ≠ 0 → 0 ≤ weight mode) :
    0 ≤ inner Real (complexDiagonalRealOperator Mode weight state)
      (state : ComplexDiagonalHilbert Mode) := by
  change 0 ≤ (inner Complex (complexDiagonalRealOperator Mode weight state)
    (state : ComplexDiagonalHilbert Mode)).re
  rw [lp.inner_eq_tsum, Complex.re_tsum (lp.summable_inner _ _)]
  apply tsum_nonneg
  intro mode
  rw [complexDiagonalRealOperator_apply]
  by_cases hZero : state.1 mode = 0
  · simp only [hZero, inner_zero_right, Complex.zero_re, le_refl]
  · change 0 ≤ (inner Complex ((weight mode : Complex) • state.1 mode) (state.1 mode)).re
    rw [inner_smul_left]
    simp only [Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero]
    exact mul_nonneg (hWeight mode hZero) (inner_self_nonneg (𝕜 := Complex) (x := state.1 mode))

theorem spectralBRST_pairing_nonneg (period : Real) (hPeriod : period ≠ 0)
    {iota : Type*} [DecidableEq iota] (covector : iota → TangentVector3) (matterMass : Real)
    (state : (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator period hPeriod covector matterMass).domain)
    (hMatter : ∀ mode : Sector × PrimitiveSpinCGeometricSignedMode, state.1 (.inr mode) = 0) :
    0 ≤ inner Real (programPGlobalGaugeFixedSpectralHessianRealMaximalOperator period hPeriod covector matterMass state)
      (state : ProgramPGlobalGaugeFixedSpectralHessianHilbert iota) := by
  classical
  apply complexDiagonalRealOperator_pairing_nonneg_on_support
  intro mode hNonzero
  rcases mode with mode | mode
  · dsimp [programPGlobalGaugeFixedSpectralHessianWeight, d9GaugeGhostUnboundedWeight,
      P0EFTJanusComplexDiagonalProperShiftFredholm4D.complexDiagonalSumWeight, normSquared, tangentDot]
    nlinarith [sq_nonneg (covector mode.1).x, sq_nonneg (covector mode.1).y,
      sq_nonneg (covector mode.1).z]
  · exact False.elim (hNonzero (hMatter mode))

end
end JanusFormal.P0EFTJanusProgramPT12SpectralBRSTNonnegative4D
