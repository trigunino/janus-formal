import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusInfiniteTemporalFourierSobolevBridge4D

/-!
# Zero-mode exactness in the completed temporal H1 sector

The completed temporal coefficient derivative has kernel exactly equal to the
range of the constant Fourier mode.  Injective Fourier synthesis transports
the same kernel computation to the genuine quotient `L²` derivative field.

This is only the scalar, spatially constant temporal sector.  It is not the
cohomology of the full smooth or Sobolev BRST complex.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusInfiniteTemporalH1ZeroModeCohomology4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusCircleUnboundedDiracDomain
open P0EFTJanusMappingTorusFiniteTemporalFourierGaugeGhostCohomology4D
open P0EFTJanusMappingTorusInfiniteTemporalFourierSobolevBridge4D

variable (period : Real) [hPeriodPos : Fact (0 < period)]

/-- Inclusion of the constant temporal coefficient into the completed
weighted coordinates. -/
def temporalH1ZeroModeCoefficientOperator :
    Complex →L[Complex] TemporalH1CoefficientHilbert period :=
  lp.singleContinuousLinearMap Complex (fun _ : Int => Complex) 2 0

@[simp]
theorem temporalH1ZeroModeCoefficientOperator_apply
    (coefficient : Complex) (mode : Int) :
    temporalH1ZeroModeCoefficientOperator period coefficient mode =
      if mode = 0 then coefficient else 0 := by
  by_cases hMode : mode = 0
  · subst mode
    simp [temporalH1ZeroModeCoefficientOperator]
  · simp [temporalH1ZeroModeCoefficientOperator, hMode, Ne.symm hMode]

theorem temporalH1ZeroModeCoefficientOperator_injective :
    Function.Injective (temporalH1ZeroModeCoefficientOperator period) := by
  intro first second hEqual
  have hZero := congrArg
    (fun state : TemporalH1CoefficientHilbert period => state 0) hEqual
  simpa using hZero

theorem temporalH1DerivativeMultiplier_ne_zero
    (mode : Int) (hMode : mode ≠ 0) :
    temporalFourierDerivativeMultiplier period mode ≠ 0 := by
  have hPi : (Real.pi : Complex) ≠ 0 := by
    exact_mod_cast Real.pi_pos.ne'
  have hModeComplex : (mode : Complex) ≠ 0 := by
    exact_mod_cast hMode
  have hPeriodComplex : (period : Complex) ≠ 0 := by
    exact_mod_cast hPeriodPos.out.ne'
  exact div_ne_zero
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) hPi)
      Complex.I_ne_zero) hModeComplex) hPeriodComplex

theorem temporalH1FieldScale_ne_zero (mode : Int) :
    temporalH1FieldScale period mode ≠ 0 := by
  unfold temporalH1FieldScale
  exact inv_ne_zero (Complex.ofReal_ne_zero.mpr
    (Real.sqrt_ne_zero'.2 (temporalH1Weight_pos period mode)))

private theorem temporalH1_state_mode_eq_zero_of_derivative_eq_zero
    (state : TemporalH1CoefficientHilbert period)
    (hDerivative : temporalH1DerivativeCoefficientOperator period state = 0)
    (mode : Int) (hMode : mode ≠ 0) :
    state mode = 0 := by
  have hEvaluated := congrArg
    (fun value : CircleHilbert => value mode) hDerivative
  have hProduct :
      temporalFourierDerivativeMultiplier period mode *
          temporalH1FieldCoefficientOperator period state mode = 0 := by
    simpa using hEvaluated
  have hField : temporalH1FieldCoefficientOperator period state mode = 0 :=
    (mul_eq_zero.mp hProduct).resolve_left
      (temporalH1DerivativeMultiplier_ne_zero period mode hMode)
  rw [temporalH1FieldCoefficientOperator_apply] at hField
  exact (mul_eq_zero.mp hField).resolve_left
    (temporalH1FieldScale_ne_zero period mode)

/-- Exact coefficient-level zero-mode computation in the infinite temporal
`H¹` completion. -/
theorem temporalH1DerivativeCoefficient_kernel_eq_zeroMode_range :
    LinearMap.ker
        (temporalH1DerivativeCoefficientOperator period).toLinearMap =
      LinearMap.range
        (temporalH1ZeroModeCoefficientOperator period).toLinearMap := by
  apply le_antisymm
  · intro state hKernel
    change temporalH1DerivativeCoefficientOperator period state = 0 at hKernel
    refine ⟨state 0, ?_⟩
    ext mode
    by_cases hMode : mode = 0
    · subst mode
      simp
    · have hZero := temporalH1_state_mode_eq_zero_of_derivative_eq_zero
        period state hKernel mode hMode
      simp [hMode, hZero]
  · rintro state ⟨coefficient, rfl⟩
    change temporalH1DerivativeCoefficientOperator period
        (temporalH1ZeroModeCoefficientOperator period coefficient) = 0
    ext mode
    by_cases hMode : mode = 0
    · subst mode
      simp [temporalFourierDerivativeMultiplier]
    · simp [hMode]

/-- Injective quotient Fourier synthesis transports the same exact kernel to
the actual mapping-torus quotient `L²` derivative field. -/
theorem temporalH1DerivativeL2_kernel_eq_zeroMode_range :
    LinearMap.ker (temporalH1DerivativeL2 period).toLinearMap =
      LinearMap.range
        (temporalH1ZeroModeCoefficientOperator period).toLinearMap := by
  apply le_antisymm
  · intro state hKernel
    change temporalH1DerivativeL2 period state = 0 at hKernel
    have hCoefficient :
        temporalH1DerivativeCoefficientOperator period state = 0 := by
      apply mappingTorusTemporalL2Synthesis_injective period
      simpa [temporalH1DerivativeL2] using hKernel
    have hCoefficientKernel : state ∈ LinearMap.ker
        (temporalH1DerivativeCoefficientOperator period).toLinearMap :=
      hCoefficient
    rw [temporalH1DerivativeCoefficient_kernel_eq_zeroMode_range period]
      at hCoefficientKernel
    exact hCoefficientKernel
  · intro state hRange
    rw [← temporalH1DerivativeCoefficient_kernel_eq_zeroMode_range period]
      at hRange
    change temporalH1DerivativeCoefficientOperator period state = 0 at hRange
    change temporalH1DerivativeL2 period state = 0
    simp [temporalH1DerivativeL2, hRange]

/-- Public summary: the constant mode embeds faithfully and is precisely the
kernel both before and after quotient `L²` Fourier synthesis. -/
theorem mappingTorus_infiniteTemporalH1_zeroMode_exact4D :
    Function.Injective (temporalH1ZeroModeCoefficientOperator period) ∧
      LinearMap.ker
          (temporalH1DerivativeCoefficientOperator period).toLinearMap =
        LinearMap.range
          (temporalH1ZeroModeCoefficientOperator period).toLinearMap ∧
      LinearMap.ker (temporalH1DerivativeL2 period).toLinearMap =
        LinearMap.range
          (temporalH1ZeroModeCoefficientOperator period).toLinearMap :=
  ⟨temporalH1ZeroModeCoefficientOperator_injective period,
    temporalH1DerivativeCoefficient_kernel_eq_zeroMode_range period,
    temporalH1DerivativeL2_kernel_eq_zeroMode_range period⟩

end

end P0EFTJanusMappingTorusInfiniteTemporalH1ZeroModeCohomology4D
end JanusFormal
