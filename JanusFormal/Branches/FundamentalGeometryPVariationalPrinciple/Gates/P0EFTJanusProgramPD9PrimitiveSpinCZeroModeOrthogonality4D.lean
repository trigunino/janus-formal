import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D

/-!
# Orthogonality of the primitive SpinC zero-sphere tower

The rotating-frame coefficients have integer frequencies of one parity.
Their frequency differences are therefore ordinary integral Fourier
frequencies, so integration over one mapping-torus period is exact.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9PrimitiveSpinCZeroModeOrthogonality4D

set_option autoImplicit false
noncomputable section

open scoped ComplexConjugate Interval
open P0EFTJanusProgramPD9PrimitiveSpinCNormalModeSection4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

theorem normalRootSpinFrameFrequency_sub
    (hPeriod : period ≠ 0)
    (choice : NormalRootChoice) (first second : Int) :
    normalRootSpinFrameFrequency period choice second -
        normalRootSpinFrameFrequency period choice first =
      2 * Real.pi * ((second - first : Int) : Real) / period := by
  cases choice <;>
    simp [normalRootSpinFrameFrequency,
      normalRootSpinFrameModeIndex] <;>
    push_cast <;>
    field_simp [hPeriod] <;>
    ring

theorem normalRootSpinFrameExponential_conj_mul
    (choice : NormalRootChoice) (first second : Int) (time : Real) :
    conj
          (normalRootSpinFrameExponential period choice first time) *
        normalRootSpinFrameExponential period choice second time =
      Complex.exp
        (((normalRootSpinFrameFrequency period choice second -
              normalRootSpinFrameFrequency period choice first : Real) :
            Complex) * Complex.I * (time : Complex)) := by
  simp only [normalRootSpinFrameExponential]
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

private theorem normalRootSpinFrameDifferenceCoefficient_ne_zero
    (hPeriod : period ≠ 0)
    (choice : NormalRootChoice) (first second : Int)
    (hModes : first ≠ second) :
    (((normalRootSpinFrameFrequency period choice second -
          normalRootSpinFrameFrequency period choice first : Real) :
        Complex) * Complex.I) ≠ 0 := by
  have hDifferenceInt : second - first ≠ 0 :=
    sub_ne_zero.mpr hModes.symm
  have hDifferenceReal : ((second - first : Int) : Real) ≠ 0 := by
    exact_mod_cast hDifferenceInt
  have hFrequency :
      normalRootSpinFrameFrequency period choice second -
          normalRootSpinFrameFrequency period choice first ≠ 0 := by
    rw [normalRootSpinFrameFrequency_sub
      period hPeriod choice first second]
    exact div_ne_zero
      (mul_ne_zero
        (mul_ne_zero (by norm_num) Real.pi_ne_zero)
        hDifferenceReal)
      hPeriod
  exact mul_ne_zero (Complex.ofReal_ne_zero.mpr hFrequency)
    Complex.I_ne_zero

private theorem normalRootSpinFrameDifferenceCoefficient_period
    (hPeriod : period ≠ 0)
    (choice : NormalRootChoice) (first second : Int) :
    (((normalRootSpinFrameFrequency period choice second -
          normalRootSpinFrameFrequency period choice first : Real) :
        Complex) * Complex.I) * (period : Complex) =
      ((second - first : Int) : Complex) *
        (2 * Real.pi * Complex.I) := by
  rw [normalRootSpinFrameFrequency_sub
    period hPeriod choice first second]
  push_cast
  field_simp [hPeriod]

theorem normalRootSpinFrameExponential_orthogonal
    (hPeriod : period ≠ 0)
    (choice : NormalRootChoice) (first second : Int)
    (hModes : first ≠ second) :
    (∫ time in (0 : Real)..period,
        conj
            (normalRootSpinFrameExponential period choice first time) *
          normalRootSpinFrameExponential period choice second time) = 0 := by
  let coefficient : Complex :=
    ((normalRootSpinFrameFrequency period choice second -
        normalRootSpinFrameFrequency period choice first : Real) : Complex) *
      Complex.I
  have hCoefficient : coefficient ≠ 0 :=
    normalRootSpinFrameDifferenceCoefficient_ne_zero
      period hPeriod choice first second hModes
  rw [show
      (fun time : Real =>
        conj
            (normalRootSpinFrameExponential period choice first time) *
          normalRootSpinFrameExponential period choice second time) =
        fun time : Real => Complex.exp (coefficient * time) by
      funext time
      exact normalRootSpinFrameExponential_conj_mul
        period choice first second time]
  rw [integral_exp_mul_complex hCoefficient]
  have hEndpoint :
      Complex.exp (coefficient * (period : Complex)) = 1 := by
    rw [show coefficient * (period : Complex) =
        ((second - first : Int) : Complex) *
          (2 * Real.pi * Complex.I) by
      exact normalRootSpinFrameDifferenceCoefficient_period
        period hPeriod choice first second]
    exact Complex.exp_int_mul_two_pi_mul_I (second - first)
  rw [hEndpoint]
  simp

theorem normalRootSpinFrameExponential_norm_integral
    (choice : NormalRootChoice) (mode : Int) :
    (∫ time in (0 : Real)..period,
        conj
            (normalRootSpinFrameExponential period choice mode time) *
          normalRootSpinFrameExponential period choice mode time) =
      (period : Complex) := by
  simp_rw [normalRootSpinFrameExponential_conj_mul]
  simp

theorem normalRootSpinFrameExponential_pairing
    (hPeriod : period ≠ 0)
    (choice : NormalRootChoice) (first second : Int) :
    (∫ time in (0 : Real)..period,
        conj
            (normalRootSpinFrameExponential period choice first time) *
          normalRootSpinFrameExponential period choice second time) =
      if first = second then (period : Complex) else 0 := by
  by_cases hModes : first = second
  · subst second
    simp only [if_pos rfl]
    exact normalRootSpinFrameExponential_norm_integral
      period choice first
  · rw [if_neg hModes]
    exact normalRootSpinFrameExponential_orthogonal
      period hPeriod choice first second hModes

theorem normalRootSpinFrameExponential_normalized_pairing
    (hPeriod : period ≠ 0)
    (choice : NormalRootChoice) (first second : Int) :
    (period : Complex)⁻¹ *
        (∫ time in (0 : Real)..period,
          conj
              (normalRootSpinFrameExponential period choice first time) *
            normalRootSpinFrameExponential period choice second time) =
      if first = second then 1 else 0 := by
  rw [normalRootSpinFrameExponential_pairing
    period hPeriod choice first second]
  split_ifs
  · exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr hPeriod)
  · simp

/-- A finite packet in one normal-root tower. -/
def normalRootSpinFrameFinitePacket
    (choice : NormalRootChoice) (modes : Finset Int)
    (coefficient : Int → Complex) (time : Real) : Complex :=
  ∑ mode ∈ modes,
    coefficient mode *
      normalRootSpinFrameExponential period choice mode time

private theorem normalRootSpinFrameFinitePacket_conj_mul
    (choice : NormalRootChoice) (modes : Finset Int)
    (coefficient : Int → Complex) (time : Real) :
    conj
          (normalRootSpinFrameFinitePacket
            period choice modes coefficient time) *
        normalRootSpinFrameFinitePacket
          period choice modes coefficient time =
      ∑ first ∈ modes, ∑ second ∈ modes,
        (conj (coefficient first) * coefficient second) *
          (conj
              (normalRootSpinFrameExponential
                period choice first time) *
            normalRootSpinFrameExponential
              period choice second time) := by
  simp only [normalRootSpinFrameFinitePacket, map_sum, map_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro first hFirst
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro second hSecond
  ring

/-- Finite Parseval identity for each twisted normal-root tower. -/
theorem normalRootSpinFrameFinitePacket_parseval
    (hPeriod : period ≠ 0)
    (choice : NormalRootChoice) (modes : Finset Int)
    (coefficient : Int → Complex) :
    (period : Complex)⁻¹ *
        (∫ time in (0 : Real)..period,
          conj
              (normalRootSpinFrameFinitePacket
                period choice modes coefficient time) *
            normalRootSpinFrameFinitePacket
              period choice modes coefficient time) =
      ∑ mode ∈ modes,
        conj (coefficient mode) * coefficient mode := by
  rw [show
      (fun time : Real =>
        conj
            (normalRootSpinFrameFinitePacket
              period choice modes coefficient time) *
          normalRootSpinFrameFinitePacket
            period choice modes coefficient time) =
        fun time : Real =>
          ∑ first ∈ modes, ∑ second ∈ modes,
            (conj (coefficient first) * coefficient second) *
              (conj
                  (normalRootSpinFrameExponential
                    period choice first time) *
                normalRootSpinFrameExponential
                  period choice second time) by
      funext time
      exact normalRootSpinFrameFinitePacket_conj_mul
        period choice modes coefficient time]
  have hPairIntegrable (first second : Int) :
      IntervalIntegrable
        (fun time : Real =>
          (conj (coefficient first) * coefficient second) *
            (conj
                (normalRootSpinFrameExponential
                  period choice first time) *
              normalRootSpinFrameExponential
                period choice second time))
        MeasureTheory.volume 0 period :=
    Continuous.intervalIntegrable (by
      simp only [normalRootSpinFrameExponential]
      fun_prop) _ _
  have hInner (first : Int) :
      (∫ time in (0 : Real)..period,
        ∑ second ∈ modes,
          (conj (coefficient first) * coefficient second) *
            (conj
                (normalRootSpinFrameExponential
                  period choice first time) *
              normalRootSpinFrameExponential
                period choice second time)) =
        ∑ second ∈ modes,
          ∫ time in (0 : Real)..period,
            (conj (coefficient first) * coefficient second) *
              (conj
                  (normalRootSpinFrameExponential
                    period choice first time) *
                normalRootSpinFrameExponential
                  period choice second time) :=
    intervalIntegral.integral_finsetSum fun second _ =>
      hPairIntegrable first second
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [hInner, intervalIntegral.integral_const_mul,
      normalRootSpinFrameExponential_pairing
      period hPeriod choice]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro first hFirst
    simp [hFirst, Complex.ofReal_ne_zero.mpr hPeriod]
    field_simp [Complex.ofReal_ne_zero.mpr hPeriod]
  · intro first hFirst
    apply (IntervalIntegrable.sum modes fun second _ =>
      hPairIntegrable first second).congr
    intro time hTime
    simp

/-- Pairing with one basis mode recovers its coefficient in a finite
packet. -/
theorem normalRootSpinFrameFinitePacket_coefficient
    (hPeriod : period ≠ 0)
    (choice : NormalRootChoice) (modes : Finset Int)
    (coefficient : Int → Complex) (mode : Int) :
    (period : Complex)⁻¹ *
        (∫ time in (0 : Real)..period,
          conj
              (normalRootSpinFrameExponential
                period choice mode time) *
            normalRootSpinFrameFinitePacket
              period choice modes coefficient time) =
      if mode ∈ modes then coefficient mode else 0 := by
  have hIntegrable (index : Int) :
      IntervalIntegrable
        (fun time : Real =>
          coefficient index *
            (conj
                (normalRootSpinFrameExponential
                  period choice mode time) *
              normalRootSpinFrameExponential
                period choice index time))
        MeasureTheory.volume 0 period :=
    Continuous.intervalIntegrable (by
      simp only [normalRootSpinFrameExponential]
      fun_prop) _ _
  rw [show
      (fun time : Real =>
        conj
            (normalRootSpinFrameExponential
              period choice mode time) *
          normalRootSpinFrameFinitePacket
            period choice modes coefficient time) =
        fun time : Real =>
          ∑ index ∈ modes,
            coefficient index *
              (conj
                  (normalRootSpinFrameExponential
                    period choice mode time) *
                normalRootSpinFrameExponential
                  period choice index time) by
      funext time
      simp [normalRootSpinFrameFinitePacket, Finset.mul_sum]
      ring]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul,
      normalRootSpinFrameExponential_pairing
        period hPeriod choice]
    by_cases hMode : mode ∈ modes
    · simp [hMode]
      field_simp [Complex.ofReal_ne_zero.mpr hPeriod]
    · simp [hMode]
  · exact fun index hIndex => hIntegrable index

/-- A finite packet which vanishes pointwise has no coefficient. -/
theorem normalRootSpinFrameFinitePacket_eq_zero_coefficients
    (hPeriod : period ≠ 0)
    (choice : NormalRootChoice) (modes : Finset Int)
    (coefficient : Int → Complex)
    (hZero :
      ∀ time,
        normalRootSpinFrameFinitePacket
          period choice modes coefficient time = 0) :
    ∀ mode ∈ modes, coefficient mode = 0 := by
  intro mode hMode
  have hCoefficient :=
    normalRootSpinFrameFinitePacket_coefficient
      period hPeriod choice modes coefficient mode
  rw [if_pos hMode] at hCoefficient
  simpa only [hZero, mul_zero, intervalIntegral.integral_zero]
    using hCoefficient.symm

end
end P0EFTJanusProgramPD9PrimitiveSpinCZeroModeOrthogonality4D
end JanusFormal
