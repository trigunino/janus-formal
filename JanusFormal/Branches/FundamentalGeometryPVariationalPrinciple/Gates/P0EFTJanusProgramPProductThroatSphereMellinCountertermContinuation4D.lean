import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.NumberTheory.Harmonic.GammaDeriv
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatSphereMellinFinitePartNormalization4D

/-!
# Gamma-regularized Mellin continuation of the reduced-sphere counterterm

The explicit counterterm Mellin transform has poles at `-1`, `0`, and `1`.
Multiplication by reciprocal Gamma removes the pole at zero.  This file
records that removal, its analytic value, and its derivative without making
any assertion about continuation of the heat-remainder integrals.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatSphereMellinCountertermContinuation4D

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusProgramPProductThroatSphereShortTimeFinitePart4D
open P0EFTJanusProgramPProductThroatSphereMellinFinitePartNormalization4D

/-- Coefficient of the linear term in the reduced-sphere heat counterterm. -/
def reducedSphereMellinLinearCoefficient
    (data : ProductThroatSpectralData) : Real :=
  (5 * (monopoleAbsCharge data : Real) ^ 2 - 1) / 30

/-- Meromorphic Mellin expression of `2 / t + a₀ + a₁ t` on `(0,1]`. -/
def reducedSphereCountertermMellinPole
    (data : ProductThroatSpectralData) (spectral : Complex) : Complex :=
  2 / (spectral - 1) +
    (reducedSphereMellinConstantCoefficient data : Complex) / spectral +
    (reducedSphereMellinLinearCoefficient data : Complex) / (spectral + 1)

/-- The zero-regularized product of the counterterm Mellin expression with
reciprocal Gamma.  The Gamma recurrence has already cancelled the factor
`spectral` against the pole `a₀ / spectral`. -/
def reducedSphereCountertermMellinZeta
    (data : ProductThroatSpectralData) (spectral : Complex) : Complex :=
  (Complex.Gamma (spectral + 1))⁻¹ *
    ((reducedSphereMellinConstantCoefficient data : Complex) +
      spectral *
        (2 / (spectral - 1) +
          (reducedSphereMellinLinearCoefficient data : Complex) /
            (spectral + 1)))

/-- Away from the three Mellin poles, the regularized expression is exactly
the Gamma-normalized counterterm Mellin transform. -/
theorem reducedSphereCountertermMellinZeta_eq
    (data : ProductThroatSpectralData) {spectral : Complex}
    (hZero : spectral ≠ 0) :
    reducedSphereCountertermMellinZeta data spectral =
      (Complex.Gamma spectral)⁻¹ *
        reducedSphereCountertermMellinPole data spectral := by
  rw [Complex.one_div_Gamma_eq_self_mul_one_div_Gamma_add_one]
  unfold reducedSphereCountertermMellinZeta
    reducedSphereCountertermMellinPole
  field_simp [hZero]
  ring

@[simp]
theorem reducedSphereCountertermMellinZeta_zero
    (data : ProductThroatSpectralData) :
    reducedSphereCountertermMellinZeta data 0 =
      reducedSphereMellinConstantCoefficient data := by
  simp [reducedSphereCountertermMellinZeta, Complex.Gamma_one]

/-- The apparent pole at zero is honestly removable: the explicit extension
is analytic there. -/
theorem reducedSphereCountertermMellinZeta_analyticAt_zero
    (data : ProductThroatSpectralData) :
    AnalyticAt Complex (reducedSphereCountertermMellinZeta data) 0 := by
  unfold reducedSphereCountertermMellinZeta
  apply AnalyticAt.mul
  · exact
      (Complex.differentiable_one_div_Gamma.comp
        (differentiable_id.add_const (1 : Complex))).analyticAt 0
  · exact analyticAt_const.add
      (analyticAt_id.mul
        ((analyticAt_const.div (analyticAt_id.sub analyticAt_const) (by norm_num)).add
          (analyticAt_const.div (analyticAt_id.add analyticAt_const) (by norm_num))))

/-- The difference quotient at zero tends to the Hadamard counterterm finite
part plus the Euler--Mascheroni correction forced by Gamma normalization.
This instance-independent formulation also records the complex derivative. -/
theorem reducedSphereCountertermMellinZeta_tendsto_slope_zero
    (data : ProductThroatSpectralData) :
    Tendsto
      (slope (reducedSphereCountertermMellinZeta data) 0)
      (𝓝[≠] (0 : Complex))
      (𝓝 (reducedSphereMellinCountertermFinitePart data : Complex)) := by
  have hGammaAtOne := Complex.hasDerivAt_Gamma_one
  rw [show (1 : Complex) = 0 + 1 by ring] at hGammaAtOne
  have hGamma := hGammaAtOne.comp
    (h := fun spectral : Complex => spectral + 1) 0
    ((hasDerivAt_id (𝕜 := Complex) 0).add_const 1)
  have hInvGammaRaw := hGamma.inv (by simp [Complex.Gamma_one])
  have hInvGamma := hInvGammaRaw.congr_deriv (show
      -(-(Real.eulerMascheroniConstant : Complex) * 1) /
          (Complex.Gamma ((0 : Complex) + 1)) ^ 2 =
        (Real.eulerMascheroniConstant : Complex) by
      simp [Complex.Gamma_one])
  have hFirstRaw :=
    (hasDerivAt_const (x := (0 : Complex)) (2 : Complex)).div
      ((hasDerivAt_id 0).sub_const 1) (by norm_num)
  have hFirst := hFirstRaw.congr_deriv (show
      ((0 : Complex) * (id 0 - 1) - 2 * 1) / (id 0 - 1) ^ 2 = -2 by
    norm_num)
  have hLinearRaw :=
    (hasDerivAt_const (x := (0 : Complex))
        (reducedSphereMellinLinearCoefficient data : Complex)).div
      ((hasDerivAt_id 0).add_const 1) (by norm_num)
  have hLinear := hLinearRaw.congr_deriv (show
      ((0 : Complex) * (id 0 + 1) -
          (reducedSphereMellinLinearCoefficient data : Complex) * 1) /
          (id 0 + 1) ^ 2 =
        -(reducedSphereMellinLinearCoefficient data : Complex) by
    norm_num)
  have hTail := hFirst.add hLinear
  have hTailProductRaw := (hasDerivAt_id (𝕜 := Complex) 0).mul hTail
  have hTailProduct := hTailProductRaw.congr_deriv (show
      1 * (2 / ((0 : Complex) - 1) +
          (reducedSphereMellinLinearCoefficient data : Complex) / (0 + 1)) +
          0 * (-2 + -(reducedSphereMellinLinearCoefficient data : Complex)) =
        (reducedSphereCountertermFinitePart data : Complex) by
    simp [reducedSphereCountertermFinitePart,
      reducedSphereMellinLinearCoefficient, div_eq_mul_inv])
  have hBracket := hTailProduct.const_add
    (reducedSphereMellinConstantCoefficient data : Complex)
  have hProductRaw := hInvGamma.mul hBracket
  have hProduct := hProductRaw.congr_deriv (show
      (Real.eulerMascheroniConstant : Complex) *
          ((reducedSphereMellinConstantCoefficient data : Complex) +
            id 0 * (2 / (id (0 : Complex) - 1) +
              (reducedSphereMellinLinearCoefficient data : Complex) /
                (id 0 + 1))) +
        (Complex.Gamma ((0 : Complex) + 1))⁻¹ *
          (reducedSphereCountertermFinitePart data : Complex) =
        (reducedSphereMellinCountertermFinitePart data : Complex) by
    simp [Complex.Gamma_one]
    unfold reducedSphereMellinCountertermFinitePart
    push_cast
    ring)
  refine hProduct.tendsto_slope.congr' ?_
  filter_upwards with spectral
  rfl

/-- Reconstruction of the usual complex derivative certificate from the
instance-independent slope limit. -/
theorem reducedSphereCountertermMellinZeta_hasDerivAt_zero
    (data : ProductThroatSpectralData) :
    HasDerivAt (reducedSphereCountertermMellinZeta data)
      (reducedSphereMellinCountertermFinitePart data : Complex) 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  exact reducedSphereCountertermMellinZeta_tendsto_slope_zero data

/-- Public checkpoint for the explicit local Mellin continuation at zero. -/
theorem product_throat_sphere_mellin_counterterm_continuation_gate
    (data : ProductThroatSpectralData) :
    AnalyticAt Complex (reducedSphereCountertermMellinZeta data) 0 ∧
      reducedSphereCountertermMellinZeta data 0 =
        reducedSphereMellinConstantCoefficient data ∧
      HasDerivAt (reducedSphereCountertermMellinZeta data)
        (reducedSphereMellinCountertermFinitePart data : Complex) 0 ∧
      Tendsto
          (slope (reducedSphereCountertermMellinZeta data) 0)
          (𝓝[≠] (0 : Complex))
          (𝓝 (reducedSphereMellinCountertermFinitePart data : Complex)) :=
  ⟨reducedSphereCountertermMellinZeta_analyticAt_zero data,
    reducedSphereCountertermMellinZeta_zero data,
    reducedSphereCountertermMellinZeta_hasDerivAt_zero data,
    reducedSphereCountertermMellinZeta_tendsto_slope_zero data⟩

end
end P0EFTJanusProgramPProductThroatSphereMellinCountertermContinuation4D
end JanusFormal
