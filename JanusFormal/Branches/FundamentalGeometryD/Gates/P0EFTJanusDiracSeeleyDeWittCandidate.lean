import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusProductThroatLocalInvariants

namespace JanusFormal
namespace P0EFTJanusDiracSeeleyDeWittCandidate

set_option autoImplicit false

open P0EFTJanusProductThroatLocalInvariants

/--
Reduced coefficients omit the common prefactor `(4*pi)^(-3/2)`.

The formulas use the standard closed-manifold Laplace-type convention for a
complex rank-two Dirac operator:

* `a0`: spinor rank times volume;
* `a2`: `- integral R / 6`;
* `a4`: pure spin geometry
  `(5 R^2 - 8 Ric^2 - 7 Riem^2)/720`
  plus gauge term `integral F^2 / 3`.

Promoting this candidate to the actual Janus operator requires constructing the
SpinC/Pin bundle and checking all sign and charge conventions.
-/


def reducedDiracA0 (s : ProductThroatInvariantData) : ℝ :=
  2 * throatVolume s


noncomputable def reducedDiracA2
    (s : ProductThroatInvariantData) : ℝ :=
  -integratedScalarCurvature s / 6


noncomputable def reducedDiracA4
    (s : ProductThroatInvariantData) : ℝ :=
  (5 * integratedScalarCurvatureSquared s -
      8 * integratedRicciSquared s -
      7 * integratedRiemannSquared s) / 720 +
    integratedMonopoleFieldSquared s / 3

/-- `a0_red = 8*pi*L^3*T`. -/
theorem reduced_dirac_a0_formula
    (s : ProductThroatInvariantData) :
    reducedDiracA0 s =
      8 * s.piConstant * s.geometricLength ^ 3 * s.circleModulus := by
  unfold reducedDiracA0
  rw [throat_volume_formula]
  ring

/-- `a2_red = -(4*pi/3)*L*T`. -/
theorem reduced_dirac_a2_formula
    (s : ProductThroatInvariantData) :
    reducedDiracA2 s =
      -(4 * s.piConstant * s.geometricLength * s.circleModulus) / 3 := by
  unfold reducedDiracA2
  rw [integrated_scalar_curvature_formula]
  ring

/--
`a4_red = 2*pi*(5*n^2-1)*T/(15*L)` in the declared monopole convention.
-/
theorem reduced_dirac_a4_formula
    (s : ProductThroatInvariantData) :
    reducedDiracA4 s =
      2 * s.piConstant *
        (5 * (s.monopoleNumber : ℝ) ^ 2 - 1) *
        s.circleModulus /
        (15 * s.geometricLength) := by
  unfold reducedDiracA4
  rw [integrated_scalar_curvature_squared_formula,
    integrated_ricci_squared_formula,
    integrated_riemann_squared_formula,
    integrated_monopole_field_squared_formula]
  ring

/-- The volume coefficient is positive. -/
theorem reduced_dirac_a0_positive
    (s : ProductThroatInvariantData) :
    0 < reducedDiracA0 s := by
  rw [reduced_dirac_a0_formula]
  exact mul_pos
    (mul_pos
      (mul_pos (by norm_num) s.piConstantPositive)
      (pow_pos s.geometricLengthPositive 3))
    s.circleModulusPositive

/-- The curvature coefficient is negative for the round product throat. -/
theorem reduced_dirac_a2_negative
    (s : ProductThroatInvariantData) :
    reducedDiracA2 s < 0 := by
  rw [reduced_dirac_a2_formula]
  have hNumerator :
      0 < 4 * s.piConstant * s.geometricLength * s.circleModulus := by
    exact mul_pos
      (mul_pos
        (mul_pos (by norm_num) s.piConstantPositive)
        s.geometricLengthPositive)
      s.circleModulusPositive
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hNumerator) (by norm_num)

/-- Primitive monopole specialization `n^2=1`. -/
theorem primitive_reduced_dirac_a4_formula
    (s : ProductThroatInvariantData)
    (hPrimitiveSquare : (s.monopoleNumber : ℝ) ^ 2 = 1) :
    reducedDiracA4 s =
      8 * s.piConstant * s.circleModulus /
        (15 * s.geometricLength) := by
  rw [reduced_dirac_a4_formula, hPrimitiveSquare]
  ring

/-- The primitive-monopole `a4` coefficient is positive. -/
theorem primitive_reduced_dirac_a4_positive
    (s : ProductThroatInvariantData)
    (hPrimitiveSquare : (s.monopoleNumber : ℝ) ^ 2 = 1) :
    0 < reducedDiracA4 s := by
  rw [primitive_reduced_dirac_a4_formula s hPrimitiveSquare]
  exact div_pos
    (mul_pos
      (mul_pos (by norm_num) s.piConstantPositive)
      s.circleModulusPositive)
    (mul_pos (by norm_num) s.geometricLengthPositive)

/-- All three reduced coefficients remain linear in the circle modulus. -/
theorem reduced_coefficients_factor_circle_modulus
    (s : ProductThroatInvariantData) :
    reducedDiracA0 s =
        s.circleModulus *
          (8 * s.piConstant * s.geometricLength ^ 3) /\
    reducedDiracA2 s =
        s.circleModulus *
          (-(4 * s.piConstant * s.geometricLength) / 3) /\
    reducedDiracA4 s =
        s.circleModulus *
          (2 * s.piConstant *
            (5 * (s.monopoleNumber : ℝ) ^ 2 - 1) /
            (15 * s.geometricLength)) := by
  constructor
  · rw [reduced_dirac_a0_formula]
    ring
  · constructor
    · rw [reduced_dirac_a2_formula]
      ring
    · rw [reduced_dirac_a4_formula]
      ring

/--
The explicit local coefficients strengthen the locality no-go: the monopole can
change the coefficient and its sign, but not the affine dependence on `T`.
The modulus must still be selected by nonlocal winding data plus a fixed
renormalization prescription or by additional interactions.
-/
structure DiracSeeleyDeWittPhysicalStatus where
  actualDiracSquareConstructed : Prop
  lichnerowiczConventionMatched : Prop
  gaugeChargeConventionMatched : Prop
  reducedA0Verified : Prop
  reducedA2Verified : Prop
  reducedA4Verified : Prop
  commonPrefactorRestored : Prop
  finiteRenormalizedCoefficientsFixed : Prop
  fullNonlocalActionComputed : Prop


def diracSeeleyDeWittPhysicalClosure
    (s : DiracSeeleyDeWittPhysicalStatus) : Prop :=
  s.actualDiracSquareConstructed /\
  s.lichnerowiczConventionMatched /\
  s.gaugeChargeConventionMatched /\
  s.reducedA0Verified /\
  s.reducedA2Verified /\
  s.reducedA4Verified /\
  s.commonPrefactorRestored /\
  s.finiteRenormalizedCoefficientsFixed /\
  s.fullNonlocalActionComputed

end P0EFTJanusDiracSeeleyDeWittCandidate
end JanusFormal
