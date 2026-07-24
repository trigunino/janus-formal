import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetEulerNormalProfiles4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerSeparatedExpansion4D

/-!
# Six boundary coefficients for the explicit Cauchy-jet Euler residual

A second-order scalar Euler operator applied to the canonical Cauchy jet has six
normal-profile sectors:

* value and normal data multiplied by `a` and `b`;
* first-normal sectors multiplied by `a'` and `b'`;
* second-normal sectors multiplied by `a''` and `b''`.

All geometry and tangential differentiation is contained in six boundary
coefficient functions.  This file packages those coefficients and reduces the
full Euler graph estimate to six independent boundary `L²` estimates.

The elementary inequality

`(x₁ + ... + x₆)² ≤ 6 (x₁² + ... + x₆²)`

is absorbed by multiplying each normal profile by `sqrt 6`.  The fixed profile
moments are already finite, so only the six tangential coefficient bounds remain
PDE-specific.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal BigOperators
open MeasureTheory Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetEulerNormalProfiles4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerProductRealization4D

universe x y

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

private abbrev ProfileIndex :=
  CanonicalLatitudeCauchyJetEulerNormalProfileIndex

/-- Six-term real Cauchy--Schwarz inequality. -/
theorem six_term_sum_sq_le
    (a b c d e f : Real) :
    (a + b + c + d + e + f) ^ 2 ≤
      6 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + f ^ 2) := by
  nlinarith
    [sq_nonneg (a - b), sq_nonneg (a - c), sq_nonneg (a - d),
     sq_nonneg (a - e), sq_nonneg (a - f), sq_nonneg (b - c),
     sq_nonneg (b - d), sq_nonneg (b - e), sq_nonneg (b - f),
     sq_nonneg (c - d), sq_nonneg (c - e), sq_nonneg (c - f),
     sq_nonneg (d - e), sq_nonneg (d - f), sq_nonneg (e - f)]

namespace CanonicalPhysicalScalarCauchyJetGeometricData

/-- The six tangential coefficient functions of the canonical Euler residual. -/
structure CauchyJetEulerSixCoefficientData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore)
    (realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod) where
  coefficient : ProfileIndex → ValueCore × NormalCore →
    CanonicalLatitudeBase → Real
  coefficientConstant : ProfileIndex → Real
  coefficientConstant_nonnegative : ∀ index,
    0 ≤ coefficientConstant index
  coefficient_sq_integrable : ∀ index data,
    Integrable
      (fun base => coefficient index data base ^ 2)
      (canonicalLatitudeBaseMeasure period)
  separated_component_sq_integrable : ∀ index data,
    Integrable
      (fun parameter : CanonicalLatitudeCauchyJetProductParameter =>
        (canonicalLatitudeCauchyJetEulerNormalProfile index parameter.2 *
          coefficient index data parameter.1) ^ 2)
      (canonicalLatitudeCauchyJetProductMeasure period)
  coefficient_bound_sq : ∀ index data,
    (∫ base,
      coefficient index data base ^ 2
      ∂canonicalLatitudeBaseMeasure period) ≤
        coefficientConstant index ^ 2 *
          ‖geometric.boundaryCoreEmbedding period hPeriod data‖ ^ 2
  residual_sq_integrable : ∀ data,
    Integrable
      (fun parameter => realization.residual data parameter ^ 2)
      (canonicalLatitudeCauchyJetProductMeasure period)
  residual_eq : ∀ data parameter,
    realization.residual data parameter =
      canonicalLatitudeCauchyJetEulerNormalProfile .value parameter.2 *
          coefficient .value data parameter.1 +
        canonicalLatitudeCauchyJetEulerNormalProfile .normal parameter.2 *
          coefficient .normal data parameter.1 +
        canonicalLatitudeCauchyJetEulerNormalProfile .valueFirst parameter.2 *
          coefficient .valueFirst data parameter.1 +
        canonicalLatitudeCauchyJetEulerNormalProfile .normalFirst parameter.2 *
          coefficient .normalFirst data parameter.1 +
        canonicalLatitudeCauchyJetEulerNormalProfile .valueSecond parameter.2 *
          coefficient .valueSecond data parameter.1 +
        canonicalLatitudeCauchyJetEulerNormalProfile .normalSecond parameter.2 *
          coefficient .normalSecond data parameter.1

namespace CauchyJetEulerSixCoefficientData

/-- The six fixed profiles rescaled by `sqrt 6`. -/
def scaledNormalProfile
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    (data : geometric.CauchyJetEulerSixCoefficientData
      period hPeriod realization)
    (index : ProfileIndex) (normal : Real) : Real :=
  Real.sqrt 6 * canonicalLatitudeCauchyJetEulerNormalProfile index normal

/-- Square-integrability of every scaled normal profile. -/
theorem scaledNormalProfile_sq_integrable
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    (data : geometric.CauchyJetEulerSixCoefficientData
      period hPeriod realization)
    (index : ProfileIndex) :
    Integrable
      (fun normal => data.scaledNormalProfile period hPeriod index normal ^ 2)
      canonicalLatitudeCauchyJetNormalMeasure := by
  unfold scaledNormalProfile
  have hProfile :=
    canonicalLatitudeCauchyJetEulerNormalProfile_sq_integrable index
  convert hProfile.const_mul (6 : Real) using 1
  funext normal
  rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : Real) ≤ 6)]

/-- Integrability of the scaled separated components. -/
theorem scaled_component_sq_integrable
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    (data : geometric.CauchyJetEulerSixCoefficientData
      period hPeriod realization)
    (index : ProfileIndex) (boundary : ValueCore × NormalCore) :
    Integrable
      (fun parameter : CanonicalLatitudeCauchyJetProductParameter =>
        (data.scaledNormalProfile period hPeriod index parameter.2 *
          data.coefficient index boundary parameter.1) ^ 2)
      (canonicalLatitudeCauchyJetProductMeasure period) := by
  have hOriginal := data.separated_component_sq_integrable index boundary
  convert hOriginal.const_mul (6 : Real) using 1
  funext parameter
  unfold scaledNormalProfile
  rw [mul_assoc, mul_pow,
    Real.sq_sqrt (by norm_num : (0 : Real) ≤ 6)]

/-- Pointwise square majorization by the six rescaled components. -/
theorem residual_sq_le_scaled_sum
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    (data : geometric.CauchyJetEulerSixCoefficientData
      period hPeriod realization)
    (boundary : ValueCore × NormalCore)
    (parameter : CanonicalLatitudeCauchyJetProductParameter) :
    realization.residual boundary parameter ^ 2 ≤
      ∑ index : ProfileIndex,
        (data.scaledNormalProfile period hPeriod index parameter.2 *
          data.coefficient index boundary parameter.1) ^ 2 := by
  let a := canonicalLatitudeCauchyJetEulerNormalProfile .value parameter.2 *
    data.coefficient .value boundary parameter.1
  let b := canonicalLatitudeCauchyJetEulerNormalProfile .normal parameter.2 *
    data.coefficient .normal boundary parameter.1
  let c := canonicalLatitudeCauchyJetEulerNormalProfile .valueFirst parameter.2 *
    data.coefficient .valueFirst boundary parameter.1
  let d := canonicalLatitudeCauchyJetEulerNormalProfile .normalFirst parameter.2 *
    data.coefficient .normalFirst boundary parameter.1
  let e := canonicalLatitudeCauchyJetEulerNormalProfile .valueSecond parameter.2 *
    data.coefficient .valueSecond boundary parameter.1
  let f := canonicalLatitudeCauchyJetEulerNormalProfile .normalSecond parameter.2 *
    data.coefficient .normalSecond boundary parameter.1
  have hSix := six_term_sum_sq_le a b c d e f
  rw [data.residual_eq]
  calc
    _ ≤ 6 * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 + e ^ 2 + f ^ 2) := by
      simpa [a, b, c, d, e, f] using hSix
    _ = ∑ index : ProfileIndex,
        (data.scaledNormalProfile period hPeriod index parameter.2 *
          data.coefficient index boundary parameter.1) ^ 2 := by
      rw [show (Finset.univ : Finset ProfileIndex) =
        {.value, .normal, .valueFirst, .normalFirst, .valueSecond, .normalSecond} by
          decide]
      simp [a, b, c, d, e, f, scaledNormalProfile, mul_pow,
        Real.sq_sqrt (by norm_num : (0 : Real) ≤ 6)]
      ring

/-- Conversion to the separated expansion interface. -/
def toSeparatedExpansionData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    (data : geometric.CauchyJetEulerSixCoefficientData
      period hPeriod realization) :
    geometric.CauchyJetEulerSeparatedExpansionData
      period hPeriod realization ProfileIndex where
  normalProfile := data.scaledNormalProfile period hPeriod
  boundaryCoefficient := data.coefficient
  coefficientConstant := data.coefficientConstant
  coefficientConstant_nonnegative := data.coefficientConstant_nonnegative
  normalProfile_sq_integrable := data.scaledNormalProfile_sq_integrable period hPeriod
  boundaryCoefficient_sq_integrable := data.coefficient_sq_integrable
  component_sq_integrable := data.scaled_component_sq_integrable period hPeriod
  coefficient_bound_sq := data.coefficient_bound_sq
  residual_sq_integrable := data.residual_sq_integrable
  residual_sq_le_sum := data.residual_sq_le_scaled_sum period hPeriod

/-- Final Euler product estimate from the six tangential coefficient estimates. -/
def toEulerProductEstimateData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    (data : geometric.CauchyJetEulerSixCoefficientData
      period hPeriod realization) :
    geometric.CauchyJetEulerProductEstimateData period hPeriod realization :=
  (data.toSeparatedExpansionData period hPeriod).toEulerProductEstimateData
    period hPeriod

/-- Six-coefficient closure certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    (data : geometric.CauchyJetEulerSixCoefficientData
      period hPeriod realization) :
    ∀ boundary : ValueCore × NormalCore,
      (∫ parameter,
        realization.residual boundary parameter ^ 2
        ∂canonicalLatitudeCauchyJetProductMeasure period) ≤
        ((data.toSeparatedExpansionData period hPeriod).toFiniteExpansionData
          period hPeriod).combinedConstant ^ 2 *
          ‖geometric.boundaryCoreEmbedding period hPeriod boundary‖ ^ 2 :=
  ((data.toSeparatedExpansionData period hPeriod).toFiniteExpansionData
    period hPeriod).product_bound_sq period hPeriod

end CauchyJetEulerSixCoefficientData

end CanonicalPhysicalScalarCauchyJetGeometricData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
end JanusFormal
