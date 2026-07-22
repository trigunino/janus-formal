import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerSixCoefficientClosure4D

/-!
# Euler coefficient estimates from bounded boundary operators

The six tangential coefficients of the explicit Cauchy-jet residual should not
carry six unrelated constants and six manually repeated integral estimates.
The natural analytic datum is a continuous linear operator on the completed
Cauchy boundary space for each normal-profile sector.

If the concrete coefficient representative agrees almost everywhere with the
output of such an operator, then:

* square-integrability of the coefficient is automatic;
* its `L²` norm is bounded by the operator norm;
* separated product integrability follows from Fubini and the already closed
  normal-profile moments;
* the coefficient constant is simply the operator norm.

Only the actual six operator formulas, their representative equations and the
pointwise residual expansion remain PDE-specific.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerBoundedCoefficients4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal BigOperators
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetEulerNormalProfiles4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerProductRealization4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerSixCoefficientClosure4D

universe x y

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ProfileIndex :=
  CanonicalLatitudeCauchyJetEulerNormalProfileIndex

private abbrev BoundaryL2 :=
  CanonicalPhysicalScalarFirstSheetL2 period

private abbrev CompletedBoundary :=
  CanonicalScalarHilbertBoundaryDatum (Trace := BoundaryL2 period)

local instance canonicalLatitudeBaseMeasureFinite :
    IsFiniteMeasure (canonicalLatitudeBaseMeasure period) :=
  canonicalLatitudeBaseMeasure_isFinite period

namespace CanonicalPhysicalScalarCauchyJetGeometricData

/-- Six coefficient representatives controlled by six continuous operators on
the completed Cauchy boundary space. -/
structure CauchyJetEulerSixBoundedCoefficientData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore)
    (realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod) where
  coefficient : ProfileIndex → ValueCore × NormalCore →
    CanonicalLatitudeBase → Real
  coefficient_memLp : ∀ index boundary,
    MemLp (coefficient index boundary) (2 : ENNReal)
      (canonicalLatitudeBaseMeasure period)
  coefficientOperator : ProfileIndex →
    CompletedBoundary period →L[Real] BoundaryL2 period
  coefficient_toLp_eq : ∀ index boundary,
    (coefficient_memLp index boundary).toLp
        (coefficient index boundary) =
      coefficientOperator index (geometric.boundaryCoreEmbedding boundary)
  residual_sq_integrable : ∀ boundary,
    Integrable
      (fun parameter => realization.residual boundary parameter ^ 2)
      (canonicalLatitudeCauchyJetProductMeasure period)
  residual_eq : ∀ boundary parameter,
    realization.residual boundary parameter =
      canonicalLatitudeCauchyJetEulerNormalProfile .value parameter.2 *
          coefficient .value boundary parameter.1 +
        canonicalLatitudeCauchyJetEulerNormalProfile .normal parameter.2 *
          coefficient .normal boundary parameter.1 +
        canonicalLatitudeCauchyJetEulerNormalProfile .valueFirst parameter.2 *
          coefficient .valueFirst boundary parameter.1 +
        canonicalLatitudeCauchyJetEulerNormalProfile .normalFirst parameter.2 *
          coefficient .normalFirst boundary parameter.1 +
        canonicalLatitudeCauchyJetEulerNormalProfile .valueSecond parameter.2 *
          coefficient .valueSecond boundary parameter.1 +
        canonicalLatitudeCauchyJetEulerNormalProfile .normalSecond parameter.2 *
          coefficient .normalSecond boundary parameter.1

namespace CauchyJetEulerSixBoundedCoefficientData

/-- `L²` realization of one coefficient representative. -/
def coefficientL2
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    (data : geometric.CauchyJetEulerSixBoundedCoefficientData
      period hPeriod realization)
    (index : ProfileIndex) (boundary : ValueCore × NormalCore) :
    BoundaryL2 period :=
  (data.coefficient_memLp index boundary).toLp
    (data.coefficient index boundary)

/-- Squared coefficient integral equals the squared boundary `L²` norm. -/
theorem coefficient_integral_sq_eq_norm_sq
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    (data : geometric.CauchyJetEulerSixBoundedCoefficientData
      period hPeriod realization)
    (index : ProfileIndex) (boundary : ValueCore × NormalCore) :
    (∫ base, data.coefficient index boundary base ^ 2
      ∂canonicalLatitudeBaseMeasure period) =
      ‖data.coefficientL2 index boundary‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [(data.coefficient_memLp index boundary).coeFn_toLp]
    with base hCoefficient
  change data.coefficient index boundary base ^ 2 =
    inner Real
      ((data.coefficientL2 index boundary :
        CanonicalLatitudeBase → Real) base)
      ((data.coefficientL2 index boundary :
        CanonicalLatitudeBase → Real) base)
  rw [hCoefficient, real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- Coefficient square-integrability is automatic. -/
theorem coefficient_sq_integrable
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    (data : geometric.CauchyJetEulerSixBoundedCoefficientData
      period hPeriod realization)
    (index : ProfileIndex) (boundary : ValueCore × NormalCore) :
    Integrable (fun base => data.coefficient index boundary base ^ 2)
      (canonicalLatitudeBaseMeasure period) :=
  (data.coefficient_memLp index boundary).integrable_sq

/-- One separated profile/coefficient square is integrable on the product. -/
theorem separated_component_sq_integrable
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    (data : geometric.CauchyJetEulerSixBoundedCoefficientData
      period hPeriod realization)
    (index : ProfileIndex) (boundary : ValueCore × NormalCore) :
    Integrable
      (fun parameter : CanonicalLatitudeCauchyJetProductParameter =>
        (canonicalLatitudeCauchyJetEulerNormalProfile index parameter.2 *
          data.coefficient index boundary parameter.1) ^ 2)
      (canonicalLatitudeCauchyJetProductMeasure period) := by
  let normalSquare : Real → Real := fun normal =>
    canonicalLatitudeCauchyJetEulerNormalProfile index normal ^ 2
  let coefficientSquare : CanonicalLatitudeBase → Real := fun base =>
    data.coefficient index boundary base ^ 2
  have hNormal : Integrable normalSquare
      canonicalLatitudeCauchyJetNormalMeasure :=
    canonicalLatitudeCauchyJetEulerNormalProfile_sq_integrable index
  have hCoefficient : Integrable coefficientSquare
      (canonicalLatitudeBaseMeasure period) :=
    data.coefficient_sq_integrable index boundary
  unfold canonicalLatitudeCauchyJetProductMeasure
  apply (integrable_prod_iff ?_).2
  · refine ⟨Filter.Eventually.of_forall fun base => ?_, ?_⟩
    · convert hNormal.const_mul (coefficientSquare base) using 1
      funext normal
      dsimp [normalSquare, coefficientSquare]
      ring
    · have hIntegral : (fun base =>
          ∫ normal,
            ‖(canonicalLatitudeCauchyJetEulerNormalProfile index normal *
              data.coefficient index boundary base) ^ 2‖
            ∂canonicalLatitudeCauchyJetNormalMeasure) =
          fun base =>
            (∫ normal, normalSquare normal
              ∂canonicalLatitudeCauchyJetNormalMeasure) *
              coefficientSquare base := by
        funext base
        rw [show (fun normal =>
            ‖(canonicalLatitudeCauchyJetEulerNormalProfile index normal *
              data.coefficient index boundary base) ^ 2‖) =
            fun normal => coefficientSquare base * normalSquare normal by
          funext normal
          dsimp [coefficientSquare, normalSquare]
          rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
          ring]
        rw [integral_const_mul]
        ring
      rw [hIntegral]
      exact hCoefficient.const_mul _
  · exact
      (((canonicalLatitudeCauchyJetEulerNormalProfile_continuous index).comp
          continuous_snd).mul
        ((data.coefficient_memLp index boundary).1.stronglyMeasurable.measurable.comp
          measurable_fst)).pow 2 |>.aestronglyMeasurable

/-- Operator norm controls the squared coefficient integral. -/
theorem coefficient_bound_sq
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    (data : geometric.CauchyJetEulerSixBoundedCoefficientData
      period hPeriod realization)
    (index : ProfileIndex) (boundary : ValueCore × NormalCore) :
    (∫ base, data.coefficient index boundary base ^ 2
      ∂canonicalLatitudeBaseMeasure period) ≤
      ‖data.coefficientOperator index‖ ^ 2 *
        ‖geometric.boundaryCoreEmbedding boundary‖ ^ 2 := by
  rw [data.coefficient_integral_sq_eq_norm_sq,
    data.coefficient_toLp_eq]
  have hNorm := (data.coefficientOperator index).le_opNorm
    (geometric.boundaryCoreEmbedding boundary)
  nlinarith [norm_nonneg
      (data.coefficientOperator index
        (geometric.boundaryCoreEmbedding boundary)),
    norm_nonneg (data.coefficientOperator index),
    norm_nonneg (geometric.boundaryCoreEmbedding boundary)]

/-- Conversion to the six-coefficient estimate package. -/
def toSixCoefficientData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    (data : geometric.CauchyJetEulerSixBoundedCoefficientData
      period hPeriod realization) :
    geometric.CauchyJetEulerSixCoefficientData
      period hPeriod realization where
  coefficient := data.coefficient
  coefficientConstant := fun index => ‖data.coefficientOperator index‖
  coefficientConstant_nonnegative := fun index => norm_nonneg _
  coefficient_sq_integrable := data.coefficient_sq_integrable
  separated_component_sq_integrable := data.separated_component_sq_integrable
  coefficient_bound_sq := data.coefficient_bound_sq
  residual_sq_integrable := data.residual_sq_integrable
  residual_eq := data.residual_eq

/-- Final Euler product estimate generated from six bounded boundary operators. -/
def toEulerProductEstimateData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    (data : geometric.CauchyJetEulerSixBoundedCoefficientData
      period hPeriod realization) :=
  data.toSixCoefficientData.toEulerProductEstimateData

/-- Bounded-coefficient closure certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    (data : geometric.CauchyJetEulerSixBoundedCoefficientData
      period hPeriod realization) :
    ∀ boundary : ValueCore × NormalCore,
      (∫ parameter,
        realization.residual boundary parameter ^ 2
        ∂canonicalLatitudeCauchyJetProductMeasure period) ≤
        data.toSixCoefficientData.toSeparatedExpansionData.toFiniteExpansionData.combinedConstant ^ 2 *
          ‖geometric.boundaryCoreEmbedding boundary‖ ^ 2 :=
  data.toSixCoefficientData.certificate

end CauchyJetEulerSixBoundedCoefficientData

end CanonicalPhysicalScalarCauchyJetGeometricData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerBoundedCoefficients4D
end JanusFormal
