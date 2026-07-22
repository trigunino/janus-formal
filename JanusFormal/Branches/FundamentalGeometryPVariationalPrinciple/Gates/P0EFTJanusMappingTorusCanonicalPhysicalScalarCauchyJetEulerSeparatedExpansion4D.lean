import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerFiniteExpansion4D

/-!
# Separated normal profiles and boundary coefficients in the Cauchy-jet Euler residual

Every term in the Euler residual of the explicit tubular Cauchy jet separates
into

`normalProfile(ν) * boundaryCoefficient(base)`.

The normal profiles are fixed combinations of `η`, `ν η` and their first two
derivatives.  The boundary coefficients contain the physical metric
coefficients and tangential derivatives of the value and normal data.

This file turns that separated representation into the finite-component
estimate used by the final PDE closure.  For each component it is enough to
prove:

* square-integrability of the fixed normal profile;
* a boundary `L²` estimate for the tangential coefficient;
* the elementary Fubini factorization of the product square.

The global Euler estimate is then the square root of the sum of the separated
component constants squared.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerSeparatedExpansion4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal BigOperators
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGraphBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerL2Reduction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerProductRealization4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerFiniteExpansion4D

universe x y z

variable (period : Real) (hPeriod : period ≠ 0)

namespace CanonicalPhysicalScalarCauchyJetGeometricData

/-- Separated finite expansion of a realized Euler residual. -/
structure CauchyJetEulerSeparatedExpansionData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore)
    (realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod)
    (Index : Type z) [Fintype Index] where
  normalProfile : Index → Real → Real
  boundaryCoefficient : Index → ValueCore × NormalCore →
    CanonicalLatitudeBase → Real
  coefficientConstant : Index → Real
  coefficientConstant_nonnegative : ∀ index,
    0 ≤ coefficientConstant index
  normalProfile_sq_integrable : ∀ index,
    Integrable
      (fun normal => normalProfile index normal ^ 2)
      canonicalLatitudeCauchyJetNormalMeasure
  boundaryCoefficient_sq_integrable : ∀ index data,
    Integrable
      (fun base => boundaryCoefficient index data base ^ 2)
      (canonicalLatitudeBaseMeasure period)
  component_sq_integrable : ∀ index data,
    Integrable
      (fun parameter : CanonicalLatitudeCauchyJetProductParameter =>
        (normalProfile index parameter.2 *
          boundaryCoefficient index data parameter.1) ^ 2)
      (canonicalLatitudeCauchyJetProductMeasure period)
  coefficient_bound_sq : ∀ index data,
    (∫ base,
      boundaryCoefficient index data base ^ 2
      ∂canonicalLatitudeBaseMeasure period) ≤
        coefficientConstant index ^ 2 *
          ‖geometric.boundaryCoreEmbedding data‖ ^ 2
  residual_sq_integrable : ∀ data,
    Integrable
      (fun parameter => realization.residual data parameter ^ 2)
      (canonicalLatitudeCauchyJetProductMeasure period)
  residual_sq_le_sum : ∀ data parameter,
    realization.residual data parameter ^ 2 ≤
      ∑ index,
        (normalProfile index parameter.2 *
          boundaryCoefficient index data parameter.1) ^ 2

namespace CauchyJetEulerSeparatedExpansionData

/-- Squared moment of one fixed normal profile. -/
def normalProfileMoment
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    {Index : Type z} [Fintype Index]
    (expansion : geometric.CauchyJetEulerSeparatedExpansionData
      period hPeriod realization Index)
    (index : Index) : Real :=
  ∫ normal, expansion.normalProfile index normal ^ 2
    ∂canonicalLatitudeCauchyJetNormalMeasure

/-- Nonnegativity of every profile moment. -/
theorem normalProfileMoment_nonnegative
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    {Index : Type z} [Fintype Index]
    (expansion : geometric.CauchyJetEulerSeparatedExpansionData
      period hPeriod realization Index)
    (index : Index) :
    0 ≤ expansion.normalProfileMoment index := by
  unfold normalProfileMoment
  exact integral_nonneg fun _ => sq_nonneg _

/-- Constant of one separated component. -/
def separatedComponentConstant
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    {Index : Type z} [Fintype Index]
    (expansion : geometric.CauchyJetEulerSeparatedExpansionData
      period hPeriod realization Index)
    (index : Index) : Real :=
  Real.sqrt (expansion.normalProfileMoment index) *
    expansion.coefficientConstant index

/-- Nonnegativity of every separated component constant. -/
theorem separatedComponentConstant_nonnegative
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    {Index : Type z} [Fintype Index]
    (expansion : geometric.CauchyJetEulerSeparatedExpansionData
      period hPeriod realization Index)
    (index : Index) :
    0 ≤ expansion.separatedComponentConstant index :=
  mul_nonneg (Real.sqrt_nonneg _)
    (expansion.coefficientConstant_nonnegative index)

/-- Square of a separated component constant. -/
theorem separatedComponentConstant_sq
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    {Index : Type z} [Fintype Index]
    (expansion : geometric.CauchyJetEulerSeparatedExpansionData
      period hPeriod realization Index)
    (index : Index) :
    expansion.separatedComponentConstant index ^ 2 =
      expansion.normalProfileMoment index *
        expansion.coefficientConstant index ^ 2 := by
  unfold separatedComponentConstant
  rw [mul_pow, Real.sq_sqrt
    (expansion.normalProfileMoment_nonnegative index)]

/-- Fubini factorization for one separated component. -/
theorem separatedComponent_integral_eq
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    {Index : Type z} [Fintype Index]
    (expansion : geometric.CauchyJetEulerSeparatedExpansionData
      period hPeriod realization Index)
    (index : Index) (data : ValueCore × NormalCore) :
    (∫ parameter : CanonicalLatitudeCauchyJetProductParameter,
      (expansion.normalProfile index parameter.2 *
        expansion.boundaryCoefficient index data parameter.1) ^ 2
      ∂canonicalLatitudeCauchyJetProductMeasure period) =
      expansion.normalProfileMoment index *
        (∫ base,
          expansion.boundaryCoefficient index data base ^ 2
          ∂canonicalLatitudeBaseMeasure period) := by
  unfold canonicalLatitudeCauchyJetProductMeasure
  rw [integral_prod]
  · have hInner : ∀ base,
        (∫ normal,
          (expansion.normalProfile index normal *
            expansion.boundaryCoefficient index data base) ^ 2
          ∂canonicalLatitudeCauchyJetNormalMeasure) =
          expansion.normalProfileMoment index *
            expansion.boundaryCoefficient index data base ^ 2 := by
      intro base
      have hProfile := expansion.normalProfile_sq_integrable index
      calc
        (∫ normal,
          (expansion.normalProfile index normal *
            expansion.boundaryCoefficient index data base) ^ 2
          ∂canonicalLatitudeCauchyJetNormalMeasure) =
            ∫ normal,
              expansion.boundaryCoefficient index data base ^ 2 *
                expansion.normalProfile index normal ^ 2
              ∂canonicalLatitudeCauchyJetNormalMeasure := by
          apply integral_congr
          intro normal
          ring
        _ = expansion.boundaryCoefficient index data base ^ 2 *
            expansion.normalProfileMoment index := by
          rw [integral_const_mul]
          rfl
        _ = expansion.normalProfileMoment index *
            expansion.boundaryCoefficient index data base ^ 2 := by ring
    simp_rw [hInner]
    rw [← integral_const_mul]
  · exact expansion.component_sq_integrable index data

/-- Product estimate for one separated component. -/
theorem separatedComponent_bound_sq
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    {Index : Type z} [Fintype Index]
    (expansion : geometric.CauchyJetEulerSeparatedExpansionData
      period hPeriod realization Index)
    (index : Index) (data : ValueCore × NormalCore) :
    (∫ parameter : CanonicalLatitudeCauchyJetProductParameter,
      (expansion.normalProfile index parameter.2 *
        expansion.boundaryCoefficient index data parameter.1) ^ 2
      ∂canonicalLatitudeCauchyJetProductMeasure period) ≤
      expansion.separatedComponentConstant index ^ 2 *
        ‖geometric.boundaryCoreEmbedding data‖ ^ 2 := by
  rw [expansion.separatedComponent_integral_eq index data,
    expansion.separatedComponentConstant_sq index]
  exact mul_le_mul_of_nonneg_left
    (expansion.coefficient_bound_sq index data)
    (expansion.normalProfileMoment_nonnegative index)

/-- Conversion to the generic finite expansion interface. -/
def toFiniteExpansionData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    {Index : Type z} [Fintype Index]
    (expansion : geometric.CauchyJetEulerSeparatedExpansionData
      period hPeriod realization Index) :
    geometric.CauchyJetEulerFiniteExpansionData
      period hPeriod realization Index where
  component := fun index data parameter =>
    expansion.normalProfile index parameter.2 *
      expansion.boundaryCoefficient index data parameter.1
  constant := expansion.separatedComponentConstant
  constant_nonnegative := expansion.separatedComponentConstant_nonnegative
  residual_sq_integrable := expansion.residual_sq_integrable
  component_sq_integrable := expansion.component_sq_integrable
  residual_sq_le_sum := expansion.residual_sq_le_sum
  component_bound_sq := expansion.separatedComponent_bound_sq

/-- Final product Euler estimate generated by the separated expansion. -/
def toEulerProductEstimateData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    {Index : Type z} [Fintype Index]
    (expansion : geometric.CauchyJetEulerSeparatedExpansionData
      period hPeriod realization Index) :
    geometric.CauchyJetEulerProductEstimateData period hPeriod realization :=
  expansion.toFiniteExpansionData.toEulerProductEstimateData

/-- Separated-expansion certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    {Index : Type z} [Fintype Index]
    (expansion : geometric.CauchyJetEulerSeparatedExpansionData
      period hPeriod realization Index) :
    (∀ index data,
      (∫ parameter : CanonicalLatitudeCauchyJetProductParameter,
        (expansion.normalProfile index parameter.2 *
          expansion.boundaryCoefficient index data parameter.1) ^ 2
        ∂canonicalLatitudeCauchyJetProductMeasure period) ≤
        expansion.separatedComponentConstant index ^ 2 *
          ‖geometric.boundaryCoreEmbedding data‖ ^ 2) ∧
      (∀ data,
        (∫ parameter,
          realization.residual data parameter ^ 2
          ∂canonicalLatitudeCauchyJetProductMeasure period) ≤
          expansion.toFiniteExpansionData.combinedConstant ^ 2 *
            ‖geometric.boundaryCoreEmbedding data‖ ^ 2) :=
  ⟨expansion.separatedComponent_bound_sq,
    expansion.toFiniteExpansionData.product_bound_sq⟩

end CauchyJetEulerSeparatedExpansionData

end CanonicalPhysicalScalarCauchyJetGeometricData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerSeparatedExpansion4D
end JanusFormal
