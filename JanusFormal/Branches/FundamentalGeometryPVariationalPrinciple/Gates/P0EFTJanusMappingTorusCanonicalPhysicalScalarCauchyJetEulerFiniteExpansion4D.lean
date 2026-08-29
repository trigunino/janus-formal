import Mathlib.MeasureTheory.Integral.Prod
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerProductRealization4D

/-!
# Finite component estimates for the Cauchy-jet Euler residual

The remaining explicit Cauchy-jet estimate concerns one scalar residual on
boundary-times-normal coordinates.  In a local second-order operator this
residual is a finite sum of terms: fixed normal profiles and their derivatives
multiply boundary values, tangential derivatives and local coefficient
functions.

This file packages that finite expansion.  If the square of the residual is
pointwise bounded by a finite sum of component squares, and every component has
an `L²` estimate against the boundary Hilbert-pair norm, then the required Euler
product estimate follows automatically.  The combined constant is the square
root of the sum of the component constants squared.

Thus the remaining PDE work can be performed term by term instead of proving one
opaque global estimate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal BigOperators
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D

universe x y z

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}

namespace CanonicalPhysicalScalarCauchyJetGeometricData

/-- Finite componentwise majorization of a realized Euler residual. -/
structure CauchyJetEulerFiniteExpansionData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore)
    (realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod)
    (Index : Type z) [Fintype Index] where
  component : Index → ValueCore × NormalCore →
    CanonicalLatitudeCauchyJetProductParameter → Real
  constant : Index → Real
  constant_nonnegative : ∀ index, 0 ≤ constant index
  residual_sq_integrable : ∀ data : ValueCore × NormalCore,
    Integrable
      (fun parameter => realization.residual data parameter ^ 2)
      (canonicalLatitudeCauchyJetProductMeasure period)
  component_sq_integrable : ∀ index data,
    Integrable
      (fun parameter => component index data parameter ^ 2)
      (canonicalLatitudeCauchyJetProductMeasure period)
  residual_sq_le_sum : ∀ data parameter,
    realization.residual data parameter ^ 2 ≤
      ∑ index, component index data parameter ^ 2
  component_bound_sq : ∀ index data,
    (∫ parameter,
      component index data parameter ^ 2
      ∂canonicalLatitudeCauchyJetProductMeasure period) ≤
        constant index ^ 2 *
          ‖geometric.boundaryCoreEmbedding period hPeriod data‖ ^ 2

namespace CauchyJetEulerFiniteExpansionData

/-- Sum of the squared component constants. -/
def constantSquareSum
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    {Index : Type z} [Fintype Index]
    (expansion : geometric.CauchyJetEulerFiniteExpansionData
      period hPeriod realization Index) : Real :=
  ∑ index, expansion.constant index ^ 2

/-- Nonnegativity of the summed square constant. -/
theorem constantSquareSum_nonnegative
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    {Index : Type z} [Fintype Index]
    (expansion : geometric.CauchyJetEulerFiniteExpansionData
      period hPeriod realization Index) :
    0 ≤ expansion.constantSquareSum :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Combined Euler estimate constant. -/
def combinedConstant
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    {Index : Type z} [Fintype Index]
    (expansion : geometric.CauchyJetEulerFiniteExpansionData
      period hPeriod realization Index) : Real :=
  Real.sqrt expansion.constantSquareSum

/-- Nonnegativity of the combined constant. -/
theorem combinedConstant_nonnegative
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    {Index : Type z} [Fintype Index]
    (expansion : geometric.CauchyJetEulerFiniteExpansionData
      period hPeriod realization Index) :
    0 ≤ expansion.combinedConstant :=
  Real.sqrt_nonneg _

/-- Square of the combined constant. -/
theorem combinedConstant_sq
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    {Index : Type z} [Fintype Index]
    (expansion : geometric.CauchyJetEulerFiniteExpansionData
      period hPeriod realization Index) :
    expansion.combinedConstant ^ 2 = expansion.constantSquareSum := by
  unfold combinedConstant
  rw [Real.sq_sqrt expansion.constantSquareSum_nonnegative]

/-- Integral of the finite component sum. -/
theorem integral_sum_components
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    {Index : Type z} [Fintype Index]
    (expansion : geometric.CauchyJetEulerFiniteExpansionData
      period hPeriod realization Index)
    (data : ValueCore × NormalCore) :
    (∫ parameter,
      ∑ index, expansion.component index data parameter ^ 2
      ∂canonicalLatitudeCauchyJetProductMeasure period) =
      ∑ index,
        ∫ parameter,
          expansion.component index data parameter ^ 2
          ∂canonicalLatitudeCauchyJetProductMeasure period := by
  rw [integral_finset_sum]
  intro index _
  exact expansion.component_sq_integrable index data

/-- The finite component bounds imply the required product Euler estimate. -/
theorem product_bound_sq
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    {Index : Type z} [Fintype Index]
    (expansion : geometric.CauchyJetEulerFiniteExpansionData
      period hPeriod realization Index)
    (data : ValueCore × NormalCore) :
    (∫ parameter,
      realization.residual data parameter ^ 2
      ∂canonicalLatitudeCauchyJetProductMeasure period) ≤
        expansion.combinedConstant ^ 2 *
          ‖geometric.boundaryCoreEmbedding period hPeriod data‖ ^ 2 := by
  have hSumIntegrable : Integrable
      (fun parameter =>
        ∑ index, expansion.component index data parameter ^ 2)
      (canonicalLatitudeCauchyJetProductMeasure period) :=
    integrable_finset_sum _ fun index _ =>
      expansion.component_sq_integrable index data
  calc
    (∫ parameter,
      realization.residual data parameter ^ 2
      ∂canonicalLatitudeCauchyJetProductMeasure period) ≤
        ∫ parameter,
          ∑ index, expansion.component index data parameter ^ 2
          ∂canonicalLatitudeCauchyJetProductMeasure period :=
      integral_mono
        (expansion.residual_sq_integrable data)
        hSumIntegrable
        (expansion.residual_sq_le_sum data)
    _ = ∑ index,
        ∫ parameter,
          expansion.component index data parameter ^ 2
          ∂canonicalLatitudeCauchyJetProductMeasure period :=
      expansion.integral_sum_components period hPeriod data
    _ ≤ ∑ index,
        expansion.constant index ^ 2 *
          ‖geometric.boundaryCoreEmbedding period hPeriod data‖ ^ 2 :=
      Finset.sum_le_sum fun index _ =>
        expansion.component_bound_sq index data
    _ = expansion.constantSquareSum *
        ‖geometric.boundaryCoreEmbedding period hPeriod data‖ ^ 2 := by
      unfold constantSquareSum
      rw [Finset.sum_mul]
    _ = expansion.combinedConstant ^ 2 *
        ‖geometric.boundaryCoreEmbedding period hPeriod data‖ ^ 2 := by
      rw [expansion.combinedConstant_sq period hPeriod]

/-- Conversion to the final product Euler estimate interface. -/
def toEulerProductEstimateData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    {Index : Type z} [Fintype Index]
    (expansion : geometric.CauchyJetEulerFiniteExpansionData
      period hPeriod realization Index) :
    geometric.CauchyJetEulerProductEstimateData
      period hPeriod realization where
  constant := expansion.combinedConstant
  nonnegative := expansion.combinedConstant_nonnegative
  product_bound_sq := expansion.product_bound_sq

/-- Finite-expansion certificate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    {realization : geometric.CauchyJetEulerProductRealizationData
      period hPeriod}
    {Index : Type z} [Fintype Index]
    (expansion : geometric.CauchyJetEulerFiniteExpansionData
      period hPeriod realization Index) :
    (∀ data : ValueCore × NormalCore,
      (∫ parameter,
        realization.residual data parameter ^ 2
        ∂canonicalLatitudeCauchyJetProductMeasure period) ≤
          expansion.combinedConstant ^ 2 *
            ‖geometric.boundaryCoreEmbedding period hPeriod data‖ ^ 2) ∧
      0 ≤ expansion.combinedConstant :=
  ⟨expansion.product_bound_sq,
    expansion.combinedConstant_nonnegative⟩

end CauchyJetEulerFiniteExpansionData

end CanonicalPhysicalScalarCauchyJetGeometricData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
end JanusFormal
