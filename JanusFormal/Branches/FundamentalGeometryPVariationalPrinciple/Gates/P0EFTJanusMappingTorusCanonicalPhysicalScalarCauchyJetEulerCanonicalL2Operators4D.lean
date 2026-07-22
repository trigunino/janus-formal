import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerBoundedCoefficients4D

/-!
# Six canonical `L²` operators for the Cauchy-jet Euler residual

The six tangential coefficients are naturally elements of the completed
boundary `L²` space.  There is no need to supply separate pointwise functions,
`MemLp` proofs, identifications with operator outputs or an integrability proof
for the canonical residual.

For every profile sector, a continuous operator

`Trace × Trace →L L²(boundary)`

already has a canonical measurable representative and a canonical `MemLp`
proof.  Moreover, the canonical product residual is the pullback of the physical
Euler residual, which is in bulk `L²`; exact coarea therefore proves its squared
integrability automatically.

The only remaining coefficient input is:

* six continuous boundary `L²` operators;
* the pointwise expansion of the canonical product residual using their
  canonical representatives.

All coefficient constants, all product integrability statements and the final
Euler graph estimate are then theorems.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerCanonicalL2Operators4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal BigOperators
open MeasureTheory Set Topology Filter Function
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D
open P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetEulerNormalProfiles4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerProductRealization4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerSixCoefficientClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerBoundedCoefficients4D

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

/-- The canonical product Euler residual has an integrable square. -/
theorem canonicalEulerProductResidual_sq_integrable
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore)
    (boundary : ValueCore × NormalCore) :
    Integrable
      (fun parameter =>
        geometric.canonicalEulerProductResidual boundary parameter ^ 2)
      (canonicalLatitudeCauchyJetProductMeasure period) := by
  let globalSquare := fun point =>
    canonicalPhysicalScalarEulerGlobalResidual
      period hPeriod massSquared (geometric.extension boundary) point ^ 2
  have hGlobal : Integrable globalSquare
      (P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D.intrinsicCanonicalLorentzVolumeMeasure
        period hPeriod) :=
    (geometric.operatorData.residual_memLp
      (geometric.extension boundary)).integrable_sq
  have hPullback :=
    (canonicalLatitudeCauchyJetProductPhysicalMap_measurePreserving
      period hPeriod).integrable_comp_of_integrable hGlobal
  simpa [canonicalEulerProductResidual, globalSquare, Function.comp_def] using
    hPullback

/-- Six continuous `L²` coefficient operators and the exact canonical residual
expansion. -/
structure CauchyJetEulerSixCanonicalL2OperatorData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore) where
  coefficientOperator : ProfileIndex →
    CompletedBoundary period →L[Real] BoundaryL2 period
  residual_eq : ∀ boundary parameter,
    geometric.canonicalEulerProductResidual boundary parameter =
      canonicalLatitudeCauchyJetEulerNormalProfile .value parameter.2 *
          ((coefficientOperator .value
            (geometric.boundaryCoreEmbedding boundary) :
              CanonicalLatitudeBase → Real) parameter.1) +
        canonicalLatitudeCauchyJetEulerNormalProfile .normal parameter.2 *
          ((coefficientOperator .normal
            (geometric.boundaryCoreEmbedding boundary) :
              CanonicalLatitudeBase → Real) parameter.1) +
        canonicalLatitudeCauchyJetEulerNormalProfile .valueFirst parameter.2 *
          ((coefficientOperator .valueFirst
            (geometric.boundaryCoreEmbedding boundary) :
              CanonicalLatitudeBase → Real) parameter.1) +
        canonicalLatitudeCauchyJetEulerNormalProfile .normalFirst parameter.2 *
          ((coefficientOperator .normalFirst
            (geometric.boundaryCoreEmbedding boundary) :
              CanonicalLatitudeBase → Real) parameter.1) +
        canonicalLatitudeCauchyJetEulerNormalProfile .valueSecond parameter.2 *
          ((coefficientOperator .valueSecond
            (geometric.boundaryCoreEmbedding boundary) :
              CanonicalLatitudeBase → Real) parameter.1) +
        canonicalLatitudeCauchyJetEulerNormalProfile .normalSecond parameter.2 *
          ((coefficientOperator .normalSecond
            (geometric.boundaryCoreEmbedding boundary) :
              CanonicalLatitudeBase → Real) parameter.1)

namespace CauchyJetEulerSixCanonicalL2OperatorData

/-- Canonical pointwise representative of one coefficient operator output. -/
def coefficient
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    (data : geometric.CauchyJetEulerSixCanonicalL2OperatorData
      period hPeriod)
    (index : ProfileIndex) (boundary : ValueCore × NormalCore) :
    CanonicalLatitudeBase → Real :=
  data.coefficientOperator index
    (geometric.boundaryCoreEmbedding boundary)

/-- Every canonical coefficient representative is automatically in `L²`. -/
theorem coefficient_memLp
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    (data : geometric.CauchyJetEulerSixCanonicalL2OperatorData
      period hPeriod)
    (index : ProfileIndex) (boundary : ValueCore × NormalCore) :
    MemLp (data.coefficient index boundary) (2 : ENNReal)
      (canonicalLatitudeBaseMeasure period) :=
  (data.coefficientOperator index
    (geometric.boundaryCoreEmbedding boundary)).memLp

/-- Repacking the canonical representative into `L²` recovers the operator
output exactly. -/
theorem coefficient_toLp_eq
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    (data : geometric.CauchyJetEulerSixCanonicalL2OperatorData
      period hPeriod)
    (index : ProfileIndex) (boundary : ValueCore × NormalCore) :
    (data.coefficient_memLp index boundary).toLp
        (data.coefficient index boundary) =
      data.coefficientOperator index
        (geometric.boundaryCoreEmbedding boundary) := by
  exact Lp.toLp_coeFn
    (data.coefficientOperator index
      (geometric.boundaryCoreEmbedding boundary))
    (data.coefficient_memLp index boundary)

/-- Conversion to the older bounded-coefficient interface.  All former analytic
fields are filled automatically. -/
def toSixBoundedCoefficientData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    (data : geometric.CauchyJetEulerSixCanonicalL2OperatorData
      period hPeriod) :
    geometric.CauchyJetEulerSixBoundedCoefficientData
      period hPeriod geometric.canonicalEulerProductRealization where
  coefficient := data.coefficient
  coefficient_memLp := data.coefficient_memLp
  coefficientOperator := data.coefficientOperator
  coefficient_toLp_eq := data.coefficient_toLp_eq
  residual_sq_integrable := geometric.canonicalEulerProductResidual_sq_integrable
  residual_eq := by
    intro boundary parameter
    simpa [coefficient] using data.residual_eq boundary parameter

/-- Conversion to the complete six-coefficient estimate package. -/
def toSixCoefficientData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    (data : geometric.CauchyJetEulerSixCanonicalL2OperatorData
      period hPeriod) :=
  data.toSixBoundedCoefficientData.toSixCoefficientData

/-- Final Euler product estimate. -/
def toEulerProductEstimateData
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    (data : geometric.CauchyJetEulerSixCanonicalL2OperatorData
      period hPeriod) :=
  data.toSixBoundedCoefficientData.toEulerProductEstimateData

/-- Operator norms provide the complete canonical Euler graph estimate. -/
theorem certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    {geometric : CanonicalPhysicalScalarCauchyJetGeometricData
      period hPeriod massSquared ValueCore NormalCore}
    (data : geometric.CauchyJetEulerSixCanonicalL2OperatorData
      period hPeriod) :
    (∀ index boundary,
      MemLp (data.coefficient index boundary) (2 : ENNReal)
        (canonicalLatitudeBaseMeasure period)) ∧
      (∀ boundary,
        Integrable
          (fun parameter =>
            geometric.canonicalEulerProductResidual boundary parameter ^ 2)
          (canonicalLatitudeCauchyJetProductMeasure period)) ∧
      (∀ boundary : ValueCore × NormalCore,
        (∫ parameter,
          geometric.canonicalEulerProductResidual boundary parameter ^ 2
          ∂canonicalLatitudeCauchyJetProductMeasure period) ≤
          data.toSixCoefficientData.toSeparatedExpansionData.toFiniteExpansionData.combinedConstant ^ 2 *
            ‖geometric.boundaryCoreEmbedding boundary‖ ^ 2) :=
  ⟨data.coefficient_memLp,
    geometric.canonicalEulerProductResidual_sq_integrable,
    data.toSixBoundedCoefficientData.certificate⟩

end CauchyJetEulerSixCanonicalL2OperatorData

end CanonicalPhysicalScalarCauchyJetGeometricData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerCanonicalL2Operators4D
end JanusFormal
