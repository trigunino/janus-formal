import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalFinalPDEClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerSixCoefficientClosure4D

/-!
# Canonical physical scalar PDE closure from six Euler coefficient bounds

The opaque product estimate in the canonical final PDE package is replaced here
by six tangential coefficient estimates corresponding to

`a`, `b`, `a'`, `b'`, `a''`, `b''`.

The fixed normal profiles and all of their moments are already formalized.  A
six-coefficient expansion therefore produces the complete Euler product bound,
the bounded Cauchy right inverse and the surjective completed physical boundary
triple.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalSixCoefficientPDEClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyJetCompatibilityGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalFinalPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerProductRealization4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEnergyGarding4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarNormalEllipticRegularity4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

private abbrev ValueCore :=
  CanonicalLatitudeSmoothPeriodicValueCore period
private abbrev NormalCore :=
  CanonicalLatitudeSmoothAntiperiodicNormalCore period

/-- Canonical final PDE inputs with the Euler estimate split into six boundary
coefficient bounds. -/
structure CanonicalPhysicalScalarCanonicalSixCoefficientPDEData
    (massSquared : Real) where
  geometric :
    CanonicalPhysicalScalarCanonicalCauchyJetCompatibilityData
      period hPeriod massSquared
  gardingEnergy : (geometric.greenCore period hPeriod).EnergyGardingData period hPeriod
  normalRegularity : (geometric.greenCore period hPeriod).NormalEllipticRegularityData
    period hPeriod (Regularity := Regularity)
  eulerCoefficients :
    ((geometric.toCompatibilityData period hPeriod).toCauchyJetGeometricData
      period hPeriod).CauchyJetEulerSixCoefficientData
      period hPeriod
      (((geometric.toCompatibilityData period hPeriod).toCauchyJetGeometricData
        period hPeriod).canonicalEulerProductRealization period hPeriod)

namespace CanonicalPhysicalScalarCanonicalSixCoefficientPDEData

/-- Conversion to the canonical final PDE package. -/
def toCanonicalFinalPDEData
    (data : CanonicalPhysicalScalarCanonicalSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :
    CanonicalPhysicalScalarCanonicalFinalPDEData
      period hPeriod massSquared (Regularity := Regularity) where
  geometric := data.geometric
  gardingEnergy := data.gardingEnergy
  normalRegularity := data.normalRegularity
  eulerEstimate := data.eulerCoefficients.toEulerProductEstimateData period hPeriod

/-- Correct completed physical boundary triple. -/
def triple
    (data : CanonicalPhysicalScalarCanonicalSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (data.toCanonicalFinalPDEData period hPeriod).triple period hPeriod

/-- Bounded completed Cauchy extension. -/
def completedExtension
    (data : CanonicalPhysicalScalarCanonicalSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (data.toCanonicalFinalPDEData period hPeriod).completedExtension period hPeriod

/-- The six coefficient bounds produce the final product Euler estimate. -/
theorem euler_product_bound
    (data : CanonicalPhysicalScalarCanonicalSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity))
    (boundary : ValueCore period × NormalCore period) :
    (∫ parameter,
      ((((data.geometric.toCompatibilityData period hPeriod).toCauchyJetGeometricData
        period hPeriod).canonicalEulerProductResidual period hPeriod
        boundary parameter) ^ 2)
      ∂P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D.canonicalLatitudeCauchyJetProductMeasure
        period) ≤
      ((data.eulerCoefficients.toSeparatedExpansionData period hPeriod)
        |>.toFiniteExpansionData period hPeriod).combinedConstant ^ 2 *
        ‖((data.geometric.toCompatibilityData period hPeriod).toCauchyJetGeometricData
          period hPeriod).boundaryCoreEmbedding period hPeriod boundary‖ ^ 2 :=
  data.eulerCoefficients.certificate period hPeriod boundary

/-- Canonical six-coefficient PDE certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarCanonicalSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :
    Function.Injective
        (canonicalScalarGreenCoreGraphInclusion
          (data.geometric.greenCore period hPeriod).core) ∧
      Function.Surjective
        (canonicalScalarGreenCoreCompletedBoundaryTrace
          (data.geometric.greenCore period hPeriod).core
          (((data.toCanonicalFinalPDEData period hPeriod).completedInputs
            period hPeriod).traceBound period hPeriod
            (data.geometric.greenCore period hPeriod))) ∧
      (∀ boundary,
        canonicalScalarGreenCoreCompletedBoundaryTrace
            (data.geometric.greenCore period hPeriod).core
            (((data.toCanonicalFinalPDEData period hPeriod).completedInputs
              period hPeriod).traceBound period hPeriod
              (data.geometric.greenCore period hPeriod))
            (data.completedExtension period hPeriod boundary) = boundary) :=
  ⟨((data.toCanonicalFinalPDEData period hPeriod).certificate period hPeriod).2.2.2.1,
    ((data.toCanonicalFinalPDEData period hPeriod).certificate period hPeriod).2.2.2.2.1,
    ((data.toCanonicalFinalPDEData period hPeriod).certificate period hPeriod).2.2.2.2.2⟩

end CanonicalPhysicalScalarCanonicalSixCoefficientPDEData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalSixCoefficientPDEClosure4D
end JanusFormal
