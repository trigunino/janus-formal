import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyJetCompatibilityGreenCore4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetFinalPDEClosure4D

/-!
# Canonical final PDE closure without a tubular regularity input

The explicit normalized-tail inverse is now a theorem and the value/normal
boundary cores are the canonical smooth periodic and antiperiodic cores.  The
final PDE interface can therefore be specialized without a tubular-coordinate
field.

Its remaining inputs are:

* Euler overlap compatibility and the global Euler-divergence identity;
* density of the two canonical smooth boundary cores;
* the physical Gårding energy estimate;
* higher normal elliptic regularity;
* the product `L²` estimate for the Euler residual of the explicit Cauchy jet.

All smooth extension, minimal-core density, graph injectivity and completed
trace surjectivity conclusions are inherited from the general final PDE closure.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalFinalPDEClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyJetCompatibilityGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetCompatibilityBridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerProductRealization4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEnergyGarding4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarNormalEllipticRegularity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetFinalPDEClosure4D
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

/-- Canonical final PDE inputs with the tubular inverse already discharged. -/
structure CanonicalPhysicalScalarCanonicalFinalPDEData
    (massSquared : Real) where
  geometric :
    CanonicalPhysicalScalarCanonicalCauchyJetCompatibilityData
      period hPeriod massSquared
  gardingEnergy : (geometric.greenCore period hPeriod).EnergyGardingData period hPeriod
  normalRegularity : (geometric.greenCore period hPeriod).NormalEllipticRegularityData
    period hPeriod (Regularity := Regularity)
  eulerEstimate :
    ((geometric.toCompatibilityData period hPeriod).toCauchyJetGeometricData
      period hPeriod).CauchyJetEulerProductEstimateData
      period hPeriod
      (((geometric.toCompatibilityData period hPeriod).toCauchyJetGeometricData
        period hPeriod).canonicalEulerProductRealization period hPeriod)

namespace CanonicalPhysicalScalarCanonicalFinalPDEData

/-- Conversion to the general final PDE package. -/
def toFinalPDEData
    (data : CanonicalPhysicalScalarCanonicalFinalPDEData
      period hPeriod massSquared (Regularity := Regularity)) :
    CanonicalPhysicalScalarCauchyJetFinalPDEData
      period hPeriod massSquared (ValueCore period) (NormalCore period)
      (Regularity := Regularity) where
  geometric := data.geometric.toCompatibilityData period hPeriod
  gardingEnergy := data.gardingEnergy
  normalRegularity := data.normalRegularity
  eulerEstimate := data.eulerEstimate

/-- Correct completed physical boundary triple. -/
def triple
    (data : CanonicalPhysicalScalarCanonicalFinalPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (data.toFinalPDEData period hPeriod).triple period hPeriod

/-- Completed physical boundary inputs. -/
def completedInputs
    (data : CanonicalPhysicalScalarCanonicalFinalPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (data.toFinalPDEData period hPeriod).completedInputs period hPeriod

/-- Bounded right inverse of the completed Cauchy trace. -/
def completedExtension
    (data : CanonicalPhysicalScalarCanonicalFinalPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (data.toFinalPDEData period hPeriod).completedExtension period hPeriod

/-- Canonical product Euler estimate in its final form. -/
theorem euler_product_bound
    (data : CanonicalPhysicalScalarCanonicalFinalPDEData
      period hPeriod massSquared (Regularity := Regularity))
    (boundary : ValueCore period × NormalCore period) :
    (∫ parameter,
      ((((data.geometric.toCompatibilityData period hPeriod).toCauchyJetGeometricData
        period hPeriod).canonicalEulerProductResidual period hPeriod
        boundary parameter) ^ 2)
      ∂P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D.canonicalLatitudeCauchyJetProductMeasure
        period) ≤
      data.eulerEstimate.constant ^ 2 *
        ‖((data.geometric.toCompatibilityData period hPeriod).toCauchyJetGeometricData
          period hPeriod).boundaryCoreEmbedding period hPeriod boundary‖ ^ 2 :=
  data.eulerEstimate.product_bound_sq boundary

/-- Canonical final PDE certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarCanonicalFinalPDEData
      period hPeriod massSquared (Regularity := Regularity)) :
    DenseRange (canonicalLatitudeSmoothPeriodicValueEmbedding period) ∧
      DenseRange
        (canonicalLatitudeSmoothAntiperiodicNormalEmbedding period) ∧
      (data.geometric.greenCore period hPeriod).MinimalCoreDense period hPeriod ∧
      Function.Injective
        (canonicalScalarGreenCoreGraphInclusion
          (data.geometric.greenCore period hPeriod).core) ∧
      Function.Surjective
        (canonicalScalarGreenCoreCompletedBoundaryTrace
          (data.geometric.greenCore period hPeriod).core
          ((data.completedInputs period hPeriod).traceBound period hPeriod
            (data.geometric.greenCore period hPeriod))) ∧
      (∀ boundary,
        canonicalScalarGreenCoreCompletedBoundaryTrace
            (data.geometric.greenCore period hPeriod).core
            ((data.completedInputs period hPeriod).traceBound period hPeriod
              (data.geometric.greenCore period hPeriod))
            (data.completedExtension period hPeriod boundary) = boundary) :=
  ⟨data.geometric.boundaryDensity.valueDense,
    data.geometric.boundaryDensity.normalDense,
    ((data.toFinalPDEData period hPeriod).certificate period hPeriod).1,
    ((data.toFinalPDEData period hPeriod).certificate period hPeriod).2.1,
    ((data.toFinalPDEData period hPeriod).certificate period hPeriod).2.2.1,
    ((data.toFinalPDEData period hPeriod).certificate period hPeriod).2.2.2⟩

end CanonicalPhysicalScalarCanonicalFinalPDEData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalFinalPDEClosure4D
end JanusFormal
