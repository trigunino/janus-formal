import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarAutomaticGardingEnergy4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalSixCoefficientPDEClosure4D

/-!
# Canonical physical scalar PDE closure from minimal energy and Euler data

The first elementary inequality in the physical Gårding argument is now a theorem
of the first-jet graph construction.  The Euler residual of the explicit Cauchy
lift is reduced to six tangential boundary coefficients.

Consequently the canonical completed physical boundary triple can be assembled
from only three analytic blocks beyond the geometric Green core:

* one estimate of the explicit first-jet component energy by the Euler pairing;
* one higher-regularity estimate carrying a bounded normal trace;
* six boundary `L²` estimates for the coefficients multiplying
  `a`, `b`, `a'`, `b'`, `a''`, and `b''`.

All other Gårding, graph-extension, minimal-core-density and completed-trace
surjectivity statements are derived.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalAutomaticSixCoefficientPDEClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalLatitudeSmoothBoundaryCores4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyJetCompatibilityGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarAutomaticGardingEnergy4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarNormalEllipticRegularity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalSixCoefficientPDEClosure4D
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

/-- Minimal canonical PDE data after making the first Gårding inequality and the
fixed normal profiles automatic. -/
structure CanonicalPhysicalScalarCanonicalAutomaticSixCoefficientPDEData
    (massSquared : Real) where
  geometric :
    CanonicalPhysicalScalarCanonicalCauchyJetCompatibilityData
      period hPeriod massSquared
  energy : (geometric.greenCore period hPeriod).AutomaticEnergyGardingData period hPeriod
  normalRegularity : (geometric.greenCore period hPeriod).NormalEllipticRegularityData
    period hPeriod (Regularity := Regularity)
  eulerCoefficients :
    ((geometric.toCompatibilityData period hPeriod).toCauchyJetGeometricData
      period hPeriod).CauchyJetEulerSixCoefficientData
      period hPeriod
      (((geometric.toCompatibilityData period hPeriod).toCauchyJetGeometricData
        period hPeriod).canonicalEulerProductRealization period hPeriod)

namespace CanonicalPhysicalScalarCanonicalAutomaticSixCoefficientPDEData

/-- Conversion to the six-coefficient PDE package. -/
def toSixCoefficientPDEData
    (data : CanonicalPhysicalScalarCanonicalAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :
    CanonicalPhysicalScalarCanonicalSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity) where
  geometric := data.geometric
  gardingEnergy := data.energy.toEnergyGardingData period hPeriod
    (data.geometric.greenCore period hPeriod)
  normalRegularity := data.normalRegularity
  eulerCoefficients := data.eulerCoefficients

/-- Conversion to the canonical final PDE package. -/
def toCanonicalFinalPDEData
    (data : CanonicalPhysicalScalarCanonicalAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (data.toSixCoefficientPDEData period hPeriod).toCanonicalFinalPDEData period hPeriod

/-- Correct completed physical boundary triple. -/
def triple
    (data : CanonicalPhysicalScalarCanonicalAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (data.toSixCoefficientPDEData period hPeriod).triple period hPeriod

/-- Completed physical boundary inputs. -/
def completedInputs
    (data : CanonicalPhysicalScalarCanonicalAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (data.toCanonicalFinalPDEData period hPeriod).completedInputs period hPeriod

/-- Bounded right inverse of the completed Cauchy trace. -/
def completedExtension
    (data : CanonicalPhysicalScalarCanonicalAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (data.toSixCoefficientPDEData period hPeriod).completedExtension period hPeriod

/-- Physical graph-elliptic estimate derived from the single component-energy
pairing estimate. -/
def graphEllipticEstimate
    (data : CanonicalPhysicalScalarCanonicalAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :=
  data.energy.toGraphEllipticEstimate period hPeriod
    (data.geometric.greenCore period hPeriod)

/-- The six tangential coefficient bounds imply the complete Euler estimate for
the explicit Cauchy extension. -/
theorem euler_product_bound
    (data : CanonicalPhysicalScalarCanonicalAutomaticSixCoefficientPDEData
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

/-- Minimal canonical PDE certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarCanonicalAutomaticSixCoefficientPDEData
      period hPeriod massSquared (Regularity := Regularity)) :
    (∀ field : P0EFTJanusMappingTorusSmoothFieldDescent4D.SmoothQuotientField
        period hPeriod Real,
      ‖P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D.smoothToCanonicalPhysicalScalarH1
          period hPeriod field‖ ^ 2 ≤
        canonicalPhysicalScalarFirstJetComponentEnergy period hPeriod field) ∧
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
  ⟨smoothToCanonicalPhysicalScalarH1_norm_sq_le_componentEnergy
      period hPeriod,
    ((data.toSixCoefficientPDEData period hPeriod).certificate period hPeriod).1,
    ((data.toSixCoefficientPDEData period hPeriod).certificate period hPeriod).2.1,
    ((data.toSixCoefficientPDEData period hPeriod).certificate period hPeriod).2.2⟩

end CanonicalPhysicalScalarCanonicalAutomaticSixCoefficientPDEData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalAutomaticSixCoefficientPDEClosure4D
end JanusFormal
