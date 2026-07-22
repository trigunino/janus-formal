import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyClosedVariational4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyReducedGaussian4D

/-!
# Canonical Cauchy-closed Gaussian response

The compact reference resolvent of the canonical periodic/antiperiodic physical
realization is the Gaussian response operator.  Its source pairing is symmetric,
the generating functional is the negative on-shell source action, exact
polarization holds and coercivity makes the response nonnegative.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyClosedGaussian4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyClosedAnalytic4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyClosedVariational4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyReducedGaussian4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

namespace CanonicalPhysicalScalarCanonicalCauchyClosedAnalyticData

/-- Canonical Gaussian source pairing. -/
def gaussianPairing
    (analytic : CanonicalPhysicalScalarCanonicalCauchyClosedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (first second :
      P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
        period hPeriod) : Real :=
  (analytic.toCauchyClosedAnalyticData.toFullyReducedAnalyticData
    period hPeriod).gaussianPairing period hPeriod first second

/-- Canonical Gaussian generating functional. -/
def gaussianGeneratingFunctional
    (analytic : CanonicalPhysicalScalarCanonicalCauchyClosedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (source :
      P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
        period hPeriod) : Real :=
  (analytic.toCauchyClosedAnalyticData.toFullyReducedAnalyticData
    period hPeriod).gaussianGeneratingFunctional period hPeriod source

/-- Symmetry of the canonical Gaussian pairing. -/
theorem gaussianPairing_comm
    (analytic : CanonicalPhysicalScalarCanonicalCauchyClosedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (first second :
      P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
        period hPeriod) :
    analytic.gaussianPairing period hPeriod first second =
      analytic.gaussianPairing period hPeriod second first :=
  (analytic.toCauchyClosedAnalyticData.toFullyReducedAnalyticData
    period hPeriod).gaussianPairing_comm period hPeriod first second

/-- Generating functional equals minus the on-shell source action. -/
theorem gaussianGeneratingFunctional_eq_neg_onShell
    (analytic : CanonicalPhysicalScalarCanonicalCauchyClosedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (source :
      P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
        period hPeriod) :
    analytic.gaussianGeneratingFunctional period hPeriod source =
      -analytic.boundary.triple.lagrangianSourceAction
        analytic.condition analytic.referenceParameter source
        (analytic.sourceSolution period hPeriod source) :=
  (analytic.toCauchyClosedAnalyticData.toFullyReducedAnalyticData
    period hPeriod).gaussianGeneratingFunctional_eq_neg_onShell
      period hPeriod source

/-- Exact Gaussian polarization. -/
theorem gaussianGeneratingFunctional_add
    (analytic : CanonicalPhysicalScalarCanonicalCauchyClosedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (first second :
      P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
        period hPeriod) :
    analytic.gaussianGeneratingFunctional period hPeriod (first + second) =
      analytic.gaussianGeneratingFunctional period hPeriod first +
        analytic.gaussianGeneratingFunctional period hPeriod second +
        analytic.gaussianPairing period hPeriod first second :=
  (analytic.toCauchyClosedAnalyticData.toFullyReducedAnalyticData
    period hPeriod).gaussianGeneratingFunctional_add
      period hPeriod first second

/-- Nonnegativity of the canonical Gaussian response. -/
theorem gaussianGeneratingFunctional_nonnegative
    (analytic : CanonicalPhysicalScalarCanonicalCauchyClosedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (source :
      P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
        period hPeriod) :
    0 ≤ analytic.gaussianGeneratingFunctional period hPeriod source :=
  (analytic.toCauchyClosedAnalyticData.toFullyReducedAnalyticData
    period hPeriod).gaussianGeneratingFunctional_nonnegative
      period hPeriod source

/-- Canonical Gaussian certificate. -/
theorem certificate
    (analytic : CanonicalPhysicalScalarCanonicalCauchyClosedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (source :
      P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
        period hPeriod) :
    analytic.gaussianGeneratingFunctional period hPeriod source =
        -analytic.boundary.triple.lagrangianSourceAction
          analytic.condition analytic.referenceParameter source
          (analytic.sourceSolution period hPeriod source) ∧
      0 ≤ analytic.gaussianGeneratingFunctional period hPeriod source :=
  ⟨analytic.gaussianGeneratingFunctional_eq_neg_onShell
      period hPeriod source,
    analytic.gaussianGeneratingFunctional_nonnegative
      period hPeriod source⟩

end CanonicalPhysicalScalarCanonicalCauchyClosedAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyClosedGaussian4D
end JanusFormal
