import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyClosedAnalytic4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyReducedVariational4D

/-!
# Canonical Cauchy-closed variational principle

For the canonical periodic/antiperiodic boundary cores, the coercive reference
form constructs the physical source solution.  The direct completed-boundary
variational theorem identifies this solution with the stationary point and the
unique global minimizer of the shifted source action.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyClosedVariational4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyClosedAnalytic4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyReducedVariational4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleVariational4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

namespace CanonicalPhysicalScalarCanonicalCauchyClosedAnalyticData

/-- Canonical physical source solution at the coercive reference parameter. -/
noncomputable def sourceSolution
    (analytic : CanonicalPhysicalScalarCanonicalCauchyClosedAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :=
  (analytic.toCauchyClosedAnalyticData.toFullyReducedAnalyticData
    period hPeriod).sourceSolution period hPeriod

/-- Strong shifted source equation. -/
theorem sourceSolution_equation
    (analytic : CanonicalPhysicalScalarCanonicalCauchyClosedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (source :
      P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
        period hPeriod) :
    analytic.boundary.triple.lagrangianShiftedOperator
        analytic.condition analytic.referenceParameter
        (analytic.sourceSolution period hPeriod source) = source :=
  (analytic.toCauchyClosedAnalyticData.toFullyReducedAnalyticData
    period hPeriod).sourceSolution_equation period hPeriod source

/-- Weak stationarity of the canonical source solution. -/
theorem sourceSolution_stationary
    (analytic : CanonicalPhysicalScalarCanonicalCauchyClosedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (source :
      P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
        period hPeriod) :
    analytic.boundary.triple.lagrangianSourceStationary
      analytic.condition analytic.referenceParameter source
      (analytic.sourceSolution period hPeriod source) :=
  (analytic.toCauchyClosedAnalyticData.toFullyReducedAnalyticData
    period hPeriod).sourceSolution_stationary period hPeriod source

/-- The canonical source solution is the unique global minimizer. -/
theorem sourceSolution_unique_minimizer
    (analytic : CanonicalPhysicalScalarCanonicalCauchyClosedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (source :
      P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
        period hPeriod) :
    (∀ field : analytic.boundary.triple.lagrangianDomainSubmodule analytic.condition,
      analytic.boundary.triple.lagrangianSourceAction
          analytic.condition analytic.referenceParameter source
          (analytic.sourceSolution period hPeriod source) ≤
        analytic.boundary.triple.lagrangianSourceAction
          analytic.condition analytic.referenceParameter source field) ∧
      (∀ field : analytic.boundary.triple.lagrangianDomainSubmodule analytic.condition,
        analytic.boundary.triple.lagrangianSourceAction
            analytic.condition analytic.referenceParameter source field =
          analytic.boundary.triple.lagrangianSourceAction
            analytic.condition analytic.referenceParameter source
            (analytic.sourceSolution period hPeriod source) →
        field = analytic.sourceSolution period hPeriod source) :=
  (analytic.toCauchyClosedAnalyticData.toFullyReducedAnalyticData
    period hPeriod).sourceSolution_unique_minimizer period hPeriod source

/-- Canonical variational certificate. -/
theorem certificate
    (analytic : CanonicalPhysicalScalarCanonicalCauchyClosedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (source :
      P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
        period hPeriod) :
    analytic.boundary.triple.lagrangianShiftedOperator
        analytic.condition analytic.referenceParameter
        (analytic.sourceSolution period hPeriod source) = source ∧
      analytic.boundary.triple.lagrangianSourceStationary
        analytic.condition analytic.referenceParameter source
        (analytic.sourceSolution period hPeriod source) ∧
      (∀ field : analytic.boundary.triple.lagrangianDomainSubmodule analytic.condition,
        analytic.boundary.triple.lagrangianSourceAction
            analytic.condition analytic.referenceParameter source
            (analytic.sourceSolution period hPeriod source) ≤
          analytic.boundary.triple.lagrangianSourceAction
            analytic.condition analytic.referenceParameter source field) :=
  ⟨analytic.sourceSolution_equation period hPeriod source,
    analytic.sourceSolution_stationary period hPeriod source,
    (analytic.sourceSolution_unique_minimizer period hPeriod source).1⟩

end CanonicalPhysicalScalarCanonicalCauchyClosedAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalCauchyClosedVariational4D
end JanusFormal
