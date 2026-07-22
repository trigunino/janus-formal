import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedAnalyticClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleVariational4D

/-!
# Variational principle at the resolvent-reduced physical endpoint

The preferred analytic package contains no adjoint regularity field.  A positive
shifted-form decomposition and domain density produce the bounded source
resolvent directly.  The generic completed-boundary variational theory then
provides the strong equation, stationarity, first variation and the unique global
minimizer.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedVariational4D
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedVariational4D

namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedAnalyticClosure4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleVariational4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

private abbrev BulkL2 :=
  P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
    period hPeriod

namespace CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData

/-- Classical source solution at the positive reference shift. -/
noncomputable def sourceSolution
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity)) :
    BulkL2 period hPeriod →L[Real]
      analytic.boundary.triple.lagrangianDomainSubmodule analytic.condition :=
  (analytic.boundedResolvent period hPeriod).resolvent

/-- Strong shifted source equation. -/
theorem sourceSolution_equation
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (source : BulkL2 period hPeriod) :
    analytic.boundary.triple.lagrangianShiftedOperator
        analytic.condition analytic.referenceParameter
        (analytic.sourceSolution period hPeriod source) = source :=
  (analytic.boundedResolvent period hPeriod).left_inverse source

/-- Weak stationarity of the classical source solution. -/
theorem sourceSolution_stationary
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (source : BulkL2 period hPeriod) :
    analytic.boundary.triple.lagrangianSourceStationary
      analytic.condition analytic.referenceParameter source
      (analytic.sourceSolution period hPeriod source) :=
  analytic.boundary.triple.lagrangianSourceStationary_of_equation
    analytic.condition analytic.referenceParameter source _
    (analytic.sourceSolution_equation period hPeriod source)

/-- Weak stationarity is equivalent to the strong source equation. -/
theorem sourceStationary_iff_equation
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (source : BulkL2 period hPeriod)
    (field : analytic.boundary.triple.lagrangianDomainSubmodule
      analytic.condition) :
    analytic.boundary.triple.lagrangianSourceStationary
        analytic.condition analytic.referenceParameter source field ↔
      analytic.boundary.triple.lagrangianShiftedOperator
        analytic.condition analytic.referenceParameter field = source :=
  analytic.boundary.triple.lagrangianSourceStationary_iff_equation
    analytic.condition analytic.referenceParameter source field
    (analytic.denseDomain period hPeriod)

/-- Exact action difference from the classical solution. -/
theorem sourceAction_sub_solution
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (source : BulkL2 period hPeriod)
    (field : analytic.boundary.triple.lagrangianDomainSubmodule
      analytic.condition) :
    analytic.boundary.triple.lagrangianSourceAction
          analytic.condition analytic.referenceParameter source field -
        analytic.boundary.triple.lagrangianSourceAction
          analytic.condition analytic.referenceParameter source
          (analytic.sourceSolution period hPeriod source) =
      analytic.boundary.triple.lagrangianShiftedQuadraticFunctional
        analytic.condition analytic.referenceParameter
        (field - analytic.sourceSolution period hPeriod source) :=
  analytic.boundary.triple.lagrangianSourceAction_sub_solution
    analytic.condition analytic.referenceParameter source
    (analytic.sourceSolution period hPeriod source) field
    (analytic.sourceSolution_equation period hPeriod source)

/-- Unique global minimizer supplied by positive shifted coercivity. -/
theorem sourceSolution_unique_minimizer
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (source : BulkL2 period hPeriod) :
    (∀ field : analytic.boundary.triple.lagrangianDomainSubmodule
        analytic.condition,
      analytic.boundary.triple.lagrangianSourceAction
          analytic.condition analytic.referenceParameter source
          (analytic.sourceSolution period hPeriod source) ≤
        analytic.boundary.triple.lagrangianSourceAction
          analytic.condition analytic.referenceParameter source field) ∧
      (∀ field : analytic.boundary.triple.lagrangianDomainSubmodule
          analytic.condition,
        analytic.boundary.triple.lagrangianSourceAction
            analytic.condition analytic.referenceParameter source field =
          analytic.boundary.triple.lagrangianSourceAction
            analytic.condition analytic.referenceParameter source
            (analytic.sourceSolution period hPeriod source) →
        field = analytic.sourceSolution period hPeriod source) :=
  (analytic.shiftedFormCoercive period hPeriod).unique_minimizer
    analytic.boundary.triple analytic.condition analytic.referenceParameter
    (analytic.denseDomain period hPeriod) source

/-- First variation of the final source action. -/
theorem sourceAction_hasDerivAt
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (source : BulkL2 period hPeriod)
    (field variation : analytic.boundary.triple.lagrangianDomainSubmodule
      analytic.condition) :
    @HasDerivAt Real _ Real
      Real.normedAddCommGroup.toAddCommGroup
      RCLike.toInnerProductSpaceReal.toModule _ _
      (fun parameter : Real =>
        analytic.boundary.triple.lagrangianSourceAction
          analytic.condition analytic.referenceParameter source
          (field + parameter • variation))
      (inner Real
        (analytic.boundary.triple.lagrangianShiftedOperator
            analytic.condition analytic.referenceParameter field - source)
        (analytic.boundary.triple.lagrangianInclusion
          analytic.condition variation)) 0 :=
  analytic.boundary.triple.lagrangianSourceAction_hasDerivAt
    analytic.condition analytic.referenceParameter source field variation

/-- Resolvent-reduced physical variational certificate. -/
theorem variational_certificate
    (analytic : CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData
      period hPeriod massSquared (Regularity := Regularity))
    (source : BulkL2 period hPeriod) :
    analytic.boundary.triple.lagrangianShiftedOperator
        analytic.condition analytic.referenceParameter
        (analytic.sourceSolution period hPeriod source) = source ∧
      analytic.boundary.triple.lagrangianSourceStationary
        analytic.condition analytic.referenceParameter source
        (analytic.sourceSolution period hPeriod source) ∧
      (∀ field : analytic.boundary.triple.lagrangianDomainSubmodule
          analytic.condition,
        analytic.boundary.triple.lagrangianSourceAction
            analytic.condition analytic.referenceParameter source
            (analytic.sourceSolution period hPeriod source) ≤
          analytic.boundary.triple.lagrangianSourceAction
            analytic.condition analytic.referenceParameter source field) ∧
      (∀ field : analytic.boundary.triple.lagrangianDomainSubmodule
          analytic.condition,
        analytic.boundary.triple.lagrangianSourceAction
            analytic.condition analytic.referenceParameter source field =
          analytic.boundary.triple.lagrangianSourceAction
            analytic.condition analytic.referenceParameter source
            (analytic.sourceSolution period hPeriod source) →
        field = analytic.sourceSolution period hPeriod source) :=
  ⟨analytic.sourceSolution_equation period hPeriod source,
    analytic.sourceSolution_stationary period hPeriod source,
    (analytic.sourceSolution_unique_minimizer period hPeriod source).1,
    (analytic.sourceSolution_unique_minimizer period hPeriod source).2⟩

end CanonicalPhysicalScalarCanonicalResolventReducedAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedAnalyticClosure4D
end JanusFormal
