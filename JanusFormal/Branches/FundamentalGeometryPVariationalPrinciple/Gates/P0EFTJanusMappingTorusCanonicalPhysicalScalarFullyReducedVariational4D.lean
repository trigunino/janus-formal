import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyReducedAnalyticClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleVariational4D

/-!
# Fully reduced physical scalar variational principle

For the fully reduced physical scalar realization, the coercive reference form
constructs a bounded source solution by Lax--Milgram.  That solution is exactly
the stationary point and the unique global minimizer of the direct source
action.  The first variation and weak/strong equivalence are inherited directly
from the completed physical boundary triple.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyReducedVariational4D
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyReducedVariational4D

namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyReducedAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyReducedAnalyticClosure4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleResolvent4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleVariational4D

universe x y r

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

namespace CanonicalPhysicalScalarFullyReducedAnalyticData

/-- Bounded physical source solution at the coercive reference parameter. -/
noncomputable def sourceSolution
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarFullyReducedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity)) :
    P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
        period hPeriod →L[Real]
      analytic.boundary.triple.lagrangianDomainSubmodule analytic.condition :=
  analytic.shiftedFormCoercive.boundedResolvent
    analytic.boundary.triple analytic.condition analytic.referenceParameter
    ((analytic.toEllipticAnalyticData period hPeriod)
      |>.toSequentialAnalyticData period hPeriod
      |>.toConstructiveAnalyticData period hPeriod
      |>.shiftedFormData period hPeriod
      |>.denseDomain period hPeriod)
    |>.resolvent

/-- The physical source solution solves the strong shifted equation. -/
theorem sourceSolution_equation
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarFullyReducedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity))
    (source :
      P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
        period hPeriod) :
    analytic.boundary.triple.lagrangianShiftedOperator
        analytic.condition analytic.referenceParameter
        (analytic.sourceSolution period hPeriod source) = source := by
  unfold sourceSolution
  exact (analytic.shiftedFormCoercive.boundedResolvent
    analytic.boundary.triple analytic.condition analytic.referenceParameter
    ((analytic.toEllipticAnalyticData period hPeriod)
      |>.toSequentialAnalyticData period hPeriod
      |>.toConstructiveAnalyticData period hPeriod
      |>.shiftedFormData period hPeriod
      |>.denseDomain period hPeriod)).left_inverse source

/-- The physical source solution is weakly stationary. -/
theorem sourceSolution_stationary
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarFullyReducedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity))
    (source :
      P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
        period hPeriod) :
    analytic.boundary.triple.lagrangianSourceStationary
      analytic.condition analytic.referenceParameter source
      (analytic.sourceSolution period hPeriod source) :=
  analytic.boundary.triple.lagrangianSourceStationary_of_equation
    analytic.condition analytic.referenceParameter source _
    (analytic.sourceSolution_equation period hPeriod source)

/-- The physical source solution is the unique global action minimizer. -/
theorem sourceSolution_unique_minimizer
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarFullyReducedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity))
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
  analytic.shiftedFormCoercive.unique_minimizer
    analytic.boundary.triple analytic.condition analytic.referenceParameter
    ((analytic.toEllipticAnalyticData period hPeriod)
      |>.toSequentialAnalyticData period hPeriod
      |>.toConstructiveAnalyticData period hPeriod
      |>.shiftedFormData period hPeriod
      |>.denseDomain period hPeriod)
    source

/-- First variation of the fully reduced physical source action. -/
theorem sourceAction_hasDerivAt
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarFullyReducedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity))
    (source :
      P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
        period hPeriod)
    (field variation :
      analytic.boundary.triple.lagrangianDomainSubmodule analytic.condition) :
    HasDerivAt
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

/-- Fully reduced physical variational certificate. -/
theorem variational_certificate
    {ValueCore : Type x} {NormalCore : Type y}
    [AddCommGroup ValueCore] [Module Real ValueCore]
    [AddCommGroup NormalCore] [Module Real NormalCore]
    (analytic : CanonicalPhysicalScalarFullyReducedAnalyticData
      period hPeriod massSquared ValueCore NormalCore
      (Regularity := Regularity))
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

end CanonicalPhysicalScalarFullyReducedAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarFullyReducedAnalyticClosure4D
end JanusFormal
