import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalStandardBoundaryResolventClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedVariational4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedGaussian4D

/-!
# Standard-boundary scalar Program P endpoints

This file carries the final Dirichlet, Neumann and constant Robin realizations to
the complete Program P output.  For every separated package it exports:

* the bounded classical source solution;
* the strong shifted equation and weak stationarity;
* the unique global minimizer of the source action;
* the symmetric nonnegative Gaussian response;
* self-adjointness, compact resolvent and the Fredholm alternative.

The only boundary-family-specific analytic input is the positive shifted-form
decomposition for the selected separated domain.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalStandardBoundaryProgramPClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalStandardBoundaryResolventClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedVariational4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalResolventReducedGaussian4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

universe r

variable (period : Real) (hPeriod : period ≠ 0)
variable {Regularity : Type r}
  [NormedAddCommGroup Regularity] [NormedSpace Real Regularity]
  [CompleteSpace Regularity]

private abbrev BulkL2 :=
  P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
    period hPeriod

namespace CanonicalPhysicalScalarCanonicalSeparatedResolventData

/-- Classical source solution for a separated realization. -/
noncomputable def sourceSolution
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarCanonicalSeparatedResolventData
      period hPeriod massSquared a b hNondegenerate
      (Regularity := Regularity)) :
    BulkL2 period hPeriod →L[Real]
      data.boundary.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate) :=
  (data.toResolventReducedAnalyticData period hPeriod)
    |>.sourceSolution period hPeriod

/-- Strong shifted source equation. -/
theorem sourceSolution_equation
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarCanonicalSeparatedResolventData
      period hPeriod massSquared a b hNondegenerate
      (Regularity := Regularity))
    (source : BulkL2 period hPeriod) :
    data.boundary.triple.lagrangianShiftedOperator
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate)
        data.referenceParameter
        (data.sourceSolution period hPeriod source) = source :=
  (data.toResolventReducedAnalyticData period hPeriod)
    |>.sourceSolution_equation period hPeriod source

/-- Weak stationarity of the separated source solution. -/
theorem sourceSolution_stationary
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarCanonicalSeparatedResolventData
      period hPeriod massSquared a b hNondegenerate
      (Regularity := Regularity))
    (source : BulkL2 period hPeriod) :
    data.boundary.triple.lagrangianSourceStationary
      (canonicalPhysicalScalarSeparatedCondition
        period a b hNondegenerate)
      data.referenceParameter source
      (data.sourceSolution period hPeriod source) :=
  (data.toResolventReducedAnalyticData period hPeriod)
    |>.sourceSolution_stationary period hPeriod source

/-- Unique global minimizer for the separated source action. -/
theorem sourceSolution_unique_minimizer
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarCanonicalSeparatedResolventData
      period hPeriod massSquared a b hNondegenerate
      (Regularity := Regularity))
    (source : BulkL2 period hPeriod) :
    (∀ field : data.boundary.triple.lagrangianDomainSubmodule
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate),
      data.boundary.triple.lagrangianSourceAction
          (canonicalPhysicalScalarSeparatedCondition
            period a b hNondegenerate)
          data.referenceParameter source
          (data.sourceSolution period hPeriod source) ≤
        data.boundary.triple.lagrangianSourceAction
          (canonicalPhysicalScalarSeparatedCondition
            period a b hNondegenerate)
          data.referenceParameter source field) ∧
      (∀ field : data.boundary.triple.lagrangianDomainSubmodule
          (canonicalPhysicalScalarSeparatedCondition
            period a b hNondegenerate),
        data.boundary.triple.lagrangianSourceAction
            (canonicalPhysicalScalarSeparatedCondition
              period a b hNondegenerate)
            data.referenceParameter source field =
          data.boundary.triple.lagrangianSourceAction
            (canonicalPhysicalScalarSeparatedCondition
              period a b hNondegenerate)
            data.referenceParameter source
            (data.sourceSolution period hPeriod source) →
        field = data.sourceSolution period hPeriod source) :=
  (data.toResolventReducedAnalyticData period hPeriod)
    |>.sourceSolution_unique_minimizer period hPeriod source

/-- Symmetric Gaussian response pairing. -/
def gaussianPairing
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarCanonicalSeparatedResolventData
      period hPeriod massSquared a b hNondegenerate
      (Regularity := Regularity))
    (first second : BulkL2 period hPeriod) : Real :=
  (data.toResolventReducedAnalyticData period hPeriod)
    |>.gaussianPairing period hPeriod first second

/-- Gaussian generating functional. -/
def gaussianGeneratingFunctional
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarCanonicalSeparatedResolventData
      period hPeriod massSquared a b hNondegenerate
      (Regularity := Regularity))
    (source : BulkL2 period hPeriod) : Real :=
  (data.toResolventReducedAnalyticData period hPeriod)
    |>.gaussianGeneratingFunctional period hPeriod source

/-- The Gaussian functional is minus the on-shell action and is nonnegative. -/
theorem gaussian_certificate
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarCanonicalSeparatedResolventData
      period hPeriod massSquared a b hNondegenerate
      (Regularity := Regularity))
    (source : BulkL2 period hPeriod) :
    data.gaussianGeneratingFunctional period hPeriod source =
        -data.boundary.triple.lagrangianSourceAction
          (canonicalPhysicalScalarSeparatedCondition
            period a b hNondegenerate)
          data.referenceParameter source
          (data.sourceSolution period hPeriod source) ∧
      0 ≤ data.gaussianGeneratingFunctional period hPeriod source :=
  (data.toResolventReducedAnalyticData period hPeriod)
    |>.gaussian_certificate period hPeriod source

/-- Complete separated Program P certificate. -/
theorem finalProgramP_certificate
    {a b : Real} {hNondegenerate : a ≠ 0 ∨ b ≠ 0}
    (data : CanonicalPhysicalScalarCanonicalSeparatedResolventData
      period hPeriod massSquared a b hNondegenerate
      (Regularity := Regularity))
    (source : BulkL2 period hPeriod) :
    data.boundary.triple.actualAdjointDomain
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate) =
      data.boundary.triple.realizationDomain
        (canonicalPhysicalScalarSeparatedCondition
          period a b hNondegenerate) ∧
      data.boundary.triple.lagrangianShiftedOperator
          (canonicalPhysicalScalarSeparatedCondition
            period a b hNondegenerate)
          data.referenceParameter
          (data.sourceSolution period hPeriod source) = source ∧
      data.boundary.triple.lagrangianSourceStationary
          (canonicalPhysicalScalarSeparatedCondition
            period a b hNondegenerate)
          data.referenceParameter source
          (data.sourceSolution period hPeriod source) ∧
      (∀ field : data.boundary.triple.lagrangianDomainSubmodule
          (canonicalPhysicalScalarSeparatedCondition
            period a b hNondegenerate),
        data.boundary.triple.lagrangianSourceAction
            (canonicalPhysicalScalarSeparatedCondition
              period a b hNondegenerate)
            data.referenceParameter source
            (data.sourceSolution period hPeriod source) ≤
          data.boundary.triple.lagrangianSourceAction
            (canonicalPhysicalScalarSeparatedCondition
              period a b hNondegenerate)
            data.referenceParameter source field) ∧
      0 ≤ data.gaussianGeneratingFunctional period hPeriod source :=
  ⟨data.actualAdjointDomain_eq period hPeriod,
    data.sourceSolution_equation period hPeriod source,
    data.sourceSolution_stationary period hPeriod source,
    (data.sourceSolution_unique_minimizer period hPeriod source).1,
    (data.gaussian_certificate period hPeriod source).2⟩

end CanonicalPhysicalScalarCanonicalSeparatedResolventData

/-- Marker for the three standard Program P families. -/
theorem canonicalPhysicalScalarStandardBoundaryProgramPClosure_available : True :=
  trivial

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarCanonicalStandardBoundaryProgramPClosure4D
end JanusFormal
