import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszResolventClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleVariational4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleGaussian4D

/-!
# Program P endpoint without normal trace regularity

The completed Cauchy trace is reconstructed by Riesz duality from the Green form
and the bounded explicit Cauchy extension.  The final physical endpoint therefore
contains neither a normal trace estimate nor a normal regularity space.

A positive shifted-form decomposition gives the classical source solution and
self-adjointness.  Finite-rank Rellich approximation gives compact spectral
theory.  This file exposes the full variational and Gaussian consequences.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszProgramPClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszResolventClosure4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleVariational4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleGaussian4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev BulkL2 :=
  P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveRieszResolventData

/-- Classical domain-valued source solution. -/
noncomputable def sourceSolution
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared) :
    BulkL2 period hPeriod →L[Real]
      analytic.boundary.triple.lagrangianDomainSubmodule analytic.condition :=
  (analytic.boundedResolvent period hPeriod).resolvent

/-- Strong shifted source equation. -/
theorem sourceSolution_equation
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    analytic.boundary.triple.lagrangianShiftedOperator
        analytic.condition analytic.referenceParameter
        (analytic.sourceSolution period hPeriod source) = source :=
  (analytic.boundedResolvent period hPeriod).left_inverse source

/-- Weak stationarity of the classical source solution. -/
theorem sourceSolution_stationary
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    analytic.boundary.triple.lagrangianSourceStationary
      analytic.condition analytic.referenceParameter source
      (analytic.sourceSolution period hPeriod source) :=
  analytic.boundary.triple.lagrangianSourceStationary_of_equation
    analytic.condition analytic.referenceParameter source _
    (analytic.sourceSolution_equation period hPeriod source)

/-- Weak stationarity is equivalent to the strong source equation. -/
theorem sourceStationary_iff_equation
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared)
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

/-- Exact first variation of the physical source action. -/
theorem sourceAction_hasDerivAt
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod)
    (field variation : analytic.boundary.triple.lagrangianDomainSubmodule
      analytic.condition) :
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

/-- Positive shifted coercivity makes the source solution the unique global
minimizer. -/
theorem sourceSolution_unique_minimizer
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared)
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

/-- Symmetric Gaussian source pairing. -/
def gaussianPairing
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared)
    (first second : BulkL2 period hPeriod) : Real :=
  analytic.boundary.triple.lagrangianGaussianPairing
    analytic.condition analytic.referenceParameter
    (analytic.boundedResolvent period hPeriod) first second

/-- Gaussian generating functional. -/
def gaussianGeneratingFunctional
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod) : Real :=
  analytic.boundary.triple.lagrangianGaussianGeneratingFunctional
    analytic.condition analytic.referenceParameter
    (analytic.boundedResolvent period hPeriod) source

/-- Symmetry of the Gaussian response. -/
theorem gaussianPairing_comm
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared)
    (first second : BulkL2 period hPeriod) :
    analytic.gaussianPairing period hPeriod first second =
      analytic.gaussianPairing period hPeriod second first :=
  analytic.boundary.triple.lagrangianGaussianPairing_comm
    analytic.condition analytic.referenceParameter
    (analytic.boundedResolvent period hPeriod) first second

/-- On-shell identity for the Gaussian generating functional. -/
theorem gaussianGeneratingFunctional_eq_neg_onShell
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    analytic.gaussianGeneratingFunctional period hPeriod source =
      -analytic.boundary.triple.lagrangianSourceAction
        analytic.condition analytic.referenceParameter source
        (analytic.sourceSolution period hPeriod source) := by
  unfold gaussianGeneratingFunctional sourceSolution
  exact analytic.boundary.triple
    |>.lagrangianGaussianGeneratingFunctional_eq_neg_onShell
      analytic.condition analytic.referenceParameter
      (analytic.boundedResolvent period hPeriod) source

/-- Nonnegativity of the physical Gaussian response. -/
theorem gaussianGeneratingFunctional_nonnegative
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    0 ≤ analytic.gaussianGeneratingFunctional period hPeriod source := by
  unfold gaussianGeneratingFunctional
  exact (analytic.shiftedFormCoercive period hPeriod).gaussian_nonnegative
    analytic.boundary.triple analytic.condition analytic.referenceParameter
    (analytic.denseDomain period hPeriod) source

/-- Complete normal-regularity-free Program P certificate. -/
theorem finalProgramP_certificate
    (analytic : CanonicalPhysicalScalarIntrinsicWaveRieszResolventData
      period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    Function.Surjective analytic.boundary.completedBoundaryTrace ∧
      analytic.boundary.triple.actualAdjointDomain analytic.condition =
        analytic.boundary.triple.realizationDomain analytic.condition ∧
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
      0 ≤ analytic.gaussianGeneratingFunctional period hPeriod source ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ analytic.referenceParameter →
          analytic.boundary.triple.LagrangianHasEigenvalue
              analytic.condition spectralParameter ∨
            analytic.boundary.triple.LagrangianResolventPoint
              analytic.condition spectralParameter) :=
  ⟨analytic.boundary.rieszBoundaryData.boundedSmoothExtension
      |>.rieszBoundaryTrace_surjective,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.sourceSolution_equation period hPeriod source,
    analytic.sourceSolution_stationary period hPeriod source,
    (analytic.sourceSolution_unique_minimizer period hPeriod source).1,
    analytic.gaussianGeneratingFunctional_nonnegative period hPeriod source,
    analytic.fredholmAlternative period hPeriod⟩

end CanonicalPhysicalScalarIntrinsicWaveRieszResolventData

/-- Marker theorem for the preferred Riesz Program P endpoint. -/
theorem canonicalPhysicalScalarIntrinsicWaveRieszProgramPClosure_available : True :=
  trivial

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveRieszProgramPClosure4D
end JanusFormal
