import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleVariational4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarCompletedBoundaryTripleGaussian4D

/-!
# Minimal final physical scalar Program P endpoint

The shifted positive part may take values in an arbitrary energy space and the
Rellich approximation is given by finite coordinate factorizations.  The
completed Cauchy trace is reconstructed by Riesz duality, while Green's theorem
uses the intrinsic normal/tangential divergence split.

The endpoint produces the classical source solution, exact stationarity,
unique global minimization, the symmetric nonnegative Gaussian response and the
complete compact spectral theory.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalProgramPClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticClosure4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleVariational4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleGaussian4D
open P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D

universe e

variable (period : Real) (hPeriod : period ≠ 0)
variable {Energy : Type e}
  [NormedAddCommGroup Energy] [NormedSpace Real Energy]

private abbrev BulkL2 :=
  P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData

/-- Classical domain-valued source solution. -/
noncomputable def sourceSolution
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy) :
    BulkL2 period hPeriod →L[Real]
      analytic.boundary.triple.lagrangianDomainSubmodule analytic.condition :=
  (analytic.boundedResolvent period hPeriod).resolvent

/-- Strong shifted source equation. -/
theorem sourceSolution_equation
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    analytic.boundary.triple.lagrangianShiftedOperator
        analytic.condition analytic.referenceParameter
        (analytic.sourceSolution period hPeriod source) = source :=
  (analytic.boundedResolvent period hPeriod).left_inverse source

/-- Weak stationarity. -/
theorem sourceSolution_stationary
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    analytic.boundary.triple.lagrangianSourceStationary
      analytic.condition analytic.referenceParameter source
      (analytic.sourceSolution period hPeriod source) :=
  analytic.boundary.triple.lagrangianSourceStationary_of_equation
    analytic.condition analytic.referenceParameter source _
    (analytic.sourceSolution_equation period hPeriod source)

/-- Weak stationarity is equivalent to the strong equation. -/
theorem sourceStationary_iff_equation
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy)
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

/-- Exact first variation. -/
theorem sourceAction_hasDerivAt
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy)
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

/-- Unique global minimizer. -/
theorem sourceSolution_unique_minimizer
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy)
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
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy)
    (first second : BulkL2 period hPeriod) : Real :=
  analytic.boundary.triple.lagrangianGaussianPairing
    analytic.condition analytic.referenceParameter
    (analytic.boundedResolvent period hPeriod) first second

/-- Gaussian generating functional. -/
def gaussianGeneratingFunctional
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) : Real :=
  analytic.boundary.triple.lagrangianGaussianGeneratingFunctional
    analytic.condition analytic.referenceParameter
    (analytic.boundedResolvent period hPeriod) source

/-- Symmetry of the Gaussian response. -/
theorem gaussianPairing_comm
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy)
    (first second : BulkL2 period hPeriod) :
    analytic.gaussianPairing period hPeriod first second =
      analytic.gaussianPairing period hPeriod second first :=
  analytic.boundary.triple.lagrangianGaussianPairing_comm
    analytic.condition analytic.referenceParameter
    (analytic.boundedResolvent period hPeriod) first second

/-- On-shell identity. -/
theorem gaussianGeneratingFunctional_eq_neg_onShell
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy)
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

/-- Nonnegative Gaussian response. -/
theorem gaussianGeneratingFunctional_nonnegative
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    0 ≤ analytic.gaussianGeneratingFunctional period hPeriod source := by
  unfold gaussianGeneratingFunctional
  exact (analytic.shiftedFormCoercive period hPeriod).gaussian_nonnegative
    analytic.boundary.triple analytic.condition analytic.referenceParameter
    (analytic.denseDomain period hPeriod) source

/-- Complete minimal Program P certificate. -/
theorem finalProgramP_certificate
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    (∀ field test,
      (∫ parameter,
        analytic.boundary.geometric.tangentialDensity field test parameter
        ∂P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D.canonicalLatitudeCauchyJetProductMeasure
          period) = 0) ∧
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
  ⟨analytic.boundary.geometric.toNormalTangentialSplitData
      |>.tangential_integral_eq_zero,
    analytic.boundary.toIntrinsicWaveRieszReducedPDEData.rieszBoundaryData
      |>.boundedSmoothExtension.rieszBoundaryTrace_surjective,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.sourceSolution_equation period hPeriod source,
    analytic.sourceSolution_stationary period hPeriod source,
    (analytic.sourceSolution_unique_minimizer period hPeriod source).1,
    analytic.gaussianGeneratingFunctional_nonnegative period hPeriod source,
    analytic.fredholmAlternative period hPeriod⟩

end CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalAnalyticData

/-- Marker theorem for the minimal final Program P endpoint. -/
theorem canonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalProgramPClosure_available : True :=
  trivial

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalProgramPClosure4D
end JanusFormal
