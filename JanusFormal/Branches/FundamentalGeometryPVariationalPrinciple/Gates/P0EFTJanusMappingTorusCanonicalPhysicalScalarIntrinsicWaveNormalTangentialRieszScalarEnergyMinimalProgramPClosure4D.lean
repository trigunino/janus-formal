import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalProgramPClosure4D

/-!
# Scalar-energy minimal Program P endpoint

This is the smallest current complete physical scalar endpoint.  The
zeroth-order part of the first-jet identity is one real coefficient, the shifted
positive part takes values in an arbitrary energy space, and Rellich is supplied
through finite coordinate factorizations.

The endpoint exports the unique variational source solution, Gaussian response,
self-adjointness and compact spectral theory.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalProgramPClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszMinimalProgramPClosure4D

universe e

variable (period : Real) (hPeriod : period ≠ 0)
variable {Energy : Type e}
  [NormedAddCommGroup Energy] [NormedSpace Real Energy]

private abbrev BulkL2 :=
  P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData

/-- Conversion to the general minimal Program P package. -/
def toMinimalProgramPData
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy) :=
  analytic.toMinimalAnalyticData

/-- Classical source solution. -/
noncomputable def sourceSolution
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy) :=
  (analytic.toMinimalProgramPData period hPeriod)
    |>.sourceSolution period hPeriod

/-- Strong shifted source equation. -/
theorem sourceSolution_equation
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    analytic.boundary.triple.lagrangianShiftedOperator
        analytic.condition analytic.referenceParameter
        (analytic.sourceSolution period hPeriod source) = source :=
  (analytic.toMinimalProgramPData period hPeriod)
    |>.sourceSolution_equation period hPeriod source

/-- Weak stationarity. -/
theorem sourceSolution_stationary
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    analytic.boundary.triple.lagrangianSourceStationary
      analytic.condition analytic.referenceParameter source
      (analytic.sourceSolution period hPeriod source) :=
  (analytic.toMinimalProgramPData period hPeriod)
    |>.sourceSolution_stationary period hPeriod source

/-- Unique global minimizer. -/
theorem sourceSolution_unique_minimizer
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData
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
  (analytic.toMinimalProgramPData period hPeriod)
    |>.sourceSolution_unique_minimizer period hPeriod source

/-- Symmetric Gaussian pairing. -/
def gaussianPairing
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy)
    (first second : BulkL2 period hPeriod) : Real :=
  (analytic.toMinimalProgramPData period hPeriod)
    |>.gaussianPairing period hPeriod first second

/-- Gaussian generating functional. -/
def gaussianGeneratingFunctional
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) : Real :=
  (analytic.toMinimalProgramPData period hPeriod)
    |>.gaussianGeneratingFunctional period hPeriod source

/-- On-shell identity and nonnegativity. -/
theorem gaussian_certificate
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    analytic.gaussianGeneratingFunctional period hPeriod source =
        -analytic.boundary.triple.lagrangianSourceAction
          analytic.condition analytic.referenceParameter source
          (analytic.sourceSolution period hPeriod source) ∧
      0 ≤ analytic.gaussianGeneratingFunctional period hPeriod source :=
  ⟨(analytic.toMinimalProgramPData period hPeriod)
      |>.gaussianGeneratingFunctional_eq_neg_onShell period hPeriod source,
    (analytic.toMinimalProgramPData period hPeriod)
      |>.gaussianGeneratingFunctional_nonnegative period hPeriod source⟩

/-- Complete smallest-endpoint Program P certificate. -/
theorem finalProgramP_certificate
    (analytic : CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    (∀ field :
      P0EFTJanusMappingTorusSmoothFieldDescent4D.SmoothQuotientField
        period hPeriod Real,
      P0EFTJanusMappingTorusCanonicalPhysicalScalarAutomaticGardingEnergy4D.canonicalPhysicalScalarFirstJetComponentEnergy
          period hPeriod field =
        analytic.boundary.energyIdentity.pairingSign *
            inner Real (analytic.boundary.geometric.greenCore.core.operator field)
              (analytic.boundary.geometric.greenCore.core.inclusion field) +
          analytic.boundary.energyIdentity.zerothCoefficient *
            ‖analytic.boundary.geometric.greenCore.core.inclusion field‖ ^ 2) ∧
      Function.Surjective analytic.boundary.completedBoundaryTrace ∧
      analytic.boundary.triple.actualAdjointDomain analytic.condition =
        analytic.boundary.triple.realizationDomain analytic.condition ∧
      analytic.boundary.triple.lagrangianShiftedOperator
          analytic.condition analytic.referenceParameter
          (analytic.sourceSolution period hPeriod source) = source ∧
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
  ⟨analytic.boundary.energyIdentity.energy_identity,
    analytic.boundary.toNormalTangentialRieszPDEData.rieszBoundaryData
      |>.boundedSmoothExtension.rieszBoundaryTrace_surjective,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.sourceSolution_equation period hPeriod source,
    (analytic.sourceSolution_unique_minimizer period hPeriod source).1,
    (analytic.gaussian_certificate period hPeriod source).2,
    analytic.fredholmAlternative period hPeriod⟩

end CanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalAnalyticData

/-- Marker theorem for the smallest complete Program P endpoint. -/
theorem canonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalProgramPClosure_available : True :=
  trivial

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalProgramPClosure4D
end JanusFormal
