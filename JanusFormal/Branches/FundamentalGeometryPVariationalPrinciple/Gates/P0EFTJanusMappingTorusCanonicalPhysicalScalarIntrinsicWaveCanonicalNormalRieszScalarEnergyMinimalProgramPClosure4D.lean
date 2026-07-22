import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalProgramPClosure4D

/-!
# Smallest complete physical scalar Program P endpoint

The tangential divergence is induced from one normal component, the completed
trace is reconstructed by Riesz duality, the first-jet lower-order remainder is
scalar, the shifted square may live in an arbitrary energy space, and Rellich is
presented through finite coordinates.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalProgramPClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveNormalTangentialRieszScalarEnergyMinimalProgramPClosure4D

universe e

variable (period : Real) (hPeriod : period ≠ 0)
variable {Energy : Type e}
  [NormedAddCommGroup Energy] [NormedSpace Real Energy]

private abbrev BulkL2 :=
  P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticData

/-- Conversion to the complete normal/tangential Program P package. -/
def toNormalTangentialProgramPData
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy) :=
  analytic.toNormalTangentialScalarEnergyMinimalAnalyticData

/-- Classical source solution. -/
noncomputable def sourceSolution
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy) :=
  (analytic.toNormalTangentialProgramPData period hPeriod)
    |>.sourceSolution period hPeriod

/-- Strong shifted source equation. -/
theorem sourceSolution_equation
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    analytic.boundary.triple.lagrangianShiftedOperator
        analytic.condition analytic.referenceParameter
        (analytic.sourceSolution period hPeriod source) = source :=
  (analytic.toNormalTangentialProgramPData period hPeriod)
    |>.sourceSolution_equation period hPeriod source

/-- Weak stationarity. -/
theorem sourceSolution_stationary
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    analytic.boundary.triple.lagrangianSourceStationary
      analytic.condition analytic.referenceParameter source
      (analytic.sourceSolution period hPeriod source) :=
  (analytic.toNormalTangentialProgramPData period hPeriod)
    |>.sourceSolution_stationary period hPeriod source

/-- Unique global minimizer. -/
theorem sourceSolution_unique_minimizer
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticData
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
  (analytic.toNormalTangentialProgramPData period hPeriod)
    |>.sourceSolution_unique_minimizer period hPeriod source

/-- Gaussian generating functional. -/
def gaussianGeneratingFunctional
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) : Real :=
  (analytic.toNormalTangentialProgramPData period hPeriod)
    |>.gaussianGeneratingFunctional period hPeriod source

/-- On-shell Gaussian identity and positivity. -/
theorem gaussian_certificate
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    analytic.gaussianGeneratingFunctional period hPeriod source =
        -analytic.boundary.triple.lagrangianSourceAction
          analytic.condition analytic.referenceParameter source
          (analytic.sourceSolution period hPeriod source) ∧
      0 ≤ analytic.gaussianGeneratingFunctional period hPeriod source :=
  (analytic.toNormalTangentialProgramPData period hPeriod)
    |>.gaussian_certificate period hPeriod source

/-- Complete smallest-endpoint certificate. -/
theorem finalProgramP_certificate
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    (∀ field test,
      Integrable
        (analytic.boundary.geometric.tangentialDensity field test)
        (P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D.canonicalLatitudeCauchyJetProductMeasure
          period)) ∧
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
  ⟨analytic.boundary.geometric.toCanonicalNormalSplitData
      |>.tangentialDensity_integrable,
    analytic.boundary.toNormalTangentialRieszScalarEnergyPDEData.toNormalTangentialRieszPDEData.rieszBoundaryData
      |>.boundedSmoothExtension.rieszBoundaryTrace_surjective,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.sourceSolution_equation period hPeriod source,
    (analytic.sourceSolution_unique_minimizer period hPeriod source).1,
    (analytic.gaussian_certificate period hPeriod source).2,
    analytic.fredholmAlternative period hPeriod⟩

end CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalAnalyticData

/-- Marker theorem for the smallest complete scalar Program P endpoint. -/
theorem canonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalProgramPClosure_available : True :=
  trivial

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalProgramPClosure4D
end JanusFormal
