import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalProgramPClosure4D

/-!
# Complete Program P endpoint with canonical `L²` coefficient operators

This is the smallest current complete endpoint.  The six Euler coefficients are
continuous operators into boundary `L²`; their representatives, integrability,
constants and graph estimate are generated automatically.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyMinimalProgramPClosure4D

universe e

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}
variable {Energy : Type e}
  [NormedAddCommGroup Energy] [NormedSpace Real Energy]

private abbrev BulkL2 :=
  P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData

/-- Conversion to the former smallest Program P endpoint. -/
def toCanonicalNormalRieszScalarEnergyProgramPData
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData
      period hPeriod massSquared Energy) :=
  analytic.toCanonicalNormalRieszScalarEnergyMinimalAnalyticData

/-- Classical source solution. -/
noncomputable def sourceSolution
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData
      period hPeriod massSquared Energy) :=
  (analytic.toCanonicalNormalRieszScalarEnergyProgramPData period hPeriod)
    |>.sourceSolution period hPeriod

/-- Strong shifted source equation. -/
theorem sourceSolution_equation
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    analytic.boundary.triple.lagrangianShiftedOperator
        analytic.condition analytic.referenceParameter
        (analytic.sourceSolution period hPeriod source) = source :=
  (analytic.toCanonicalNormalRieszScalarEnergyProgramPData period hPeriod)
    |>.sourceSolution_equation period hPeriod source

/-- Weak stationarity. -/
theorem sourceSolution_stationary
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    analytic.boundary.triple.lagrangianSourceStationary
      analytic.condition analytic.referenceParameter source
      (analytic.sourceSolution period hPeriod source) :=
  (analytic.toCanonicalNormalRieszScalarEnergyProgramPData period hPeriod)
    |>.sourceSolution_stationary period hPeriod source

/-- Unique global minimizer. -/
theorem sourceSolution_unique_minimizer
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData
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
  (analytic.toCanonicalNormalRieszScalarEnergyProgramPData period hPeriod)
    |>.sourceSolution_unique_minimizer period hPeriod source

/-- Gaussian generating functional. -/
def gaussianGeneratingFunctional
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) : Real :=
  (analytic.toCanonicalNormalRieszScalarEnergyProgramPData period hPeriod)
    |>.gaussianGeneratingFunctional period hPeriod source

/-- On-shell Gaussian identity and positivity. -/
theorem gaussian_certificate
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    analytic.gaussianGeneratingFunctional period hPeriod source =
        -analytic.boundary.triple.lagrangianSourceAction
          analytic.condition analytic.referenceParameter source
          (analytic.sourceSolution period hPeriod source) ∧
      0 ≤ analytic.gaussianGeneratingFunctional period hPeriod source :=
  (analytic.toCanonicalNormalRieszScalarEnergyProgramPData period hPeriod)
    |>.gaussian_certificate period hPeriod source

/-- Complete canonical-`L²`-operator Program P certificate. -/
theorem finalProgramP_certificate
    (analytic : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    (∀ index boundary,
      MemLp
        (analytic.boundary.eulerCoefficientOperators.coefficient
          period hPeriod index boundary)
        (2 : ENNReal)
        (P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D.canonicalLatitudeBaseMeasure
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
  ⟨analytic.boundary.eulerCoefficientOperators.coefficient_memLp period hPeriod,
    (analytic.boundary.certificate period hPeriod).2.2.2.2.1,
    analytic.actualAdjointDomain_eq period hPeriod,
    analytic.sourceSolution_equation period hPeriod source,
    (analytic.sourceSolution_unique_minimizer period hPeriod source).1,
    (analytic.gaussian_certificate period hPeriod source).2,
    analytic.fredholmAlternative period hPeriod⟩

end CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticClosure4D

namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalProgramPClosure4D

/-- Marker theorem for the canonical-`L²`-operator Program P endpoint. -/
theorem canonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalProgramPClosure_available : True :=
  trivial

end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalProgramPClosure4D
end JanusFormal
