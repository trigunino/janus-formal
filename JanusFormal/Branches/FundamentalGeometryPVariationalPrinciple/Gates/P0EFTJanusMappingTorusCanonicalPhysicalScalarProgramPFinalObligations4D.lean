import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalProgramPClosure4D

/-!
# Flat package of the remaining physical scalar Program P obligations

All automatic infrastructure is hidden behind one final structure.  Its fields
are precisely the current mathematical frontier:

1. intrinsic scalar wave plus one normal Green density;
2. one scalar first-jet energy identity;
3. six continuous boundary `L²` coefficient operators and the residual formula;
4. one closed Lagrangian boundary condition;
5. one external positive-square shifted-form identity;
6. one finite-coordinate Rellich approximation scheme.

Everything else—measure support, all density results, the completed Riesz trace,
trace surjectivity, Gårding, self-adjointness, compact resolvent, Fredholm
alternative, finite multiplicity, variational minimization and Gaussian
response—is constructed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPFinalObligations4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreen4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarScalarRemainderEnergyIdentity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorPDEClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalProgramPClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteCoordinateRellich4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleExternalPositiveShiftedForm4D

universe e

variable (period : Real) (hPeriod : period ≠ 0)
variable {massSquared : Real}
variable {Energy : Type e}
  [NormedAddCommGroup Energy] [NormedSpace Real Energy]

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

private abbrev BulkL2 :=
  P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
    period hPeriod

/-- Assemble the final completed-boundary package from the three PDE inputs. -/
def assembleCanonicalPhysicalScalarBoundaryData
    (geometric : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreenData
      period hPeriod massSquared)
    (energyIdentity : (geometric.greenCore period hPeriod).ScalarRemainderEnergyIdentityData
      period hPeriod)
    (eulerCoefficientOperators :
      geometric.toNormalTangentialGreenData.toIntrinsicWaveLocalGreenData.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.CauchyJetEulerSixCanonicalL2OperatorData
        period hPeriod) :
    CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorPDEData
      period hPeriod massSquared where
  geometric := geometric
  energyIdentity := energyIdentity
  eulerCoefficientOperators := eulerCoefficientOperators

/-- Flat current frontier of the complete physical scalar theory. -/
structure CanonicalPhysicalScalarProgramPFinalObligationsData
    (massSquared : Real) (Energy : Type e)
    [NormedAddCommGroup Energy] [NormedSpace Real Energy] where
  geometric : CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalGreenData
    period hPeriod massSquared
  energyIdentity : (geometric.greenCore period hPeriod).ScalarRemainderEnergyIdentityData
    period hPeriod
  eulerCoefficientOperators :
    geometric.toNormalTangentialGreenData.toIntrinsicWaveLocalGreenData.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.CauchyJetEulerSixCanonicalL2OperatorData
      period hPeriod
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  referenceParameter : Real
  shiftedPositiveDecomposition :
    (assembleCanonicalPhysicalScalarBoundaryData period hPeriod
      geometric energyIdentity eulerCoefficientOperators).triple
      |>.LagrangianShiftedExternalPositiveDecompositionData
        condition referenceParameter Energy
  finiteCoordinateRellich : CanonicalPhysicalScalarFiniteCoordinateRellichData
    period hPeriod

namespace CanonicalPhysicalScalarProgramPFinalObligationsData

/-- Completed-boundary package assembled from the flat obligations. -/
def boundaryData
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy) :
    CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorPDEData
      period hPeriod massSquared :=
  assembleCanonicalPhysicalScalarBoundaryData period hPeriod
    data.geometric data.energyIdentity data.eulerCoefficientOperators

/-- Complete minimal analytic package assembled from the flat obligations. -/
def analyticData
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy) :
    CanonicalPhysicalScalarIntrinsicWaveCanonicalNormalRieszScalarEnergyL2OperatorMinimalAnalyticData
      period hPeriod massSquared Energy where
  boundary := data.boundaryData
  condition := data.condition
  referenceParameter := data.referenceParameter
  shiftedPositiveDecomposition := data.shiftedPositiveDecomposition
  finiteCoordinateRellich := data.finiteCoordinateRellich

/-- Riesz-generated completed trace. -/
def completedBoundaryTrace
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy) :=
  data.boundaryData.completedBoundaryTrace

/-- Bounded right inverse of the completed trace. -/
def completedExtension
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy) :=
  data.boundaryData.completedExtension

/-- Completed physical boundary triple. -/
def triple
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy) :=
  data.boundaryData.triple

/-- Classical source solution. -/
noncomputable def sourceSolution
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy) :=
  data.analyticData.sourceSolution period hPeriod

/-- Actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy) :
    data.triple.actualAdjointDomain data.condition =
      data.triple.realizationDomain data.condition :=
  data.analyticData.actualAdjointDomain_eq period hPeriod

/-- Compact reference resolvent. -/
noncomputable def compactResolvent
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy) :=
  data.analyticData.compactResolvent period hPeriod

/-- Strong shifted source equation. -/
theorem sourceSolution_equation
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    data.triple.lagrangianShiftedOperator
        data.condition data.referenceParameter
        (data.sourceSolution period hPeriod source) = source :=
  data.analyticData.sourceSolution_equation period hPeriod source

/-- Unique global variational minimizer. -/
theorem sourceSolution_unique_minimizer
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    (∀ field : data.triple.lagrangianDomainSubmodule data.condition,
      data.triple.lagrangianSourceAction
          data.condition data.referenceParameter source
          (data.sourceSolution period hPeriod source) ≤
        data.triple.lagrangianSourceAction
          data.condition data.referenceParameter source field) ∧
      (∀ field : data.triple.lagrangianDomainSubmodule data.condition,
        data.triple.lagrangianSourceAction
            data.condition data.referenceParameter source field =
          data.triple.lagrangianSourceAction
            data.condition data.referenceParameter source
            (data.sourceSolution period hPeriod source) →
        field = data.sourceSolution period hPeriod source) :=
  data.analyticData.sourceSolution_unique_minimizer period hPeriod source

/-- Gaussian generating functional. -/
def gaussianGeneratingFunctional
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) : Real :=
  data.analyticData.gaussianGeneratingFunctional period hPeriod source

/-- On-shell Gaussian identity and positivity. -/
theorem gaussian_certificate
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    data.gaussianGeneratingFunctional period hPeriod source =
        -data.triple.lagrangianSourceAction
          data.condition data.referenceParameter source
          (data.sourceSolution period hPeriod source) ∧
      0 ≤ data.gaussianGeneratingFunctional period hPeriod source :=
  data.analyticData.gaussian_certificate period hPeriod source

/-- Fredholm alternative. -/
theorem fredholmAlternative
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ data.referenceParameter) :
    data.triple.LagrangianHasEigenvalue
        data.condition spectralParameter ∨
      data.triple.LagrangianResolventPoint
        data.condition spectralParameter :=
  data.analyticData.fredholmAlternative
    period hPeriod spectralParameter hParameter

/-- Complete flattened Program P certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerAtlasNaturality4D.CanonicalPhysicalScalarWaveAtlasNaturality
        period hPeriod ∧
      (∀ index boundary,
        MemLp
          (data.eulerCoefficientOperators.coefficient
            period hPeriod index boundary)
          (2 : ENNReal)
          (P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D.canonicalLatitudeBaseMeasure
            period)) ∧
      Function.Surjective data.completedBoundaryTrace ∧
      data.triple.actualAdjointDomain data.condition =
        data.triple.realizationDomain data.condition ∧
      data.triple.lagrangianShiftedOperator
          data.condition data.referenceParameter
          (data.sourceSolution period hPeriod source) = source ∧
      (∀ field : data.triple.lagrangianDomainSubmodule data.condition,
        data.triple.lagrangianSourceAction
            data.condition data.referenceParameter source
            (data.sourceSolution period hPeriod source) ≤
          data.triple.lagrangianSourceAction
            data.condition data.referenceParameter source field) ∧
      0 ≤ data.gaussianGeneratingFunctional period hPeriod source ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ data.referenceParameter →
          data.triple.LagrangianHasEigenvalue
              data.condition spectralParameter ∨
            data.triple.LagrangianResolventPoint
              data.condition spectralParameter) := by
  refine ⟨data.geometric.intrinsicWave.toWaveAtlasNaturality period hPeriod, ?_⟩
  exact data.analyticData.finalProgramP_certificate period hPeriod source

end CanonicalPhysicalScalarProgramPFinalObligationsData

/-- Marker theorem for the flattened final obligations package. -/
theorem canonicalPhysicalScalarProgramPFinalObligations_available : True :=
  trivial

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPFinalObligations4D
end JanusFormal
