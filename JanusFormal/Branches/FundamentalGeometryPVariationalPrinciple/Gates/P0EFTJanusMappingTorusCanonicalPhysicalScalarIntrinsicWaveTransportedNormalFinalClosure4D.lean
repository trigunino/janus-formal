import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveTransportedNormalGreen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPFinalObligations4D

/-!
# Final Program P closure from the universal normal transport

The normal Green density is not a field of this endpoint.  It is the negative
pullback of the explicit cutoff-collar divergence through one field-independent
transport whose integration formula carries the factor `2`.

The endpoint directly produces the Riesz boundary triple, self-adjoint compact
spectral theory, the variational source solution and the Gaussian response.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveTransportedNormalFinalClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveTransportedNormalGreen4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarScalarRemainderEnergyIdentity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetEulerCanonicalL2Operators4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPFinalObligations4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteCoordinateRellich4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleExternalPositiveShiftedForm4D

universe e

variable (period : Real) (hPeriod : period ≠ 0)
variable {Energy : Type e}
  [NormedAddCommGroup Energy] [NormedSpace Real Energy]

private abbrev BoundaryL2 := CanonicalPhysicalScalarFirstSheetL2 period

private abbrev BulkL2 :=
  P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D.CanonicalPhysicalBulkL2
    period hPeriod

/-- Final data whose normal Green component is transport-generated. -/
structure CanonicalPhysicalScalarIntrinsicWaveTransportedNormalFinalData
    (massSquared : Real) (Energy : Type e)
    [NormedAddCommGroup Energy] [NormedSpace Real Energy] where
  geometric : CanonicalPhysicalScalarIntrinsicWaveTransportedNormalGreenData
    period hPeriod massSquared
  energyIdentity : geometric.greenCore.ScalarRemainderEnergyIdentityData
    period hPeriod
  eulerCoefficientOperators :
    geometric.toCanonicalNormalGreenData.toNormalTangentialGreenData.toIntrinsicWaveLocalGreenData.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.CauchyJetEulerSixCanonicalL2OperatorData
      period hPeriod
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  referenceParameter : Real
  shiftedPositiveDecomposition :
    (assembleCanonicalPhysicalScalarBoundaryData period hPeriod
      geometric.toCanonicalNormalGreenData energyIdentity
        eulerCoefficientOperators).triple
      |>.LagrangianShiftedExternalPositiveDecompositionData
        condition referenceParameter Energy
  finiteCoordinateRellich : CanonicalPhysicalScalarFiniteCoordinateRellichData
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveTransportedNormalFinalData

/-- Conversion to the flat final-obligations package. -/
def toFinalObligationsData
    (data : CanonicalPhysicalScalarIntrinsicWaveTransportedNormalFinalData
      period hPeriod massSquared Energy) :
    CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy where
  geometric := data.geometric.toCanonicalNormalGreenData
  energyIdentity := data.energyIdentity
  eulerCoefficientOperators := data.eulerCoefficientOperators
  condition := data.condition
  referenceParameter := data.referenceParameter
  shiftedPositiveDecomposition := data.shiftedPositiveDecomposition
  finiteCoordinateRellich := data.finiteCoordinateRellich

/-- Completed Riesz trace. -/
def completedBoundaryTrace
    (data : CanonicalPhysicalScalarIntrinsicWaveTransportedNormalFinalData
      period hPeriod massSquared Energy) :=
  data.toFinalObligationsData.completedBoundaryTrace

/-- Completed physical boundary triple. -/
def triple
    (data : CanonicalPhysicalScalarIntrinsicWaveTransportedNormalFinalData
      period hPeriod massSquared Energy) :=
  data.toFinalObligationsData.triple

/-- Classical source solution. -/
noncomputable def sourceSolution
    (data : CanonicalPhysicalScalarIntrinsicWaveTransportedNormalFinalData
      period hPeriod massSquared Energy) :=
  data.toFinalObligationsData.sourceSolution period hPeriod

/-- Actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    (data : CanonicalPhysicalScalarIntrinsicWaveTransportedNormalFinalData
      period hPeriod massSquared Energy) :
    data.triple.actualAdjointDomain data.condition =
      data.triple.realizationDomain data.condition :=
  data.toFinalObligationsData.actualAdjointDomain_eq period hPeriod

/-- Strong shifted source equation. -/
theorem sourceSolution_equation
    (data : CanonicalPhysicalScalarIntrinsicWaveTransportedNormalFinalData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    data.triple.lagrangianShiftedOperator
        data.condition data.referenceParameter
        (data.sourceSolution period hPeriod source) = source :=
  data.toFinalObligationsData.sourceSolution_equation period hPeriod source

/-- Unique global minimizer. -/
theorem sourceSolution_unique_minimizer
    (data : CanonicalPhysicalScalarIntrinsicWaveTransportedNormalFinalData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :=
  data.toFinalObligationsData.sourceSolution_unique_minimizer
    period hPeriod source

/-- Gaussian generating functional. -/
def gaussianGeneratingFunctional
    (data : CanonicalPhysicalScalarIntrinsicWaveTransportedNormalFinalData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) : Real :=
  data.toFinalObligationsData.gaussianGeneratingFunctional period hPeriod source

/-- On-shell Gaussian identity and positivity. -/
theorem gaussian_certificate
    (data : CanonicalPhysicalScalarIntrinsicWaveTransportedNormalFinalData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    data.gaussianGeneratingFunctional period hPeriod source =
        -data.triple.lagrangianSourceAction
          data.condition data.referenceParameter source
          (data.sourceSolution period hPeriod source) ∧
      0 ≤ data.gaussianGeneratingFunctional period hPeriod source :=
  data.toFinalObligationsData.gaussian_certificate period hPeriod source

/-- Direct Fredholm alternative. -/
theorem fredholmAlternative
    (data : CanonicalPhysicalScalarIntrinsicWaveTransportedNormalFinalData
      period hPeriod massSquared Energy)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ data.referenceParameter) :
    data.triple.LagrangianHasEigenvalue
        data.condition spectralParameter ∨
      data.triple.LagrangianResolventPoint
        data.condition spectralParameter :=
  data.toFinalObligationsData.fredholmAlternative
    period hPeriod spectralParameter hParameter

/-- Complete transport-generated final certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarIntrinsicWaveTransportedNormalFinalData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    (∀ field test,
      Integrable (data.geometric.normalDensity field test)
        (P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D.canonicalLatitudeCauchyJetProductMeasure
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
              data.condition spectralParameter) :=
  ⟨data.geometric.toTransportedNormalDensityData.normalDensity_integrable,
    data.toFinalObligationsData.boundaryData.toCanonicalNormalRieszScalarEnergyPDEData.toNormalTangentialRieszScalarEnergyPDEData.toNormalTangentialRieszPDEData.rieszBoundaryData.boundedSmoothExtension
      |>.rieszBoundaryTrace_surjective,
    data.actualAdjointDomain_eq period hPeriod,
    data.sourceSolution_equation period hPeriod source,
    (data.sourceSolution_unique_minimizer period hPeriod source).1,
    (data.gaussian_certificate period hPeriod source).2,
    data.fredholmAlternative period hPeriod⟩

end CanonicalPhysicalScalarIntrinsicWaveTransportedNormalFinalData

/-- Marker theorem for the transport-generated final endpoint. -/
theorem canonicalPhysicalScalarIntrinsicWaveTransportedNormalFinalClosure_available : True :=
  trivial

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveTransportedNormalFinalClosure4D
end JanusFormal
