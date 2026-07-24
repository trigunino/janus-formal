import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalGreen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveTransportedNormalFinalClosure4D

/-!
# Final Program P closure from one normal pushforward measure identity

This endpoint replaces the analytical transport fields by one geometric theorem

`Measure.map transport μ_fullNormal = 2 • μ_positiveCollar`.

All remaining Program P conclusions are inherited from the transport-generated
normal Green package.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalFinalClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalGreen4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveTransportedNormalFinalClosure4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarScalarRemainderEnergyIdentity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
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

/-- Final data based on one pushforward normal-measure identity. -/
structure CanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalFinalData
    (massSquared : Real) (Energy : Type e)
    [NormedAddCommGroup Energy] [NormedSpace Real Energy] where
  geometric :
    CanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalGreenData
      period hPeriod massSquared
  energyIdentity : (geometric.greenCore period hPeriod).ScalarRemainderEnergyIdentityData
    period hPeriod
  eulerCoefficientOperators :
    geometric.toCanonicalNormalGreenData.toNormalTangentialGreenData.toIntrinsicWaveLocalGreenData.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.CauchyJetEulerSixCanonicalL2OperatorData
      period hPeriod
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  referenceParameter : Real
  shiftedPositiveDecomposition :
    (P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPFinalObligations4D.assembleCanonicalPhysicalScalarBoundaryData
      period hPeriod (geometric.toCanonicalNormalGreenData period hPeriod) energyIdentity
        eulerCoefficientOperators).triple
      |>.LagrangianShiftedExternalPositiveDecompositionData
        condition referenceParameter Energy
  finiteCoordinateRellich : CanonicalPhysicalScalarFiniteCoordinateRellichData
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalFinalData

/-- Conversion to the analytical transported-normal endpoint. -/
def toTransportedNormalFinalData
    (data : CanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalFinalData
      period hPeriod massSquared Energy) :
    CanonicalPhysicalScalarIntrinsicWaveTransportedNormalFinalData
      period hPeriod massSquared Energy where
  geometric := data.geometric.toTransportedNormalGreenData period hPeriod
  energyIdentity := data.energyIdentity
  eulerCoefficientOperators := data.eulerCoefficientOperators
  condition := data.condition
  referenceParameter := data.referenceParameter
  shiftedPositiveDecomposition := data.shiftedPositiveDecomposition
  finiteCoordinateRellich := data.finiteCoordinateRellich

/-- Completed Riesz trace. -/
def completedBoundaryTrace
    (data : CanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalFinalData
      period hPeriod massSquared Energy) :=
  data.toTransportedNormalFinalData.completedBoundaryTrace

/-- Completed physical boundary triple. -/
def triple
    (data : CanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalFinalData
      period hPeriod massSquared Energy) :=
  data.toTransportedNormalFinalData.triple

/-- Classical source solution. -/
noncomputable def sourceSolution
    (data : CanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalFinalData
      period hPeriod massSquared Energy) :=
  data.toTransportedNormalFinalData.sourceSolution period hPeriod

/-- Actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    (data : CanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalFinalData
      period hPeriod massSquared Energy) :
    data.triple.actualAdjointDomain data.condition =
      data.triple.realizationDomain data.condition :=
  data.toTransportedNormalFinalData.actualAdjointDomain_eq period hPeriod

/-- Strong shifted source equation. -/
theorem sourceSolution_equation
    (data : CanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalFinalData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    data.triple.lagrangianShiftedOperator
        data.condition data.referenceParameter
        (data.sourceSolution period hPeriod source) = source :=
  data.toTransportedNormalFinalData.sourceSolution_equation
    period hPeriod source

/-- Unique global minimizer. -/
theorem sourceSolution_unique_minimizer
    (data : CanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalFinalData
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
  data.toTransportedNormalFinalData.sourceSolution_unique_minimizer
    period hPeriod source

/-- Gaussian generating functional. -/
def gaussianGeneratingFunctional
    (data : CanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalFinalData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) : Real :=
  data.toTransportedNormalFinalData.gaussianGeneratingFunctional
    period hPeriod source

/-- On-shell Gaussian identity and positivity. -/
theorem gaussian_certificate
    (data : CanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalFinalData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    data.gaussianGeneratingFunctional period hPeriod source =
        -data.triple.lagrangianSourceAction
          data.condition data.referenceParameter source
          (data.sourceSolution period hPeriod source) ∧
      0 ≤ data.gaussianGeneratingFunctional period hPeriod source :=
  data.toTransportedNormalFinalData.gaussian_certificate
    period hPeriod source

/-- Fredholm alternative. -/
theorem fredholmAlternative
    (data : CanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalFinalData
      period hPeriod massSquared Energy)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ data.referenceParameter) :
    data.triple.LagrangianHasEigenvalue
        data.condition spectralParameter ∨
      data.triple.LagrangianResolventPoint
        data.condition spectralParameter :=
  data.toTransportedNormalFinalData.fredholmAlternative
    period hPeriod spectralParameter hParameter

/-- Pushforward-measure final certificate. -/
theorem certificate
    (data : CanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalFinalData
      period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    Measure.map data.geometric.measureTransport.transport
        (P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D.canonicalLatitudeCauchyJetProductMeasure
          period) =
      (2 : NNReal) •
        P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D.canonicalLatitudeCollarMeasure
          period ∧
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
  refine ⟨(data.geometric.certificate period hPeriod).1, ?_⟩
  exact (data.toTransportedNormalFinalData.certificate period hPeriod source).2

end CanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalFinalData

/-- Marker for the pushforward-measure final endpoint. -/
theorem canonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalFinalClosure_available : True :=
  trivial

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveMeasureTransportedNormalFinalClosure4D
end JanusFormal
