import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPFinalObligations4D

/-!
# Final Program P closure from corrected weighted normal transport

The corrected affine transport constructs the normal Green component and its
factor-two integral.  The remaining final fields are exactly the nontransport
obligations of the flattened Program P package.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalFinalClosure4D

set_option autoImplicit false
noncomputable section

open Set Topology MeasureTheory
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetHilbertTrace4D
open P0EFTJanusMappingTorusCanonicalLatitudeNormalHalfCollarMeasureTransport4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreen4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarScalarRemainderEnergyIdentity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarCauchyJetGeometricGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarProgramPFinalObligations4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFiniteCoordinateRellich4D
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarCompletedBoundaryTripleShiftedForm4D
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

/-- Preferred weighted-transport endpoint with a direct graph estimate and
direct shifted coercivity. -/
structure CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphDirectCoerciveFinalData
    (massSquared : Real) where
  geometric :
    CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
      period hPeriod massSquared
  eulerCoefficientOperators :
    geometric.toCanonicalNormalGreenData.toNormalTangentialGreenData.toIntrinsicWaveLocalGreenData.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.CauchyJetEulerSixCanonicalL2OperatorData
      period hPeriod
  graphEllipticEstimate :
    (geometric.greenCore period hPeriod).GraphEllipticEstimate period hPeriod
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  referenceParameter : Real
  shiftedFormCoercive :
    (assembleCanonicalPhysicalScalarGraphBoundaryData period hPeriod
      (geometric.toCanonicalNormalGreenData period hPeriod)
      eulerCoefficientOperators).triple
      |>.LagrangianShiftedFormCoerciveData condition referenceParameter
  finiteCoordinateRellich : CanonicalPhysicalScalarFiniteCoordinateRellichData
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphDirectCoerciveFinalData

/-- Conversion to the preferred flattened final obligations. -/
def toGraphDirectCoerciveFinalObligationsData
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphDirectCoerciveFinalData
        period hPeriod massSquared) :
    CanonicalPhysicalScalarProgramPGraphDirectCoerciveFinalObligationsData
      period hPeriod massSquared where
  geometric := data.geometric.toCanonicalNormalGreenData period hPeriod
  eulerCoefficientOperators := data.eulerCoefficientOperators
  graphEllipticEstimate := data.graphEllipticEstimate
  condition := data.condition
  referenceParameter := data.referenceParameter
  shiftedFormCoercive := data.shiftedFormCoercive
  finiteCoordinateRellich := data.finiteCoordinateRellich

/-- Riesz-generated completed boundary trace. -/
def completedBoundaryTrace
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphDirectCoerciveFinalData
        period hPeriod massSquared) :=
  data.toGraphDirectCoerciveFinalObligationsData.completedBoundaryTrace

/-- Completed physical boundary triple. -/
def triple
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphDirectCoerciveFinalData
        period hPeriod massSquared) :=
  data.toGraphDirectCoerciveFinalObligationsData.triple

/-- Compact reference resolvent. -/
noncomputable def compactResolvent
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphDirectCoerciveFinalData
        period hPeriod massSquared) :=
  data.toGraphDirectCoerciveFinalObligationsData.compactResolvent period hPeriod

/-- Classical shifted source solution. -/
noncomputable def sourceSolution
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphDirectCoerciveFinalData
        period hPeriod massSquared) :=
  data.toGraphDirectCoerciveFinalObligationsData.sourceSolution period hPeriod

/-- Actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphDirectCoerciveFinalData
        period hPeriod massSquared) :
    data.triple.actualAdjointDomain data.condition =
      data.triple.realizationDomain data.condition :=
  data.toGraphDirectCoerciveFinalObligationsData.actualAdjointDomain_eq
    period hPeriod

/-- Strong shifted source equation. -/
theorem sourceSolution_equation
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphDirectCoerciveFinalData
        period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    data.triple.lagrangianShiftedOperator
        data.condition data.referenceParameter
        (data.sourceSolution period hPeriod source) = source :=
  data.toGraphDirectCoerciveFinalObligationsData.sourceSolution_equation
    period hPeriod source

/-- Fredholm alternative away from the reference parameter. -/
theorem fredholmAlternative
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphDirectCoerciveFinalData
        period hPeriod massSquared)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ data.referenceParameter) :
    data.triple.LagrangianHasEigenvalue data.condition spectralParameter ∨
      data.triple.LagrangianResolventPoint data.condition spectralParameter :=
  data.toGraphDirectCoerciveFinalObligationsData.fredholmAlternative
    period hPeriod spectralParameter hParameter

/-- Preferred weighted-transport final certificate. -/
theorem certificate
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphDirectCoerciveFinalData
        period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    Measure.map canonicalLatitudeWeightedNormalToHalfCollarTransport
        (canonicalLatitudeCorrectedCauchyJetProductMeasure period) =
      (2 : NNReal) •
        P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D.canonicalLatitudeCollarMeasure
          period ∧
      (∀ field test,
        Integrable
          (P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalProductLocalDivergence4D.canonicalPhysicalScalarEulerProductLocalDivergenceDensity
            period hPeriod field test)
          (P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D.canonicalLatitudeCauchyJetProductMeasure
            period)) ∧
      Function.Surjective data.completedBoundaryTrace ∧
      data.triple.actualAdjointDomain data.condition =
        data.triple.realizationDomain data.condition ∧
      data.triple.lagrangianShiftedOperator
          data.condition data.referenceParameter
          (data.sourceSolution period hPeriod source) = source ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ data.referenceParameter →
          data.triple.LagrangianHasEigenvalue
              data.condition spectralParameter ∨
          data.triple.LagrangianResolventPoint
              data.condition spectralParameter) := by
  refine ⟨map_canonicalLatitudeCorrectedCauchyJetProductMeasure period,
    data.geometric.localDivergence_integrable period hPeriod, ?_⟩
  have hFinal :=
    data.toGraphDirectCoerciveFinalObligationsData.certificate
      period hPeriod source
  exact ⟨hFinal.2.2.1, hFinal.2.2.2.1,
    hFinal.2.2.2.2.1, data.fredholmAlternative period hPeriod⟩

end CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphDirectCoerciveFinalData

/-- Final weighted-transport data with shifted coercivity supplied directly. -/
structure CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalDirectCoerciveFinalData
    (massSquared : Real) where
  geometric :
    CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
      period hPeriod massSquared
  energyIdentity :
    (geometric.greenCore period hPeriod).MassCorrectedEnergyIdentityData
      period hPeriod
  eulerCoefficientOperators :
    geometric.toCanonicalNormalGreenData.toNormalTangentialGreenData.toIntrinsicWaveLocalGreenData.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.CauchyJetEulerSixCanonicalL2OperatorData
      period hPeriod
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  referenceParameter : Real
  shiftedFormCoercive :
    (assembleCanonicalPhysicalScalarBoundaryData period hPeriod
      (geometric.toCanonicalNormalGreenData period hPeriod)
        (energyIdentity.toScalarRemainderEnergyIdentityData
          period hPeriod (geometric.greenCore period hPeriod))
        eulerCoefficientOperators).triple
      |>.LagrangianShiftedFormCoerciveData condition referenceParameter
  finiteCoordinateRellich : CanonicalPhysicalScalarFiniteCoordinateRellichData
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalDirectCoerciveFinalData

/-- Conversion to the direct-coercive flattened final obligations. -/
def toDirectCoerciveFinalObligationsData
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalDirectCoerciveFinalData
        period hPeriod massSquared) :
    CanonicalPhysicalScalarProgramPDirectCoerciveFinalObligationsData
      period hPeriod massSquared where
  geometric := data.geometric.toCanonicalNormalGreenData period hPeriod
  energyIdentity :=
    data.energyIdentity.toScalarRemainderEnergyIdentityData
      period hPeriod (data.geometric.greenCore period hPeriod)
  eulerCoefficientOperators := data.eulerCoefficientOperators
  condition := data.condition
  referenceParameter := data.referenceParameter
  shiftedFormCoercive := data.shiftedFormCoercive
  finiteCoordinateRellich := data.finiteCoordinateRellich

/-- The scalar zeroth-order remainder is fixed by the mass convention. -/
theorem energyZerothCoefficient_eq
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalDirectCoerciveFinalData
        period hPeriod massSquared) :
    data.toDirectCoerciveFinalObligationsData.energyIdentity.zerothCoefficient =
      data.energyIdentity.pairingSign * massSquared :=
  rfl

/-- Riesz-generated completed boundary trace. -/
def completedBoundaryTrace
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalDirectCoerciveFinalData
        period hPeriod massSquared) :=
  data.toDirectCoerciveFinalObligationsData.completedBoundaryTrace

/-- Completed physical boundary triple. -/
def triple
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalDirectCoerciveFinalData
        period hPeriod massSquared) :=
  data.toDirectCoerciveFinalObligationsData.triple

/-- Compact reference resolvent. -/
noncomputable def compactResolvent
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalDirectCoerciveFinalData
        period hPeriod massSquared) :=
  data.toDirectCoerciveFinalObligationsData.compactResolvent period hPeriod

/-- Classical shifted source solution. -/
noncomputable def sourceSolution
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalDirectCoerciveFinalData
        period hPeriod massSquared) :=
  data.toDirectCoerciveFinalObligationsData.sourceSolution period hPeriod

/-- Actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalDirectCoerciveFinalData
        period hPeriod massSquared) :
    data.triple.actualAdjointDomain data.condition =
      data.triple.realizationDomain data.condition :=
  data.toDirectCoerciveFinalObligationsData.actualAdjointDomain_eq
    period hPeriod

/-- Strong shifted source equation. -/
theorem sourceSolution_equation
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalDirectCoerciveFinalData
        period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    data.triple.lagrangianShiftedOperator
        data.condition data.referenceParameter
        (data.sourceSolution period hPeriod source) = source :=
  data.toDirectCoerciveFinalObligationsData.sourceSolution_equation
    period hPeriod source

/-- Fredholm alternative away from the reference parameter. -/
theorem fredholmAlternative
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalDirectCoerciveFinalData
        period hPeriod massSquared)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ data.referenceParameter) :
    data.triple.LagrangianHasEigenvalue
        data.condition spectralParameter ∨
      data.triple.LagrangianResolventPoint
        data.condition spectralParameter :=
  data.toDirectCoerciveFinalObligationsData.fredholmAlternative
    period hPeriod spectralParameter hParameter

/-- Direct-coercive weighted-transport final certificate. -/
theorem certificate
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalDirectCoerciveFinalData
        period hPeriod massSquared)
    (source : BulkL2 period hPeriod) :
    Measure.map canonicalLatitudeWeightedNormalToHalfCollarTransport
        (canonicalLatitudeCorrectedCauchyJetProductMeasure period) =
      (2 : NNReal) •
        P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D.canonicalLatitudeCollarMeasure
          period ∧
      (∀ field test,
        Integrable
          (P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalProductLocalDivergence4D.canonicalPhysicalScalarEulerProductLocalDivergenceDensity
            period hPeriod field test)
          (P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D.canonicalLatitudeCauchyJetProductMeasure
            period)) ∧
      Function.Surjective data.completedBoundaryTrace ∧
      data.triple.actualAdjointDomain data.condition =
        data.triple.realizationDomain data.condition ∧
      data.triple.lagrangianShiftedOperator
          data.condition data.referenceParameter
          (data.sourceSolution period hPeriod source) = source ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ data.referenceParameter →
          data.triple.LagrangianHasEigenvalue
              data.condition spectralParameter ∨
          data.triple.LagrangianResolventPoint
              data.condition spectralParameter) := by
  refine ⟨map_canonicalLatitudeCorrectedCauchyJetProductMeasure period,
    data.geometric.localDivergence_integrable period hPeriod, ?_⟩
  have hFinal :=
    data.toDirectCoerciveFinalObligationsData.certificate
      period hPeriod source
  exact ⟨hFinal.2.2.1, hFinal.2.2.2.1,
    hFinal.2.2.2.2.1, data.fredholmAlternative period hPeriod⟩

end CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalDirectCoerciveFinalData

/-- Final data with the normal Green component generated by corrected weighted
transport. -/
structure CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalFinalData
    (massSquared : Real) (Energy : Type e)
    [NormedAddCommGroup Energy] [NormedSpace Real Energy] where
  geometric :
    CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedGlobalGreenData
      period hPeriod massSquared
  energyIdentity :
    (geometric.greenCore period hPeriod).MassCorrectedEnergyIdentityData
      period hPeriod
  eulerCoefficientOperators :
    geometric.toCanonicalNormalGreenData.toNormalTangentialGreenData.toIntrinsicWaveLocalGreenData.toCanonicalLocalDivergenceData.toCanonicalWaveCauchyJetData.toCanonicalCauchyJetCompatibilityData.toCompatibilityData.toCauchyJetGeometricData.CauchyJetEulerSixCanonicalL2OperatorData
      period hPeriod
  condition : CanonicalScalarHilbertLagrangianBoundaryCondition
    (BoundaryL2 period)
  referenceParameter : Real
  shiftedPositiveDecomposition :
    (assembleCanonicalPhysicalScalarBoundaryData period hPeriod
      (geometric.toCanonicalNormalGreenData period hPeriod)
        (energyIdentity.toScalarRemainderEnergyIdentityData
          period hPeriod (geometric.greenCore period hPeriod))
        eulerCoefficientOperators).triple
      |>.LagrangianShiftedExternalPositiveDecompositionData
        condition referenceParameter Energy
  finiteCoordinateRellich : CanonicalPhysicalScalarFiniteCoordinateRellichData
    period hPeriod

namespace CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalFinalData

/-- Conversion to the flattened final obligations package. -/
def toFinalObligationsData
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalFinalData
        period hPeriod massSquared Energy) :
    CanonicalPhysicalScalarProgramPFinalObligationsData
      period hPeriod massSquared Energy where
  geometric := data.geometric.toCanonicalNormalGreenData period hPeriod
  energyIdentity :=
    data.energyIdentity.toScalarRemainderEnergyIdentityData
      period hPeriod (data.geometric.greenCore period hPeriod)
  eulerCoefficientOperators := data.eulerCoefficientOperators
  condition := data.condition
  referenceParameter := data.referenceParameter
  shiftedPositiveDecomposition := data.shiftedPositiveDecomposition
  finiteCoordinateRellich := data.finiteCoordinateRellich

/-- The scalar zeroth-order remainder is fixed by the mass convention. -/
theorem energyZerothCoefficient_eq
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalFinalData
        period hPeriod massSquared Energy) :
    data.toFinalObligationsData.energyIdentity.zerothCoefficient =
      data.energyIdentity.pairingSign * massSquared :=
  rfl

/-- Riesz-generated completed boundary trace. -/
def completedBoundaryTrace
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalFinalData
        period hPeriod massSquared Energy) :=
  data.toFinalObligationsData.completedBoundaryTrace

/-- Completed physical boundary triple. -/
def triple
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalFinalData
        period hPeriod massSquared Energy) :=
  data.toFinalObligationsData.triple

/-- Compact reference resolvent. -/
noncomputable def compactResolvent
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalFinalData
        period hPeriod massSquared Energy) :=
  data.toFinalObligationsData.compactResolvent period hPeriod

/-- Classical shifted source solution. -/
noncomputable def sourceSolution
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalFinalData
        period hPeriod massSquared Energy) :=
  data.toFinalObligationsData.sourceSolution period hPeriod

/-- Actual Hilbert self-adjointness. -/
theorem actualAdjointDomain_eq
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalFinalData
        period hPeriod massSquared Energy) :
    data.triple.actualAdjointDomain data.condition =
      data.triple.realizationDomain data.condition :=
  data.toFinalObligationsData.actualAdjointDomain_eq period hPeriod

/-- Strong shifted source equation. -/
theorem sourceSolution_equation
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalFinalData
        period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    data.triple.lagrangianShiftedOperator
        data.condition data.referenceParameter
        (data.sourceSolution period hPeriod source) = source :=
  data.toFinalObligationsData.sourceSolution_equation
    period hPeriod source

/-- Fredholm alternative away from the reference parameter. -/
theorem fredholmAlternative
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalFinalData
        period hPeriod massSquared Energy)
    (spectralParameter : Real)
    (hParameter : spectralParameter ≠ data.referenceParameter) :
    data.triple.LagrangianHasEigenvalue
        data.condition spectralParameter ∨
      data.triple.LagrangianResolventPoint
        data.condition spectralParameter :=
  data.toFinalObligationsData.fredholmAlternative
    period hPeriod spectralParameter hParameter

/-- Corrected weighted-transport final certificate. -/
theorem certificate
    (data :
      CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalFinalData
        period hPeriod massSquared Energy)
    (source : BulkL2 period hPeriod) :
    Measure.map canonicalLatitudeWeightedNormalToHalfCollarTransport
        (canonicalLatitudeCorrectedCauchyJetProductMeasure period) =
      (2 : NNReal) •
        P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D.canonicalLatitudeCollarMeasure
          period ∧
      (∀ field test,
        Integrable
          (P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalProductLocalDivergence4D.canonicalPhysicalScalarEulerProductLocalDivergenceDensity
            period hPeriod field test)
          (P0EFTJanusMappingTorusCanonicalLatitudeCauchyJetProductCoarea4D.canonicalLatitudeCauchyJetProductMeasure
            period)) ∧
      Function.Surjective data.completedBoundaryTrace ∧
      data.triple.actualAdjointDomain data.condition =
        data.triple.realizationDomain data.condition ∧
      data.triple.lagrangianShiftedOperator
          data.condition data.referenceParameter
          (data.sourceSolution period hPeriod source) = source ∧
      (∀ spectralParameter : Real,
        spectralParameter ≠ data.referenceParameter →
          data.triple.LagrangianHasEigenvalue
              data.condition spectralParameter ∨
          data.triple.LagrangianResolventPoint
              data.condition spectralParameter) := by
  refine ⟨map_canonicalLatitudeCorrectedCauchyJetProductMeasure period,
    data.geometric.localDivergence_integrable period hPeriod, ?_⟩
  have hFinal :=
    data.toFinalObligationsData.certificate period hPeriod source
  exact ⟨hFinal.2.2.1, hFinal.2.2.2.1,
    hFinal.2.2.2.2.1, data.fredholmAlternative period hPeriod⟩

end CanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalFinalData

/-- Marker for the direct-coercive weighted transported-normal endpoint. -/
theorem canonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalDirectCoerciveFinalClosure_available :
    True :=
  trivial

/-- Marker for the preferred graph/direct-coercive endpoint. -/
theorem canonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalGraphDirectCoerciveFinalClosure_available :
    True :=
  trivial

/-- Marker for the corrected weighted transported-normal final endpoint. -/
theorem canonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalFinalClosure_available :
    True :=
  trivial

end
end P0EFTJanusMappingTorusCanonicalPhysicalScalarIntrinsicWaveWeightedTransportedNormalFinalClosure4D
end JanusFormal
