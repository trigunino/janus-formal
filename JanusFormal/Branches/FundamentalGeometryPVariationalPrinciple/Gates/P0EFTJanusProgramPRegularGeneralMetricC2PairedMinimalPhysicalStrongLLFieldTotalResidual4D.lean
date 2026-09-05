import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCTotalResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLTotalEuler4D

/-! # Pointwise total LL-field residual in the canonical physical system -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldTotalResidual4D

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLGeometricStokes4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLStrongEquation4D
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldWeakResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLTotalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMeasureResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCTotalResidual4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl

local instance intrinsicCanonicalLorentzVolumeMeasureIsFinite :
    IsFiniteMeasure (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance canonicalThroatMeasureIsFinite :
    IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

local instance canonicalThroatMeasureIsOpenPos :
    Measure.IsOpenPosMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isOpenPosMeasure period hPeriod

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) := inferInstance

section

variable {couplings : GlobalCandidateAActionCouplings}
variable {NonNullFace NullFace : Type*}
variable [Fintype NonNullFace] [Fintype NullFace]
variable (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
variable (data : GlobalCandidateAActionData period hPeriod
  configuration.physical couplings NonNullFace NullFace)
variable (analysis : GlobalAnalysisData period hPeriod configuration.physical)
variable (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
  period hPeriod couplings.matterMassSquared)
variable (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
variable (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
  period hPeriod plusBase minusBase)
variable (point : GlobalMinimalPhysicalFieldTangent period hPeriod
  configuration.physical)

/-- The authentic pointwise residual of the total LL-field covector. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldTotalResidual :
    SmoothThroatField period hPeriod LLFieldFiber :=
  ptSymmetricStrongDifferentialLLEulerField period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (smoothLLStrongRegularity period hPeriod
      (canonicalDivergenceFreeLLFrame period hPeriod))
    (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
      configuration.physical point)

/-- Exact Stokes reduction of the complete LL-field Euler covector to the
pointwise strong residual pairing. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongLLField_eq_totalResidualPairing
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldTest
      period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator period
        hPeriod configuration data analysis realization plusBase minusBase hBase
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldDirection period
          hPeriod configuration.physical test) =
      ∫ throatPoint,
        inner Real
          (regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldTotalResidual
            period hPeriod configuration point throatPoint)
          (test throatPoint)
        ∂intrinsicCanonicalThroatVolumeMeasure period hPeriod := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongLLField_eq_LLBlock
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point hPoint test]
  rw [regular_general_metric_c2_paired_minimal_physical_strong_LL_field_weak_residual_gate
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point hPoint test]
  rw [weakLLEulerOperator_apply]
  let fields := regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period
    hPeriod configuration.physical point
  let regularity := smoothLLStrongRegularity period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
  let contract := canonicalDivergenceFreeLLFrameGeometricStokesContract period
    hPeriod fields regularity
  have hIPP :=
    (contract.toStrongLLIntegrationByParts period hPeriod).integrationByParts test
  have hFlux :
      (contract.toStrongLLIntegrationByParts period hPeriod).boundaryFlux test = 0 := by
    simpa [ptSymmetricLLBoundaryFlux] using
      contract.satisfiesNaturalBoundaryCondition period hPeriod test
  rw [hFlux, add_zero] at hIPP
  simpa [fields, regularity,
    regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldTotalResidual] using hIPP

def regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldTotalResidualRepresentation
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    SeparatingPDEResidualRepresentation
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let residual :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldTotalResidual period
      hPeriod configuration point
  exact
    { Residual := SmoothThroatField period hPeriod LLFieldFiber
      zeroResidual := 0
      residual := residual
      pairing := fun value test ↦
        ∫ throatPoint, inner Real (value throatPoint) (test throatPoint)
          ∂intrinsicCanonicalThroatVolumeMeasure period hPeriod
      represents := by
        intro test
        change
          regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
              period hPeriod configuration data analysis realization plusBase
                minusBase hBase
                  (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point
              (regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldDirection
                period hPeriod configuration.physical test) = _
        exact
          regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongLLField_eq_totalResidualPairing
            period hPeriod configuration data analysis realization plusBase
              minusBase hBase point hPoint test
      separates :=
        smoothThroatField_pairing_detects_zero_field period hPeriod residual }

def regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldSpinCTotalPDEDataAt
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (hPlus : couplings.plusMaxwellScale ≠ 0)
    (hMinus : couplings.minusMaxwellScale ≠ 0) :
    RegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEDataAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point :=
  { regularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMeasureCanonicalMaxwellSpinCTotalPDEDataAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase point hPoint hPlus hMinus with
    llField :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldTotalResidualRepresentation
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase point hPoint }

def RegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldSpinCTotalSystemAt
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (hPlus : couplings.plusMaxwellScale ≠ 0)
    (hMinus : couplings.minusMaxwellScale ≠ 0) : Prop :=
  RegularGeneralMetricC2PairedMinimalPhysicalComponentwiseStrongPDESystemAt
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldSpinCTotalPDEDataAt
          period hPeriod configuration data analysis realization plusBase minusBase
            hBase point hPoint hPlus hMinus)

theorem regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldEquation_iff_pointwise
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (hPlus : couplings.plusMaxwellScale ≠ 0)
    (hMinus : couplings.minusMaxwellScale ≠ 0) :
    let pdeData :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldSpinCTotalPDEDataAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase point hPoint hPlus hMinus
    pdeData.llField.residual = pdeData.llField.zeroResidual ↔
      SatisfiesPTSymmetricStrongDifferentialLLEquation period hPeriod
        (canonicalDivergenceFreeLLFrame period hPeriod)
        (smoothLLStrongRegularity period hPeriod
          (canonicalDivergenceFreeLLFrame period hPeriod))
        (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
          configuration.physical point) := by
  change
    regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldTotalResidual period
        hPeriod configuration point = 0 ↔ _
  constructor
  · intro hZero throatPoint
    have hApply := congrArg
      (fun value : SmoothThroatField period hPeriod LLFieldFiber ↦
        value throatPoint) hZero
    simpa [regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldTotalResidual]
      using hApply
  · intro hPointwise
    apply SmoothThroatField.ext period hPeriod LLFieldFiber
    exact hPointwise

theorem regular_general_metric_c2_paired_minimal_physical_strong_LL_field_total_residual_gate
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (hPlus : couplings.plusMaxwellScale ≠ 0)
    (hMinus : couplings.minusMaxwellScale ≠ 0) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator period
        hPeriod configuration data analysis realization plusBase minusBase hBase
          (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point = 0 ↔
      RegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldSpinCTotalSystemAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase point hPoint hPlus hMinus :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_componentwiseStrongPDE
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldSpinCTotalPDEDataAt
          period hPeriod configuration data analysis realization plusBase minusBase
            hBase point hPoint hPlus hMinus)

end
end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldTotalResidual4D
end JanusFormal
