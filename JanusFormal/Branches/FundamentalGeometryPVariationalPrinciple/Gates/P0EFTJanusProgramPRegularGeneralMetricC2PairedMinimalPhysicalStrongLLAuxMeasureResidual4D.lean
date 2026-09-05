import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCanonicalVariationalResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMeasureTotalEuler4D

/-! # Pointwise LL auxiliary and measure residuals in the strong system -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMeasureResidual4D

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
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMeasureTotalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeCanonicalVariationalResidual4D

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

theorem smoothThroatField_pairing_detects_zero_field
    {Fiber : Type*} [NormedAddCommGroup Fiber] [InnerProductSpace Real Fiber]
    (residual : SmoothThroatField period hPeriod Fiber) :
    (∀ direction : SmoothThroatField period hPeriod Fiber,
        (∫ point, inner Real (residual point) (direction point)
          ∂intrinsicCanonicalThroatVolumeMeasure period hPeriod) = 0) ↔
      residual = 0 := by
  rw [smoothThroatField_pairing_detects_pointwise_zero period hPeriod residual
    (intrinsicCanonicalThroatVolumeMeasure period hPeriod)]
  constructor
  · intro hPointwise
    apply SmoothThroatField.ext period hPeriod Fiber
    exact hPointwise
  · intro hZero point
    rw [hZero]
    rfl

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

def regularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMetricResidualRepresentation
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    SeparatingPDEResidualRepresentation
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMetricEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let residual := ptSymmetricLLAuxMetricStrongResidual period hPeriod
    (canonicalDivergenceFreeLLFrame period hPeriod)
    (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
      configuration.physical point)
  exact
    { Residual := SmoothThroatField period hPeriod LLMetricFiber
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
              (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMetricDirection
                period hPeriod configuration.physical test) = _
        exact
          regularGeneralMetricC2PairedMinimalPhysicalTotalEuler_pureLLAuxMetric_eq_pairing
            period hPeriod configuration data analysis realization plusBase
              minusBase hBase
                (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point
                  hPoint test
      separates :=
        smoothThroatField_pairing_detects_zero_field period hPeriod residual }

def regularGeneralMetricC2PairedMinimalPhysicalStrongLLMeasureResidualRepresentation
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    SeparatingPDEResidualRepresentation
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLMeasureEulerCovectorAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let residual := llMeasureStrongResidual period hPeriod
    (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
      configuration.physical point)
  exact
    { Residual := SmoothThroatField period hPeriod Real
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
              (regularGeneralMetricC2PairedMinimalPhysicalStrongLLMeasureDirection
                period hPeriod configuration.physical test) = _
        exact
          regularGeneralMetricC2PairedMinimalPhysicalTotalEuler_pureLLMeasure_eq_pairing
            period hPeriod configuration data analysis realization plusBase
              minusBase hBase
                (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point
                  hPoint test
      separates :=
        smoothThroatField_pairing_detects_zero_field period hPeriod residual }

/-- Component data with both remaining LL algebraic residuals made pointwise. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMeasureCanonicalMaxwellPDEDataAt
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (hPlus : couplings.plusMaxwellScale ≠ 0)
    (hMinus : couplings.minusMaxwellScale ≠ 0) :
    RegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEDataAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point :=
  { regularGeneralMetricC2PairedMinimalPhysicalStrongCanonicalVariationalMaxwellPDEDataAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase point hPoint hPlus hMinus with
    llAuxMetric :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMetricResidualRepresentation
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase point hPoint
    llMeasure :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongLLMeasureResidualRepresentation
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase point hPoint }

def RegularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMeasureCanonicalMaxwellSystemAt
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (hPlus : couplings.plusMaxwellScale ≠ 0)
    (hMinus : couplings.minusMaxwellScale ≠ 0) : Prop :=
  RegularGeneralMetricC2PairedMinimalPhysicalComponentwiseStrongPDESystemAt
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMeasureCanonicalMaxwellPDEDataAt
          period hPeriod configuration data analysis realization plusBase minusBase
            hBase point hPoint hPlus hMinus)

theorem regular_general_metric_c2_paired_minimal_physical_strong_LL_aux_measure_residual_gate
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
      RegularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMeasureCanonicalMaxwellSystemAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase point hPoint hPlus hMinus :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_componentwiseStrongPDE
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMeasureCanonicalMaxwellPDEDataAt
          period hPeriod configuration data analysis realization plusBase minusBase
            hBase point hPoint hPlus hMinus)

end
end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMeasureResidual4D
end JanusFormal
