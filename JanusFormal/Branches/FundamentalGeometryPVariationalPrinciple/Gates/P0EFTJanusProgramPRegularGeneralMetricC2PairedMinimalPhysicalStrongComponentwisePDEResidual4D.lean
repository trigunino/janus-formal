import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D

/-! # Componentwise PDE residual bridge for the authentic strong Euler system -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEResidual4D

set_option autoImplicit false
set_option maxHeartbeats 300000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D

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
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

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
variable (measure : Measure (EffectiveQuotient period hPeriod))
variable [IsFiniteMeasure measure]
variable (point : GlobalMinimalPhysicalFieldTangent period hPeriod
  configuration.physical)

/-- One separating residual representation for each authentic physical Euler
sector. Concrete tensorial/distributional realizations can fill this record. -/
structure RegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEDataAt where
  metric : SeparatingPDEResidualRepresentation
    (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricEulerCovectorAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point)
  gauge : SeparatingPDEResidualRepresentation
    (regularGeneralMetricC2PairedMinimalPhysicalStrongGaugeEulerCovectorAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point)
  normal : SeparatingPDEResidualRepresentation
    (regularGeneralMetricC2PairedMinimalPhysicalStrongNormalEulerCovectorAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point)
  diffeomorphismGhost : SeparatingPDEResidualRepresentation
    (regularGeneralMetricC2PairedMinimalPhysicalStrongDiffeomorphismGhostEulerCovectorAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point)
  llAuxMetric : SeparatingPDEResidualRepresentation
    (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAuxMetricEulerCovectorAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point)
  llMeasure : SeparatingPDEResidualRepresentation
    (regularGeneralMetricC2PairedMinimalPhysicalStrongLLMeasureEulerCovectorAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point)
  llField : SeparatingPDEResidualRepresentation
    (regularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldEulerCovectorAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point)
  spinC : SeparatingPDEResidualRepresentation
    (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterEulerCovectorAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point)

/-- Eight concrete strong residual equations. -/
def RegularGeneralMetricC2PairedMinimalPhysicalComponentwiseStrongPDESystemAt
    (pdeData :
      RegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEDataAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point) : Prop :=
  (pdeData.metric.residual = pdeData.metric.zeroResidual ∧
    pdeData.gauge.residual = pdeData.gauge.zeroResidual ∧
    pdeData.normal.residual = pdeData.normal.zeroResidual ∧
    pdeData.diffeomorphismGhost.residual =
      pdeData.diffeomorphismGhost.zeroResidual ∧
    pdeData.llAuxMetric.residual = pdeData.llAuxMetric.zeroResidual ∧
    pdeData.llMeasure.residual = pdeData.llMeasure.zeroResidual ∧
    pdeData.llField.residual = pdeData.llField.zeroResidual) ∧
  pdeData.spinC.residual = pdeData.spinC.zeroResidual

/-- Supplying separating physical representatives turns the authentic Euler
equation into the eight componentwise strong PDE residual equations. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_componentwiseStrongPDE
    (pdeData :
      RegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEDataAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point = 0 ↔
      RegularGeneralMetricC2PairedMinimalPhysicalComponentwiseStrongPDESystemAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point pdeData := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period hPeriod
    configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_eightSectors
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point]
  unfold RegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEulerSystemAt
  unfold RegularGeneralMetricC2PairedMinimalPhysicalComponentwiseStrongPDESystemAt
  rw [separatingPDEResidualRepresentation_covector_eq_zero_iff pdeData.metric]
  rw [separatingPDEResidualRepresentation_covector_eq_zero_iff pdeData.gauge]
  rw [separatingPDEResidualRepresentation_covector_eq_zero_iff pdeData.normal]
  rw [separatingPDEResidualRepresentation_covector_eq_zero_iff
    pdeData.diffeomorphismGhost]
  rw [separatingPDEResidualRepresentation_covector_eq_zero_iff
    pdeData.llAuxMetric]
  rw [separatingPDEResidualRepresentation_covector_eq_zero_iff
    pdeData.llMeasure]
  rw [separatingPDEResidualRepresentation_covector_eq_zero_iff pdeData.llField]
  rw [separatingPDEResidualRepresentation_covector_eq_zero_iff pdeData.spinC]

/-- Gate marker: concrete separating representations suffice to identify the
authentic Euler equation with the componentwise strong PDE system. -/
theorem regular_general_metric_c2_paired_minimal_physical_componentwise_strong_pde_bridge_gate
    (_hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (pdeData :
      RegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEDataAt
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point = 0 ↔
      RegularGeneralMetricC2PairedMinimalPhysicalComponentwiseStrongPDESystemAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point pdeData :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_componentwiseStrongPDE
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point pdeData

end

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEResidual4D
end JanusFormal
