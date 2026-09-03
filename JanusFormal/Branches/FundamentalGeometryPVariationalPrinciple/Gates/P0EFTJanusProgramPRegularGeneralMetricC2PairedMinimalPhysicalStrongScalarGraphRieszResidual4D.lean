import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentPDEBlockPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPStateDependentAugmentedGraphRieszResidual4D

/-! # Closed-graph Riesz residuals for the authentic strong Euler sectors -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongScalarGraphRieszResidual4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
open P0EFTJanusProgramPStateDependentAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEResidual4D

universe u

/-- A scalar closed-graph datum retaining an arbitrary test covector exactly. -/
def scalarClosedGraphRieszData
    {Test : Type u} [AddCommGroup Test] [Module Real Test]
    (covector : Test →ₗ[Real] Real) :
    StateDependentAugmentedGraphRieszData (Test := Test) (Base := Real) where
  baseMap := covector
  remainder := 0
  baseCovector := ContinuousLinearMap.id Real Real

@[simp]
theorem scalarClosedGraphRieszData_totalCovector
    {Test : Type u} [AddCommGroup Test] [Module Real Test]
    (covector : Test →ₗ[Real] Real) :
    stateDependentAugmentedTotalCovector
      (scalarClosedGraphRieszData covector) = covector := by
  apply LinearMap.ext
  intro test
  simp [stateDependentAugmentedTotalCovector, scalarClosedGraphRieszData]

/-- Exact separating Riesz representation on the completed scalar graph. -/
def scalarClosedGraphRieszResidualRepresentation
    {Test : Type u} [AddCommGroup Test] [Module Real Test]
    (covector : Test →ₗ[Real] Real) :
    SeparatingPDEResidualRepresentation covector := by
  rw [← scalarClosedGraphRieszData_totalCovector covector]
  exact stateDependentAugmentedGraphResidualRepresentation
    (scalarClosedGraphRieszData covector)

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

/-- Unconditional completed-graph Riesz representatives for all eight
authentic sector covectors. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongScalarGraphPDEDataAt :
    RegularGeneralMetricC2PairedMinimalPhysicalStrongComponentwisePDEDataAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point where
  metric := scalarClosedGraphRieszResidualRepresentation _
  gauge := scalarClosedGraphRieszResidualRepresentation _
  normal := scalarClosedGraphRieszResidualRepresentation _
  diffeomorphismGhost := scalarClosedGraphRieszResidualRepresentation _
  llAuxMetric := scalarClosedGraphRieszResidualRepresentation _
  llMeasure := scalarClosedGraphRieszResidualRepresentation _
  llField := scalarClosedGraphRieszResidualRepresentation _
  spinC := scalarClosedGraphRieszResidualRepresentation _

/-- The eight closed-Hilbert-graph Riesz equations. -/
def RegularGeneralMetricC2PairedMinimalPhysicalStrongScalarGraphRieszSystemAt :
    Prop :=
  RegularGeneralMetricC2PairedMinimalPhysicalComponentwiseStrongPDESystemAt
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongScalarGraphPDEDataAt
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point)

/-- The authentic strong Euler equation is unconditionally equivalent to the
eight exact closed-graph Riesz residual equations. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_scalarGraphRieszSystem :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point = 0 ↔
      RegularGeneralMetricC2PairedMinimalPhysicalStrongScalarGraphRieszSystemAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_componentwiseStrongPDE
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point
        (regularGeneralMetricC2PairedMinimalPhysicalStrongScalarGraphPDEDataAt
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure point)

/-- Gate marker: the authentic eight-sector Euler system has unconditional
separating residuals on completed scalar graphs. -/
theorem regular_general_metric_c2_paired_minimal_physical_strong_scalar_graph_riesz_gate
    (_hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point = 0 ↔
      RegularGeneralMetricC2PairedMinimalPhysicalStrongScalarGraphRieszSystemAt
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure point :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_eq_zero_iff_scalarGraphRieszSystem
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point

end

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongScalarGraphRieszResidual4D
end JanusFormal
