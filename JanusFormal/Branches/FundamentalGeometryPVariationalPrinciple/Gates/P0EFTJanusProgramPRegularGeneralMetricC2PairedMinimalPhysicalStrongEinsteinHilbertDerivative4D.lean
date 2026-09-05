import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricInteractionTotalEuler4D

/-! # Fixed-volume Einstein--Hilbert derivatives in the strong chart -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedFixedVolumeEinsteinHilbertC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedEinsteinHilbertActionBridge4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance 1900]
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedAddCommGroup
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Pullback of the plus fixed-volume Einstein--Hilbert derivative through the
metric projection of the canonical strong metric/gauge/LL graph topology. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertPlusActionDerivative
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical
      →L[Real] Real := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let projection := globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM
    period hPeriod configuration data analysis realization plusBase minusBase
  exact (fderiv Real
    (regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction period
      hPeriod plusBase minusBase measure couplings.plusEinstein)
    (projection point)).comp projection

/-- Pullback of the minus fixed-volume Einstein--Hilbert derivative through the
same strong metric projection. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertMinusActionDerivative
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical
      →L[Real] Real := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let projection := globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM
    period hPeriod configuration data analysis realization plusBase minusBase
  exact (fderiv Real
    (regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction period
      hPeriod plusBase minusBase measure couplings.minusEinstein)
    (projection point)).comp projection

theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertPlus_strong_hasFDerivAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    HasFDerivAt
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks period
        hPeriod configuration.physical couplings data plusBase minusBase hBase
          measure).einsteinHilbertPlus
      (regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertPlusActionDerivative
        period hPeriod configuration data analysis realization plusBase
          minusBase measure point) point := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let projection := globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM
    period hPeriod configuration data analysis realization plusBase minusBase
  have hCore : projection point ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase
        minusBase :=
    (globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
      period hPeriod configuration.physical plusBase minusBase point).1 hPoint
  have hAction : HasFDerivAt
      (regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction period
        hPeriod plusBase minusBase measure couplings.plusEinstein)
      (fderiv Real
        (regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction period
          hPeriod plusBase minusBase measure couplings.plusEinstein)
        (projection point)) (projection point) :=
    (((regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction_contDiffOn
      period hPeriod plusBase minusBase measure couplings.plusEinstein).contDiffAt
        ((regularGeneralMetricC2PairedLorentzMatrixDomain_isOpen period hPeriod
          plusBase minusBase).mem_nhds hCore)).differentiableAt
            (by norm_num)).hasFDerivAt
  have hAux := hAction.comp point projection.hasFDerivAt
  have hAux' : HasFDerivAt
      (fun direction =>
        regularGeneralMetricC2PairedPlusFixedVolumeEinsteinHilbertAction period
          hPeriod plusBase minusBase measure couplings.plusEinstein
            (projection direction))
      (regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertPlusActionDerivative
        period hPeriod configuration data analysis realization plusBase
          minusBase measure point) point := by
    simpa [regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertPlusActionDerivative,
      projection, Function.comp_def] using hAux
  apply hAux'.congr_of_eventuallyEq
  filter_upwards
    [(regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
      period hPeriod configuration data analysis realization plusBase
        minusBase).mem_nhds hPoint] with direction hDirection
  exact regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertPlus_eq
    period hPeriod configuration.physical couplings data plusBase minusBase
      hBase measure direction hDirection

theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertMinus_strong_hasFDerivAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    HasFDerivAt
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks period
        hPeriod configuration.physical couplings data plusBase minusBase hBase
          measure).einsteinHilbertMinus
      (regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertMinusActionDerivative
        period hPeriod configuration data analysis realization plusBase
          minusBase measure point) point := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let projection := globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM
    period hPeriod configuration data analysis realization plusBase minusBase
  have hCore : projection point ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase
        minusBase :=
    (globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
      period hPeriod configuration.physical plusBase minusBase point).1 hPoint
  have hAction : HasFDerivAt
      (regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction period
        hPeriod plusBase minusBase measure couplings.minusEinstein)
      (fderiv Real
        (regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction period
          hPeriod plusBase minusBase measure couplings.minusEinstein)
        (projection point)) (projection point) :=
    (((regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction_contDiffOn
      period hPeriod plusBase minusBase measure couplings.minusEinstein).contDiffAt
        ((regularGeneralMetricC2PairedLorentzMatrixDomain_isOpen period hPeriod
          plusBase minusBase).mem_nhds hCore)).differentiableAt
            (by norm_num)).hasFDerivAt
  have hAux := hAction.comp point projection.hasFDerivAt
  have hAux' : HasFDerivAt
      (fun direction =>
        regularGeneralMetricC2PairedMinusFixedVolumeEinsteinHilbertAction period
          hPeriod plusBase minusBase measure couplings.minusEinstein
            (projection direction))
      (regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertMinusActionDerivative
        period hPeriod configuration data analysis realization plusBase
          minusBase measure point) point := by
    simpa [regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertMinusActionDerivative,
      projection, Function.comp_def] using hAux
  apply hAux'.congr_of_eventuallyEq
  filter_upwards
    [(regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
      period hPeriod configuration data analysis realization plusBase
        minusBase).mem_nhds hPoint] with direction hDirection
  exact regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertMinus_eq
    period hPeriod configuration.physical couplings data plusBase minusBase
      hBase measure direction hDirection

theorem regularGeneralMetricC2PairedMinimalPhysicalEinsteinHilbertPlus_actionGradient_eq_strongDerivative
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    actionGradient
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks period
          hPeriod configuration.physical couplings data plusBase minusBase hBase
            measure).einsteinHilbertPlus point direction =
      regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertPlusActionDerivative
        period hPeriod configuration data analysis realization plusBase
          minusBase measure point direction := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  unfold actionGradient
  rw [(regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertPlus_strong_hasFDerivAt
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint).fderiv]

theorem regularGeneralMetricC2PairedMinimalPhysicalEinsteinHilbertMinus_actionGradient_eq_strongDerivative
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    actionGradient
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks period
          hPeriod configuration.physical couplings data plusBase minusBase hBase
            measure).einsteinHilbertMinus point direction =
      regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertMinusActionDerivative
        period hPeriod configuration data analysis realization plusBase
          minusBase measure point direction := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  unfold actionGradient
  rw [(regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertMinus_strong_hasFDerivAt
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint).fderiv]

/-- Gate marker: both actual Einstein--Hilbert blocks have their strong-chart
fixed-volume derivatives, with no abstract action gradient left. -/
theorem regular_general_metric_c2_paired_minimal_physical_strong_einstein_hilbert_derivative_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    HasFDerivAt
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks period
          hPeriod configuration.physical couplings data plusBase minusBase hBase
            measure).einsteinHilbertPlus
        (regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertPlusActionDerivative
          period hPeriod configuration data analysis realization plusBase
            minusBase measure point) point ∧
      HasFDerivAt
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks period
          hPeriod configuration.physical couplings data plusBase minusBase hBase
            measure).einsteinHilbertMinus
        (regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertMinusActionDerivative
          period hPeriod configuration data analysis realization plusBase
            minusBase measure point) point := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  exact ⟨
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertPlus_strong_hasFDerivAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint,
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_einsteinHilbertMinus_strong_hasFDerivAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint⟩

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertDerivative4D
end JanusFormal
