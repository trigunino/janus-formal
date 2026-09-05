import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricEinsteinHilbertTotalEuler4D

/-! # Joint metric--gauge Maxwell derivatives in the strong chart -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellDerivative4D

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
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
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
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedGaugeCoefficientMaxwellAction4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

attribute [local instance 1900]
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedAddCommGroup
  P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D.relativeCoreNormedSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

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

local instance c2ScalarNormedAddCommGroup :
    NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance c2ScalarNormedSpace :
    NormedSpace Real (C2Scalar period hPeriod) := inferInstance

/-- Pullback of the scaled plus Maxwell derivative through the joint strong
metric--gauge projection. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellPlusActionDerivative
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
  let projection := globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM
    period hPeriod configuration data analysis realization plusBase minusBase
  exact (fderiv Real
    (fun core => couplings.plusMaxwellScale *
      regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction period hPeriod
        configuration.physical plusBase minusBase measure core)
    (projection point)).comp projection

/-- Pullback of the scaled minus Maxwell derivative through the same joint
strong metric--gauge projection. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellMinusActionDerivative
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
  let projection := globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM
    period hPeriod configuration data analysis realization plusBase minusBase
  exact (fderiv Real
    (fun core => couplings.minusMaxwellScale *
      regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction period hPeriod
        configuration.physical plusBase minusBase measure core)
    (projection point)).comp projection

theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellPlus_strong_hasFDerivAt
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
          measure).maxwellPlus
      (regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellPlusActionDerivative
        period hPeriod configuration data analysis realization plusBase
          minusBase measure point) point := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let projection := globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM
    period hPeriod configuration data analysis realization plusBase minusBase
  let outer := fun core => couplings.plusMaxwellScale *
    regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction period hPeriod
      configuration.physical plusBase minusBase measure core
  have hTarget : projection point ∈
      regularGeneralMetricC2PairedMetricGaugeMaxwellDomain period hPeriod
        plusBase minusBase := ⟨
    (globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
      period hPeriod configuration.physical plusBase minusBase point).1 hPoint,
    Set.mem_univ _⟩
  have hOuter : HasFDerivAt outer (fderiv Real outer (projection point))
      (projection point) :=
    (((contDiffOn_const.mul
      (regularGeneralMetricC2PairedPlusFixedVolumeMaxwellAction_contDiffOn_two
        period hPeriod configuration.physical plusBase minusBase measure)).contDiffAt
          (((regularGeneralMetricC2PairedLorentzMatrixDomain_isOpen period hPeriod
            plusBase minusBase).prod isOpen_univ).mem_nhds hTarget)
        ).differentiableAt (by norm_num)).hasFDerivAt
  have hAux := hOuter.comp point projection.hasFDerivAt
  have hAux' : HasFDerivAt (fun direction => outer (projection direction))
      (regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellPlusActionDerivative
        period hPeriod configuration data analysis realization plusBase
          minusBase measure point) point := by
    simpa [regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellPlusActionDerivative,
      outer, projection, Function.comp_def] using hAux
  apply hAux'.congr_of_eventuallyEq
  filter_upwards
    [(regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
      period hPeriod configuration data analysis realization plusBase
        minusBase).mem_nhds hPoint] with direction hDirection
  exact regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellPlus_eq
    period hPeriod configuration.physical couplings data plusBase minusBase
      hBase measure direction hDirection

theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellMinus_strong_hasFDerivAt
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
          measure).maxwellMinus
      (regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellMinusActionDerivative
        period hPeriod configuration data analysis realization plusBase
          minusBase measure point) point := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let projection := globalMinimalPhysicalPairedMetricGaugeLLStrongOldCoreCLM
    period hPeriod configuration data analysis realization plusBase minusBase
  let outer := fun core => couplings.minusMaxwellScale *
    regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction period hPeriod
      configuration.physical plusBase minusBase measure core
  have hTarget : projection point ∈
      regularGeneralMetricC2PairedMetricGaugeMaxwellDomain period hPeriod
        plusBase minusBase := ⟨
    (globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
      period hPeriod configuration.physical plusBase minusBase point).1 hPoint,
    Set.mem_univ _⟩
  have hOuter : HasFDerivAt outer (fderiv Real outer (projection point))
      (projection point) :=
    (((contDiffOn_const.mul
      (regularGeneralMetricC2PairedMinusFixedVolumeMaxwellAction_contDiffOn_two
        period hPeriod configuration.physical plusBase minusBase measure)).contDiffAt
          (((regularGeneralMetricC2PairedLorentzMatrixDomain_isOpen period hPeriod
            plusBase minusBase).prod isOpen_univ).mem_nhds hTarget)
        ).differentiableAt (by norm_num)).hasFDerivAt
  have hAux := hOuter.comp point projection.hasFDerivAt
  have hAux' : HasFDerivAt (fun direction => outer (projection direction))
      (regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellMinusActionDerivative
        period hPeriod configuration data analysis realization plusBase
          minusBase measure point) point := by
    simpa [regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellMinusActionDerivative,
      outer, projection, Function.comp_def] using hAux
  apply hAux'.congr_of_eventuallyEq
  filter_upwards
    [(regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
      period hPeriod configuration data analysis realization plusBase
        minusBase).mem_nhds hPoint] with direction hDirection
  exact regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellMinus_eq
    period hPeriod configuration.physical couplings data plusBase minusBase
      hBase measure direction hDirection

theorem regularGeneralMetricC2PairedMinimalPhysicalMaxwellPlus_actionGradient_eq_strongDerivative
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
            measure).maxwellPlus point direction =
      regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellPlusActionDerivative
        period hPeriod configuration data analysis realization plusBase
          minusBase measure point direction := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  unfold actionGradient
  rw [(regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellPlus_strong_hasFDerivAt
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint).fderiv]

theorem regularGeneralMetricC2PairedMinimalPhysicalMaxwellMinus_actionGradient_eq_strongDerivative
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
            measure).maxwellMinus point direction =
      regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellMinusActionDerivative
        period hPeriod configuration data analysis realization plusBase
          minusBase measure point direction := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  unfold actionGradient
  rw [(regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellMinus_strong_hasFDerivAt
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint).fderiv]

/-- Gate marker: both genuine Maxwell blocks have exact joint metric--gauge
derivatives in the authentic strong chart. -/
theorem regular_general_metric_c2_paired_minimal_physical_strong_maxwell_derivative_gate
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
            measure).maxwellPlus
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellPlusActionDerivative
          period hPeriod configuration data analysis realization plusBase
            minusBase measure point) point ∧
      HasFDerivAt
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks period
          hPeriod configuration.physical couplings data plusBase minusBase hBase
            measure).maxwellMinus
        (regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellMinusActionDerivative
          period hPeriod configuration data analysis realization plusBase
            minusBase measure point) point := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  exact ⟨
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellPlus_strong_hasFDerivAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint,
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_maxwellMinus_strong_hasFDerivAt
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure point hPoint⟩

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellDerivative4D
end JanusFormal
