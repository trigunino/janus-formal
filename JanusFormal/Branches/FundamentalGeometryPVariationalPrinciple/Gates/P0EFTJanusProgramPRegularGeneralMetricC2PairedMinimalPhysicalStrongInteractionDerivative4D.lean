import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricAffineTarget4D

/-! # Exact Candidate-A interaction derivative in the authentic strong chart -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongInteractionDerivative4D

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
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricTotalEulerReduction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricAffineTarget4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeRootSpectralDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2MatrixSpectralPotential4D
open P0EFTJanusMatrixInteractionFrechetNoether
open P0EFTJanusReciprocalBimetricPotential

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

/-- Pullback of the exact interaction derivative through the metric projection
of the canonical strong metric/gauge/LL graph topology. -/
def regularGeneralMetricC2PairedMinimalPhysicalStrongInteractionActionDerivative
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
  exact (regularGeneralMetricC2PairedInteractionC2ActionDerivative period
      hPeriod plusBase minusBase measure couplings.interactionScale
        couplings.interactionCoefficients (projection point)
        ((globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
          period hPeriod configuration.physical plusBase minusBase point).1
            hPoint)).comp projection

/-- The genuine Candidate-A block has the exact interaction derivative in the
same strong topology used by the total Euler operator. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_candidateA_strong_hasFDerivAt
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
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure).candidateA
      (regularGeneralMetricC2PairedMinimalPhysicalStrongInteractionActionDerivative
        period hPeriod configuration data analysis realization plusBase
          minusBase measure point hPoint) point := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let projection := globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM
    period hPeriod configuration data analysis realization plusBase minusBase
  have hCore : projection point ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod
        plusBase minusBase :=
    (globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
      period hPeriod configuration.physical plusBase minusBase point).1 hPoint
  have hAux := HasFDerivAt.comp
    (f := fun direction => projection direction)
    (g := regularGeneralMetricC2PairedInteractionC2Action period hPeriod
      plusBase minusBase measure couplings.interactionScale
        couplings.interactionCoefficients)
    point
    (regularGeneralMetricC2PairedInteractionC2Action_hasFDerivAt period hPeriod
      plusBase minusBase measure couplings.interactionScale
        couplings.interactionCoefficients (projection point) hCore)
    projection.hasFDerivAt
  have hAux' : HasFDerivAt
      (fun direction =>
        regularGeneralMetricC2PairedInteractionC2Action period hPeriod
          plusBase minusBase measure couplings.interactionScale
            couplings.interactionCoefficients (projection direction))
      (regularGeneralMetricC2PairedMinimalPhysicalStrongInteractionActionDerivative
        period hPeriod configuration data analysis realization plusBase
          minusBase measure point hPoint) point := by
    simpa [regularGeneralMetricC2PairedMinimalPhysicalStrongInteractionActionDerivative,
      projection, Function.comp_def] using hAux
  apply hAux'.congr_of_eventuallyEq
  filter_upwards
    [(regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
      period hPeriod configuration data analysis realization plusBase
        minusBase).mem_nhds hPoint] with direction hDirection
  exact regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_candidateA_eq
    period hPeriod configuration.physical couplings data plusBase minusBase
      hBase measure direction hDirection

/-- The abstract action gradient used by the total strong Euler operator is
exactly the concrete pulled-back interaction covector. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalCandidateA_actionGradient_eq_strongInteractionDerivative
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
        configuration.physical plusBase minusBase)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    actionGradient
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure).candidateA point direction =
      regularGeneralMetricC2PairedMinimalPhysicalStrongInteractionActionDerivative
        period hPeriod configuration data analysis realization plusBase
          minusBase measure point hPoint direction := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  unfold actionGradient
  rw [(regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_candidateA_strong_hasFDerivAt
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint).fderiv]

/-- Explicit integral formula for the strong-chart interaction covector. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongInteractionActionDerivative_apply
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
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (direction : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    let projection := globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM
      period hPeriod configuration data analysis realization plusBase minusBase
    regularGeneralMetricC2PairedMinimalPhysicalStrongInteractionActionDerivative
        period hPeriod configuration data analysis realization plusBase
          minusBase measure point hPoint direction =
      ∫ spacetimePoint,
        (-couplings.interactionScale) * plusBase.volume spacetimePoint *
          matrixSpectralPotentialDerivative couplings.interactionCoefficients
            (c2FiniteMatrixValueAt period hPeriod 4
              (regularGeneralMetricC2PairedRelativeRoot period hPeriod
                plusBase minusBase (projection point)) spacetimePoint)
            (c2FiniteMatrixValueAt period hPeriod 4
              (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod
                plusBase minusBase (projection point)
                ((globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
                  period hPeriod configuration.physical plusBase minusBase
                    point).1 hPoint)
                (projection direction)) spacetimePoint)
        ∂measure := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  unfold regularGeneralMetricC2PairedMinimalPhysicalStrongInteractionActionDerivative
  simp only [ContinuousLinearMap.comp_apply]
  rw [regularGeneralMetricC2PairedInteractionC2ActionDerivative_apply]

/-- On a pure strong metric test the Candidate-A block is the explicit
spectral interaction integral. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalCandidateA_actionGradient_strongMetric_eq_integral
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
        configuration.physical plusBase minusBase)
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    let projection := globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM
      period hPeriod configuration data analysis realization plusBase minusBase
    let direction :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
        hPeriod configuration.physical test
    actionGradient
        (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
          period hPeriod configuration.physical couplings data plusBase minusBase
            hBase measure).candidateA point direction =
      ∫ spacetimePoint,
        (-couplings.interactionScale) * plusBase.volume spacetimePoint *
          matrixSpectralPotentialDerivative couplings.interactionCoefficients
            (c2FiniteMatrixValueAt period hPeriod 4
              (regularGeneralMetricC2PairedRelativeRoot period hPeriod
                plusBase minusBase (projection point)) spacetimePoint)
            (c2FiniteMatrixValueAt period hPeriod 4
              (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod
                plusBase minusBase (projection point)
                ((globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
                  period hPeriod configuration.physical plusBase minusBase
                    point).1 hPoint)
                (projection direction)) spacetimePoint)
        ∂measure := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  dsimp only
  rw [regularGeneralMetricC2PairedMinimalPhysicalCandidateA_actionGradient_eq_strongInteractionDerivative
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint]
  exact regularGeneralMetricC2PairedMinimalPhysicalStrongInteractionActionDerivative_apply
    period hPeriod configuration data analysis realization plusBase minusBase
      measure point hPoint
      (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
        hPeriod configuration.physical test)

/-- The plus component of the strong interaction test core is exactly the
completed C² lift of `test.plus`. -/
@[simp] theorem regularGeneralMetricC2PairedMinimalPhysicalStrongInteractionMetricCore_plus
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
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    (globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
      configuration data analysis realization plusBase minusBase
      (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
        hPeriod configuration.physical test)).2.1 =
      regularGeneralMetricC2VariationMatrix period hPeriod plusBase
        (test .plus) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM_apply,
    globalMinimalPhysicalPairedRelativeMetricCoreLinearMap_plus,
    regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection_fullMetricPerturbation]

/-- The cross component is the fixed-plus lift of `test.minus - test.plus`. -/
@[simp] theorem regularGeneralMetricC2PairedMinimalPhysicalStrongInteractionMetricCore_cross
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
    (test : GlobalMinimalPhysicalMetricTest period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    (globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM period hPeriod
      configuration data analysis realization plusBase minusBase
      (regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
        hPeriod configuration.physical test)).2.2 =
      regularGeneralMetricC2VariationMatrix period hPeriod plusBase
          (test .minus) -
        regularGeneralMetricC2VariationMatrix period hPeriod plusBase
          (test .plus) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [globalMinimalPhysicalPairedMetricGaugeLLStrongMetricCLM_apply,
    globalMinimalPhysicalPairedRelativeMetricCoreLinearMap_cross,
    regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection_fullMetricPerturbation]

/-- Gate marker: the previously abstract Candidate-A term in the total strong
metric equation is now its exact spectral integral on arbitrary metric tests. -/
theorem regular_general_metric_c2_paired_minimal_physical_strong_interaction_derivative_gate
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
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure).candidateA
      (regularGeneralMetricC2PairedMinimalPhysicalStrongInteractionActionDerivative
        period hPeriod configuration data analysis realization plusBase
          minusBase measure point hPoint) point :=
  regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_candidateA_strong_hasFDerivAt
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongInteractionDerivative4D
end JanusFormal
