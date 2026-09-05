import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedInteractionActionDerivative4D

/-! # Exact Candidate-A interaction derivative on the minimal physical tangent -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionDerivative4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2ToStrongH1C0Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootJetRigidity4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartInteraction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixCore4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedRelativeMatrixC2Exact4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D
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

private abbrev RelativeCore
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod) :=
  RegularGeneralMetricC2PairedRelativeCore
    period hPeriod plusBase minusBase

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

/-- Pullback of the exact paired interaction derivative to the complete
minimal-physical tangent. -/
def regularGeneralMetricC2PairedMinimalPhysicalInteractionActionDerivative
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
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
    GlobalMinimalPhysicalFieldTangent period hPeriod configuration.physical
      →L[Real] Real := by
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
  let projection := globalMinimalPhysicalPairedRelativeMetricCoreCLM period
    hPeriod configuration data analysis realization plusBase minusBase
  exact (regularGeneralMetricC2PairedInteractionC2ActionDerivative period
      hPeriod plusBase minusBase measure couplings.interactionScale
        couplings.interactionCoefficients (projection point)
        ((globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
          period hPeriod configuration.physical plusBase minusBase point).1
            hPoint)).comp projection

/-- The genuine Candidate-A interaction block has the pulled-back exact
Fréchet derivative at every point of the open paired chart. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_candidateA_hasFDerivAt
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
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
    HasFDerivAt
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure).candidateA
      (regularGeneralMetricC2PairedMinimalPhysicalInteractionActionDerivative
        period hPeriod configuration data analysis realization plusBase
          minusBase measure point hPoint) point := by
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
  let projection := globalMinimalPhysicalPairedRelativeMetricCoreCLM period
    hPeriod configuration data analysis realization plusBase minusBase
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
      (regularGeneralMetricC2PairedMinimalPhysicalInteractionActionDerivative
        period hPeriod configuration data analysis realization plusBase
          minusBase measure point hPoint) point := by
    simpa [regularGeneralMetricC2PairedMinimalPhysicalInteractionActionDerivative,
      projection, Function.comp_def] using hAux
  apply hAux'.congr_of_eventuallyEq
  filter_upwards
    [(regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_isOpen
      period hPeriod configuration data analysis realization plusBase
        minusBase).mem_nhds hPoint] with direction hDirection
  exact regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_candidateA_eq
    period hPeriod configuration.physical couplings data plusBase minusBase
      hBase measure direction hDirection

/-- Explicit integral formula for the genuine Candidate-A first variation. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalInteractionActionDerivative_apply
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
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
    regularGeneralMetricC2PairedMinimalPhysicalInteractionActionDerivative
        period hPeriod configuration data analysis realization plusBase
          minusBase measure point hPoint direction =
      ∫ spacetimePoint,
        (-couplings.interactionScale) * plusBase.volume spacetimePoint *
          matrixSpectralPotentialDerivative couplings.interactionCoefficients
            (c2FiniteMatrixValueAt period hPeriod 4
              (regularGeneralMetricC2PairedRelativeRoot period hPeriod
                plusBase minusBase
                (globalMinimalPhysicalPairedRelativeMetricCoreCLM period
                  hPeriod configuration data analysis realization plusBase
                    minusBase point)) spacetimePoint)
            (c2FiniteMatrixValueAt period hPeriod 4
              (regularGeneralMetricC2PairedRelativeRootDerivative period hPeriod
                plusBase minusBase
                (globalMinimalPhysicalPairedRelativeMetricCoreCLM period
                  hPeriod configuration data analysis realization plusBase
                    minusBase point)
                ((globalMetricPerturbationPairLorentzChartAdmissible_iff_mem_matrixDomain
                  period hPeriod configuration.physical plusBase minusBase
                    point).1 hPoint)
                (globalMinimalPhysicalPairedRelativeMetricCoreCLM period
                  hPeriod configuration data analysis realization plusBase
                    minusBase direction)) spacetimePoint)
        ∂measure := by
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
  letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
  unfold regularGeneralMetricC2PairedMinimalPhysicalInteractionActionDerivative
  simp only [ContinuousLinearMap.comp_apply]
  rw [regularGeneralMetricC2PairedInteractionC2ActionDerivative_apply]

/-- Gate marker: Candidate-A now has an exact full-tangent derivative and an
explicit integrated first variation on the open physical chart. -/
theorem regular_general_metric_c2_paired_minimal_physical_interaction_derivative_gate
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
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
    letI := globalMinimalPhysicalPairedRelativeMetricCoreNormedSpace period
      hPeriod configuration data analysis realization plusBase minusBase
    HasFDerivAt
      (regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
        period hPeriod configuration.physical couplings data plusBase minusBase
          hBase measure).candidateA
      (regularGeneralMetricC2PairedMinimalPhysicalInteractionActionDerivative
        period hPeriod configuration data analysis realization plusBase
          minusBase measure point hPoint) point :=
  regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks_candidateA_hasFDerivAt
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionDerivative4D
end JanusFormal
