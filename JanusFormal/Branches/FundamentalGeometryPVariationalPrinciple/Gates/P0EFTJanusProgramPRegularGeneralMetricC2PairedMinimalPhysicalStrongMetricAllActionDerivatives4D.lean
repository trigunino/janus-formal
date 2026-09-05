import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellDerivative4D

/-! # Complete action derivatives in the total strong metric equation -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricAllActionDerivatives4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff
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
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricTotalEulerReduction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongInteractionDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellDerivative4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricEinsteinHilbertTotalEuler4D

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

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

/-- The total metric first variation is the sum of four concrete pulled-back
covectors: Candidate-A, plus/minus gravity, and plus/minus Maxwell. -/
theorem regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongMetric_eq_allActionDerivatives
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
    let direction :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
        hPeriod configuration.physical test
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point direction =
      ((((regularGeneralMetricC2PairedMinimalPhysicalStrongInteractionActionDerivative
              period hPeriod configuration data analysis realization plusBase
                minusBase measure point hPoint direction +
            regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertPlusActionDerivative
              period hPeriod configuration data analysis realization plusBase
                minusBase measure point direction) +
          regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertMinusActionDerivative
            period hPeriod configuration data analysis realization plusBase
              minusBase measure point direction) +
        regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellPlusActionDerivative
          period hPeriod configuration data analysis realization plusBase
            minusBase measure point direction) +
      regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellMinusActionDerivative
        period hPeriod configuration data analysis realization plusBase
          minusBase measure point direction) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  dsimp only
  rw [regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongMetric_eq_explicitInteractionEinsteinHilbertAndMaxwellBlocks
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint test]
  rw [regularGeneralMetricC2PairedMinimalPhysicalMaxwellPlus_actionGradient_eq_strongDerivative
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point _ hPoint]
  rw [regularGeneralMetricC2PairedMinimalPhysicalMaxwellMinus_actionGradient_eq_strongDerivative
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point _ hPoint]

/-- Gate marker: no abstract action gradient remains in the total strong metric
equation. -/
theorem regular_general_metric_c2_paired_minimal_physical_strong_metric_all_action_derivatives_gate
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
    let direction :=
      regularGeneralMetricC2PairedMinimalPhysicalStrongMetricDirection period
        hPeriod configuration.physical test
    regularGeneralMetricC2PairedMinimalPhysicalStrongEulerLagrangeOperator
        period hPeriod configuration data analysis realization plusBase minusBase
          hBase measure point direction =
      ((((regularGeneralMetricC2PairedMinimalPhysicalStrongInteractionActionDerivative
              period hPeriod configuration data analysis realization plusBase
                minusBase measure point hPoint direction +
            regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertPlusActionDerivative
              period hPeriod configuration data analysis realization plusBase
                minusBase measure point direction) +
          regularGeneralMetricC2PairedMinimalPhysicalStrongEinsteinHilbertMinusActionDerivative
            period hPeriod configuration data analysis realization plusBase
              minusBase measure point direction) +
        regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellPlusActionDerivative
          period hPeriod configuration data analysis realization plusBase
            minusBase measure point direction) +
      regularGeneralMetricC2PairedMinimalPhysicalStrongMaxwellMinusActionDerivative
        period hPeriod configuration data analysis realization plusBase
          minusBase measure point direction) :=
  regularGeneralMetricC2PairedMinimalPhysicalStrongEuler_strongMetric_eq_allActionDerivatives
    period hPeriod configuration data analysis realization plusBase minusBase
      hBase measure point hPoint test

end
end P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongMetricAllActionDerivatives4D
end JanusFormal
