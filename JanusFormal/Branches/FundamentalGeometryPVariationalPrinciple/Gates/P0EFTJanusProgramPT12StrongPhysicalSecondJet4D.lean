import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongToH11PhysicalSecondJet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongMatterLLSameActionBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongLLPhysicalMixedHessianZero4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MinimalPhysicalMatterLLReducedSliceToChart4D

/-! The strong same-action chart supplies its own physical second jet. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12StrongPhysicalSecondJet4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusCompleteVariationModuleCore4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusIndependentFieldVariationLinearSpace4D
open P0EFTJanusProgramPCommonLLActionVariation4D
open P0EFTJanusCommonGaugeD9Variation4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateABulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentPDEBlockPairing4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLWeakFirstVariation4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPT12StrongMatterLLSameActionBridge4D
open P0EFTJanusProgramPT12StrongToH11PhysicalSecondJet4D
open P0EFTJanusProgramPT12StrongLLPhysicalMixedHessianZero4D
open P0EFTJanusProgramPT12MinimalPhysicalMatterLLReducedSliceToChart4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D

attribute [local instance]
  actualKernelNormedAddCommGroup
  actualKernelInnerProductSpace
  actualKernelNormedSpace
  actualKernelModule
  actualKernelCompleteSpace
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance : ChartedSpace ThroatCoverModel
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- For the concrete strong chart, the H11 chart bridge is the identity at
the origin, so its physical second jet is definitionally the same Hessian. -/
def strongPhysicalSecondJet
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
    (hCenter : RegularGeneralMetricC2PairedMinimalPhysicalCenterCompatible
      period hPeriod configuration.physical plusBase minusBase hBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    StrongToH11PhysicalSecondJet period hPeriod configuration data analysis
      realization
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure)
      (strongMatterLLSameActionBridge period hPeriod configuration data analysis
        realization plusBase minusBase hBase hCenter measure)
      plusBase minusBase hBase := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  refine { point := 0, point_mem := ?_, physical_second_jet := ?_ }
  · exact zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration.physical plusBase minusBase hBase
  · intro first second
    rfl

private theorem pureMatter_minimal_eq_strongMatter
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (matter : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis
        (0, (0, (matter, 0))) =
      regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection
          period hPeriod configuration.physical
          (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
            matter) := by
  apply Subtype.ext
  simp [diagonalExtendedBulkMinimalPhysicalTangentLinearMap,
    diagonalExtendedBulkGaugeFixedTangentLinearMap,
    extendedMatterGaugeFixedTangentLinearMap,
    extendedLLGaugeFixedTangentLinearMap,
    extendedMatterMinimalTangentLinearMap,
    extendedLLMinimalTangentLinearMap,
    globalGaugeFixedPhysicalTangentPhysicalProjectionLinearMap,
    globalGaugeFixedPhysicalTangentPhysicalInclusionLinearMap,
    globalCandidateABulkMatterPhysicalTangentLinearMap,
    regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection,
    globalMinimalPhysicalTangentSectorEquiv,
    productSecondInclusion,
    programPPrimitiveSpinCMatterSmoothFiniteSynthesisRealLinearMap,
    programPPrimitiveSpinCMatterSmoothFiniteSynthesisLinearMap]

private theorem pureLL_minimal_eq_strongLL
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (ll : LLH1Smooth period hPeriod (analysis.llH1Data period hPeriod)) :
    diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis (0, (0, (0, (0, ll)))) =
      regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
        hPeriod configuration.physical (0, (0, ll.toTest)) := by
  apply Subtype.ext
  simp [diagonalExtendedBulkMinimalPhysicalTangentLinearMap,
    diagonalExtendedBulkGaugeFixedTangentLinearMap,
    extendedMatterGaugeFixedTangentLinearMap,
    extendedLLGaugeFixedTangentLinearMap,
    extendedMatterMinimalTangentLinearMap,
    extendedLLMinimalTangentLinearMap,
    globalGaugeFixedPhysicalTangentPhysicalProjectionLinearMap,
    globalGaugeFixedPhysicalTangentPhysicalInclusionLinearMap,
    regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection,
    regularGeneralMetricC2PairedMinimalPhysicalStrongSevenBulkDirection,
    globalMinimalPhysicalTangentSectorEquiv,
    globalMinimalPhysicalSevenBulkEquiv,
    productFirstInclusion,
    fullLLSmoothPhysicalTangentLinearMap,
    fullLLSmoothGeneralMetricLinearMap,
    fullLLSmoothMatterFreeLinearMap,
    fullLLSmoothCompleteLinearMap,
    fullLLSmoothIndependentLinearMap,
    independentCompleteVariationLinearMap,
    independentCompleteVariation,
    zeroSmoothDiagonalMetricVariation]
  constructor
  · apply SmoothDiagonalMetricVariation.ext <;> rfl
  constructor
  · funext sector
    rfl
  constructor
  · funext sector
    apply ContMDiffSection.coe_injective
    rfl
  · funext sector
    apply SmoothSymmetricCovariantTwoTensor.ext
    rfl

/-- On the centered strong chart, all seven physical blocks annihilate every
smooth reduced matter--LL slice vector in the common physical Riesz model. -/
theorem strongPhysicalRiesz_matterLLReducedSlice_zero
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    [IsFiniteMeasure measure]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (hCenter : RegularGeneralMetricC2PairedMinimalPhysicalCenterCompatible
      period hPeriod configuration.physical plusBase minusBase hBase)
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure)
      (strongMatterLLSameActionBridge period hPeriod configuration data analysis
        realization plusBase minusBase hBase hCenter measure))
    (direction : ProgramPT12MinimalPhysicalMatterLLReducedSlice period hPeriod
      configuration analysis) :
    globalCandidateACanonicalStablePhysicalPerturbation period hPeriod
        configuration data analysis
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure)
        (strongMatterLLSameActionBridge period hPeriod configuration data
          analysis realization plusBase minusBase hBase hCenter measure)
        physical
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis
          (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
            configuration analysis direction)) = 0 := by
  apply physicalRiesz_core_zero_of_hessian_column_zero period hPeriod
    configuration data analysis
    (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure)
    (strongMatterLLSameActionBridge period hPeriod configuration data analysis
      realization plusBase minusBase hBase hCenter measure)
    physical
    (programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
      configuration analysis direction)
  intro test
  rw [(strongPhysicalSecondJet period hPeriod configuration data analysis
    realization plusBase minusBase hBase hCenter measure).physical_second_jet]
  have hCore :
      programPT12MinimalPhysicalMatterLLReducedSliceCore period hPeriod
          configuration analysis direction =
        (0, (0, (direction.1, 0))) +
          (0, (0, (0, (0, direction.2)))) := by
    ext <;> simp [programPT12MinimalPhysicalMatterLLReducedSliceCore]
  rw [hCore, map_add,
    pureMatter_minimal_eq_strongMatter period hPeriod configuration data
      analysis direction.1,
    pureLL_minimal_eq_strongLL period hPeriod configuration data analysis
      direction.2]
  exact strong_matter_LL_physical_mixed_hessian_zero period hPeriod
    configuration data analysis realization plusBase minusBase hBase measure
    0
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
      configuration data analysis test)
    (zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
      period hPeriod configuration.physical plusBase minusBase hBase)
    (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
      direction.1)
    (0, (0, direction.2.toTest))

end
end P0EFTJanusProgramPT12StrongPhysicalSecondJet4D
end JanusFormal
