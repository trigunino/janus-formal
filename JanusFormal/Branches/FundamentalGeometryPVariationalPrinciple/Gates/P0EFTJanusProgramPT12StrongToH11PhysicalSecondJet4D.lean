import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12AugmentedMatterNoGapOfEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongSpinCPhysicalMixedHessianZero4D

/-! A genuine physical second-jet comparison on the full diagonal smooth core
transfers the strong-chart SpinC cancellation to the H11 chart.  The comparison
is an explicit hypothesis; it is not furnished by the matter--LL H13 bridge. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12StrongToH11PhysicalSecondJet4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set Filter Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateABulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPNamedModeKernelStablePerturbation4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentPDEBlockPairing4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPT12DiagonalMatterModeVector4D
open P0EFTJanusProgramPT12CanonicalReferenceMatterEigen4D
open P0EFTJanusProgramPT12MatterModeSmoothCoreEmbedding4D
open P0EFTJanusProgramPT12MatterGraphRieszNoGap4D
open P0EFTJanusProgramPT12SelfAdjointModalGapBound4D
open P0EFTJanusProgramPT12StrongSpinCPhysicalMixedHessianZero4D

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

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- The canonical diagonal-core inclusion takes a pure spectral SpinC mode to
the corresponding pure smooth SpinC direction in the strong physical chart. -/
private theorem diagonalMatterMode_minimal_eq_strongSpinC
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (mode : PrimitiveSpinCGeometricSignedMode) :
    diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
        configuration data analysis
        (diagonalMatterModeSmoothCore period hPeriod configuration analysis
          (.plus : Sector) mode) =
      regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection
        period hPeriod configuration.physical
        (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
          (Finsupp.single ((.plus : Sector), mode) (1 : Complex))) := by
  apply Subtype.ext
  simp [diagonalExtendedBulkMinimalPhysicalTangentLinearMap,
    diagonalExtendedBulkGaugeFixedTangentLinearMap,
    diagonalMatterModeSmoothCore,
    extendedMatterGaugeFixedTangentLinearMap,
    extendedMatterMinimalTangentLinearMap,
    globalGaugeFixedPhysicalTangentPhysicalProjectionLinearMap,
    globalGaugeFixedPhysicalTangentPhysicalInclusionLinearMap,
    globalCandidateABulkMatterPhysicalTangentLinearMap,
    regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection,
    globalMinimalPhysicalTangentSectorEquiv,
    P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D.productSecondInclusion,
    programPPrimitiveSpinCMatterSmoothFiniteSynthesisRealLinearMap,
    programPPrimitiveSpinCMatterSmoothFiniteSynthesisLinearMap]

/-- The missing physical two-jet bridge compares both slots on the whole
diagonal core using its canonical minimal-physical tangent inclusion.  No such
comparison follows from H13 matter--LL agreement. -/
structure StrongToH11PhysicalSecondJet
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
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase) where
  point : GlobalMinimalPhysicalFieldTangent period hPeriod
    configuration.physical
  point_mem : point ∈
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period
      hPeriod configuration.physical plusBase minusBase
  physical_second_jet : ∀ first second,
    diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period
      hPeriod configuration data analysis chart sameAction.chartBridge first
        second =
      globalCandidateALocalPhysicalHessian period hPeriod
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure)
        point
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis first)
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis second)

/-- Dense-core Hessian cancellation determines the full physical Riesz image. -/
private theorem physicalRiesz_core_zero_of_hessian_column_zero
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis)
    (hHessian : ∀ test,
      diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period
        hPeriod configuration data analysis chart sameAction.chartBridge test
          core = 0) :
    globalCandidateACanonicalStablePhysicalPerturbation period hPeriod
      configuration data analysis chart sameAction physical
      (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis core) = 0 := by
  let embedding := diagonalExtendedBulkL2SmoothEmbedding period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis
  let riesz := globalCandidateACanonicalStablePhysicalPerturbation period hPeriod
    configuration data analysis chart sameAction physical
  have hDense := diagonalExtendedBulkL2SmoothEmbedding_denseRange period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis
  have hPair : ∀ test, inner Real (riesz (embedding core)) (embedding test) = 0 := by
    intro test
    calc
      inner Real (riesz (embedding core)) (embedding test) =
          physical.form (embedding core) (embedding test) := by
        exact globalCandidateASevenPhysicalCommonRieszOperator_pairing period
          hPeriod configuration data analysis chart sameAction physical _ _
      _ = physical.form (embedding test) (embedding core) := physical.symmetric _ _
      _ = diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period
            hPeriod configuration data analysis chart sameAction.chartBridge
            test core := physical.smooth_agreement test core
      _ = 0 := hHessian test
  have hAll : (fun test => inner Real (riesz (embedding core)) test) =
      (fun _ => (0 : Real)) := by
    apply hDense.equalizer
    · exact continuous_const.inner continuous_id
    · exact continuous_const
    · funext test
      exact hPair test
  exact inner_self_eq_zero.mp (congrFun hAll (riesz (embedding core)))

/-- A physical second-jet comparison with the concrete strong chart kills
the complete seven-block Riesz image of every completed plus-sector mode. -/
theorem physicalRiesz_matterMode_zero_of_strong_second_jet
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
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (bridge : StrongToH11PhysicalSecondJet period hPeriod configuration data
      analysis realization chart sameAction plusBase minusBase hBase)
    (mode : PrimitiveSpinCGeometricSignedMode) :
    globalCandidateACanonicalStablePhysicalPerturbation period hPeriod
      configuration data analysis chart sameAction physical
      (diagonalMatterModeVector period hPeriod configuration data analysis
        (.plus : Sector) mode) = 0 := by
  rw [diagonalMatterModeVector_eq_smoothCoreEmbedding period hPeriod
    configuration data analysis (.plus : Sector) mode]
  apply physicalRiesz_core_zero_of_hessian_column_zero period hPeriod
    configuration data analysis chart sameAction physical
    (diagonalMatterModeSmoothCore period hPeriod configuration analysis
      (.plus : Sector) mode)
  intro test
  rw [bridge.physical_second_jet test
    (diagonalMatterModeSmoothCore period hPeriod configuration analysis
      (.plus : Sector) mode),
    diagonalMatterMode_minimal_eq_strongSpinC period hPeriod configuration
      data analysis mode]
  exact strong_spinC_physical_mixed_hessian_zero period hPeriod configuration
    data analysis realization plusBase minusBase hBase measure bridge.point
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
      configuration data analysis test) bridge.point_mem
    (programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
      (Finsupp.single ((.plus : Sector), mode) (1 : Complex)))

/-- The full augmented H12 gap fails whenever this explicit physical
strong-to-H11 second-jet comparison is available. -/
theorem no_augmented_kernelComplementGap_of_strong_second_jet
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
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (bridge : StrongToH11PhysicalSecondJet period hPeriod configuration data
      analysis realization chart sameAction plusBase minusBase hBase) :
    SelfAdjointKernelComplementGapData
      (globalCandidateAActualKernelOperator period hPeriod configuration data
        analysis chart sameAction physical)
      (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
        configuration data analysis chart sameAction physical) → False := by
  intro gapData
  obtain ⟨mode, hWeight, hSmall⟩ := exists_nonzero_matter_ratio_below
    period hPeriod couplings.matterMassSquared gapData.gap gapData.gap_pos
  let w := primitiveSpinCGeometricSignedKineticHessianWeight
    period hPeriod mode + couplings.matterMassSquared
  let eigenvalue := w / (1 + w ^ 2)
  let vector := diagonalMatterModeVector period hPeriod configuration data
    analysis (.plus : Sector) mode
  have hDen : 1 + w ^ 2 ≠ 0 := by positivity
  have hEigenvalue : eigenvalue ≠ 0 := div_ne_zero hWeight hDen
  have hVector : vector ≠ 0 :=
    diagonalMatterModeVector_ne_zero period hPeriod configuration data
      analysis (.plus : Sector) mode
  have hReference :
      globalCandidateACanonicalStableReferenceOperator period hPeriod
        configuration data analysis vector = eigenvalue • vector := by
    simpa only [programPPrimitiveSpinCMatterHessianWeight, vector, eigenvalue, w] using
      globalCandidateACanonicalStableReferenceOperator_matter_mode_eigen
        period hPeriod configuration data analysis (.plus : Sector) mode
  have hPhysical :
      globalCandidateACanonicalStablePhysicalPerturbation period hPeriod
        configuration data analysis chart sameAction physical vector = 0 :=
    physicalRiesz_matterMode_zero_of_strong_second_jet period hPeriod
      configuration data analysis realization chart sameAction physical
      plusBase minusBase hBase bridge mode
  have hFull :
      globalCandidateAActualKernelOperator period hPeriod configuration data
        analysis chart sameAction physical vector = eigenvalue • vector := by
    rw [globalCandidateAActualKernelOperator_eq_canonicalStableSum]
    simp [finiteKernelStablePerturbedOperator, hReference, hPhysical]
  have hFloor := gap_le_abs_nonzero_eigenvalue
    (globalCandidateAActualKernelOperator period hPeriod configuration data
      analysis chart sameAction physical)
    (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
    gapData hEigenvalue hVector hFull
  exact (not_lt_of_ge hFloor) hSmall

end
end P0EFTJanusProgramPT12StrongToH11PhysicalSecondJet4D
end JanusFormal
