import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12CanonicalReferenceMatterEigen4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MatterModePhysicalRieszZero4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MatterGraphRieszNoGap4D

/-! If every pure SpinC mode has vanishing physical Euler germ, the augmented
Candidate-A Riesz map has no positive kernel-complement norm gap. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12AugmentedMatterNoGapOfEuler4D

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Filter Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
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
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPPrimitiveSpinCGeometricSignedFredholm4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPNamedModeKernelStablePerturbation4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPT12DiagonalMatterModeVector4D
open P0EFTJanusProgramPT12CanonicalReferenceMatterEigen4D
open P0EFTJanusProgramPT12MatterModeSmoothCoreEmbedding4D
open P0EFTJanusProgramPT12MatterModePhysicalRieszZero4D
open P0EFTJanusProgramPT12MatterGraphRieszNoGap4D
open P0EFTJanusProgramPT12SelfAdjointModalGapBound4D

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

/-- Under the stated local Euler-vanishing condition, every high-frequency
SpinC mode remains a nonzero eigenmode of the full augmented Riesz map. -/
theorem no_augmented_kernelComplementGap_of_matter_euler_zero
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
    (hEuler : ∀ mode : PrimitiveSpinCGeometricSignedMode,
      (fun state : chart.Model =>
        actionGradient
          (fullCoupledPhysicalAction
            (globalCandidateAActionBlocks period hPeriod
              (chart.family.toActionFamily period hPeriod 0
                chart.zero_mem_domain) measure)) state
          (sameAction.chartBridge.tangentAnalysis
            (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
              configuration data analysis
              (diagonalMatterModeSmoothCore period hPeriod configuration
                analysis (.plus : Sector) mode)))) =ᶠ[𝓝 sameAction.chartBridge.basePoint]
        fun _ => (0 : Real)) :
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
    simpa only [programPPrimitiveSpinCMatterHessianWeight] using
      globalCandidateACanonicalStableReferenceOperator_matter_mode_eigen
        period hPeriod configuration data analysis (.plus : Sector) mode
  have hPhysical :
      globalCandidateACanonicalStablePhysicalPerturbation period hPeriod
        configuration data analysis chart sameAction physical vector = 0 :=
    physicalRiesz_matterMode_zero_of_eventually_euler_zero period hPeriod
      configuration data analysis chart sameAction physical (.plus : Sector)
      mode (hEuler mode)
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
end P0EFTJanusProgramPT12AugmentedMatterNoGapOfEuler4D
end JanusFormal
