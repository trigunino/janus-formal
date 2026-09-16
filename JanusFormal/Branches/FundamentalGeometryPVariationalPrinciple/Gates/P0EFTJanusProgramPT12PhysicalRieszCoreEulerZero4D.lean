import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LocalPhysicalHessianDirectionalZero4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D

/-! A physical Euler component vanishing as a germ annihilates its full seven-block Riesz vector. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12PhysicalRieszCoreEulerZero4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateACanonicalStablePerturbation4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPT12LocalPhysicalHessianDirectionalZero4D

attribute [local instance]
  actualKernelNormedAddCommGroup
  actualKernelInnerProductSpace
  actualKernelNormedSpace
  actualKernelModule
  actualKernelCompleteSpace

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

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

/-- Germwise vanishing of the physical Euler component controls all mixed
pairings, hence the complete Riesz vector rather than only its matter projection. -/
theorem physicalRiesz_core_zero_of_eventually_euler_zero
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
    (hEuler :
      (fun state : chart.Model =>
        actionGradient
          (fullCoupledPhysicalAction
            (globalCandidateAActionBlocks period hPeriod
              (chart.family.toActionFamily period hPeriod 0
                chart.zero_mem_domain) measure)) state
          (sameAction.chartBridge.tangentAnalysis
            (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
              configuration data analysis core))) =ᶠ[𝓝 sameAction.chartBridge.basePoint]
        fun _ => (0 : Real)) :
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
      _ = physical.form (embedding test) (embedding core) :=
        physical.symmetric _ _
      _ = diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period
            hPeriod configuration data analysis chart sameAction.chartBridge
            test core := physical.smooth_agreement test core
      _ = 0 := localPhysicalHessian_second_slot_zero_of_eventually_euler_zero
        period hPeriod chart sameAction.chartBridge.basePoint
        sameAction.chartBridge.basePoint_mem
        (sameAction.chartBridge.tangentAnalysis
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis core)) hEuler
        (sameAction.chartBridge.tangentAnalysis
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis test))
  have hAll : (fun test => inner Real (riesz (embedding core)) test) =
      (fun _ => (0 : Real)) := by
    apply hDense.equalizer
    · exact continuous_const.inner continuous_id
    · exact continuous_const
    · funext test
      exact hPair test
  have hSelf := congrFun hAll (riesz (embedding core))
  exact inner_self_eq_zero.mp hSelf

end
end P0EFTJanusProgramPT12PhysicalRieszCoreEulerZero4D
end JanusFormal
