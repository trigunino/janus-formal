import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeFaithfulAugmentedRieszResidual4D

/-!
# Weak--strong closure for the full augmented Candidate-A Hessian

Density of the typed smooth core upgrades vanishing against every smooth test
to vanishing of the full Hilbert Riesz residual.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeFaithfulAugmentedSmoothWeakStrongResidual4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalEulerLagrangeFaithfulAugmentedRieszResidual4D

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

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- The local weak linearized Euler system on every smooth test is equivalent
to the full strong Riesz equation. -/
theorem globalCandidateAFaithfulAugmentedSmoothWeakEuler_iff_rieszResidual
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
    (first : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    (∀ second : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
        analysis,
      diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore period
        hPeriod configuration data analysis chart sameAction.chartBridge first
          second = 0) ↔
      globalCandidateAFaithfulAugmentedRieszResidual period hPeriod
        configuration data analysis chart sameAction physical
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis first) = 0 := by
  let embedding := diagonalExtendedBulkL2SmoothEmbedding period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis
  constructor
  · intro hWeak
    have hDense : DenseRange embedding :=
      diagonalExtendedBulkL2SmoothEmbedding_denseRange period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
    let covector := globalCandidateACommonAugmentedHessian period hPeriod
      configuration data analysis chart sameAction physical (embedding first)
    have hOnCore : ∀ second, covector (embedding second) = 0 := by
      intro second
      exact
        (globalCandidateACommonAugmentedHessian_smooth_eq_gaugeFixed period
          hPeriod configuration data analysis chart sameAction physical first
            second).trans (hWeak second)
    have hPointwise : (fun test => covector test) = fun _ => 0 :=
      hDense.equalizer covector.continuous continuous_const (by
        funext second
        exact hOnCore second)
    have hCovector : covector = 0 := by
      apply ContinuousLinearMap.ext
      intro test
      exact congrFun hPointwise test
    apply
      (globalCandidateAFaithfulAugmentedEulerCovector_eq_zero_iff_rieszResidual
        period hPeriod configuration data analysis chart sameAction physical
          (embedding first)).mp
    rw [globalCandidateACommonAugmentedAction_fderiv period hPeriod
      configuration data analysis chart sameAction physical (embedding first)]
    exact hCovector
  · intro hResidual second
    have hPairing :=
      globalCandidateAFaithfulAugmentedRieszResidual_smooth_pairing period
        hPeriod configuration data analysis chart sameAction physical first
          second
    simpa only [globalCandidateAFaithfulAugmentedRieszResidualPairing,
      hResidual, inner_zero_left] using hPairing.symm

/-- Equivalently, the local weak system is the zero Frechet covector equation
of the full augmented quadratic action. -/
theorem globalCandidateAFaithfulAugmentedSmoothWeakEuler_iff_actionEulerCovector
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
    (first : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    (∀ second : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
        analysis,
      diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore period
        hPeriod configuration data analysis chart sameAction.chartBridge first
          second = 0) ↔
      fderiv Real
        (globalCandidateACommonAugmentedAction period hPeriod configuration data
          analysis chart sameAction physical)
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis first) = 0 := by
  rw [globalCandidateAFaithfulAugmentedSmoothWeakEuler_iff_rieszResidual period
    hPeriod configuration data analysis chart sameAction physical first]
  exact
    (globalCandidateAFaithfulAugmentedEulerCovector_eq_zero_iff_rieszResidual
      period hPeriod configuration data analysis chart sameAction physical
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis first)).symm

end
end P0EFTJanusProgramPGlobalEulerLagrangeFaithfulAugmentedSmoothWeakStrongResidual4D
end JanusFormal
