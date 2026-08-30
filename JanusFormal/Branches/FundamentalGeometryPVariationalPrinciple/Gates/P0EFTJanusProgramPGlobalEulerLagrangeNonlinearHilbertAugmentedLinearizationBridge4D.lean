import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertLinearization4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeFaithfulAugmentedRieszResidual4D

/-!
# Bridge from nonlinear covariant Euler to the augmented gauge-fixed Hessian

On the dense smooth core, the linearization of the exact nonlinear covariant
Euler map is the true local covariant Hessian.  The previously constructed
augmented Hessian is exactly this form plus the explicit gauge-fixing Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertAugmentedLinearizationBridge4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open Set MeasureTheory
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
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalEulerLagrangeFaithfulAugmentedRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertLinearization4D

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

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section

variable
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
    (chartRealization :
      CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
        chart.Model)
    (smoothCoreAgreement :
      ∀ core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
          analysis,
        chartRealization
            (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
              (globalCandidateAMetricBySector period hPeriod data)
              couplings.matterMassSquared data analysis core) =
          sameAction.chartBridge.tangentAnalysis
            (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
              configuration data analysis core))

include smoothCoreAgreement

/-- The nonlinear covariant linearization is the genuine local covariant
Hessian on every pair of smooth core directions. -/
theorem globalCandidateANonlinearHilbertHessian_smooth_eq_covariant
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period
      hPeriod analysis) :
    globalCandidateANonlinearHilbertHessian period hPeriod configuration data
        analysis chart sameAction.chartBridge.basePoint chartRealization 0
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis first)
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis second) =
      diagonalExtendedBulkMinimalPhysicalLocalCovariantHessianOnCore period
        hPeriod configuration data analysis chart sameAction.chartBridge first
          second := by
  rw [globalCandidateANonlinearHilbertHessian_pairing period hPeriod
    configuration data analysis chart sameAction.chartBridge.basePoint
      chartRealization 0]
  simp only [globalCandidateANonlinearHilbertChartPoint, map_zero, add_zero]
  rw [smoothCoreAgreement first, smoothCoreAgreement second]
  rfl

/-- The full augmented Hessian is the nonlinear covariant linearization plus
the explicit gauge-fixing form; no gauge block is discarded. -/
theorem globalCandidateACommonAugmentedHessian_smooth_eq_nonlinear_add_gaugeFixing
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period
      hPeriod analysis) :
    globalCandidateACommonAugmentedHessian period hPeriod configuration data
        analysis chart sameAction physical
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis first)
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis second) =
      globalCandidateANonlinearHilbertHessian period hPeriod configuration data
          analysis chart sameAction.chartBridge.basePoint chartRealization 0
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis first)
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis second) +
        diagonalExtendedBulkGaugeFixingHessianOnCore period hPeriod
          configuration data analysis first second := by
  rw [globalCandidateACommonAugmentedHessian_smooth_eq_gaugeFixed period hPeriod
    configuration data analysis chart sameAction physical first second]
  unfold diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore
  rw [globalCandidateANonlinearHilbertHessian_smooth_eq_covariant period hPeriod
    configuration data analysis chart sameAction chartRealization
      smoothCoreAgreement first second]

/-- Thus equality with the augmented Hessian is equivalent exactly to
vanishing of the gauge-fixing Hessian on the tested pair. -/
theorem globalCandidateACommonAugmentedHessian_smooth_eq_nonlinear_iff_gaugeFixing
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period
      hPeriod analysis) :
    globalCandidateACommonAugmentedHessian period hPeriod configuration data
        analysis chart sameAction physical
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis first)
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis second) =
      globalCandidateANonlinearHilbertHessian period hPeriod configuration data
        analysis chart sameAction.chartBridge.basePoint chartRealization 0
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis first)
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis second) ↔
      diagonalExtendedBulkGaugeFixingHessianOnCore period hPeriod
        configuration data analysis first second = 0 := by
  rw [globalCandidateACommonAugmentedHessian_smooth_eq_nonlinear_add_gaugeFixing
    period hPeriod configuration data analysis chart sameAction chartRealization
      smoothCoreAgreement physical first second]
  constructor
  · intro hEquality
    linarith
  · intro hGauge
    rw [hGauge, add_zero]

/-- Weak pairing of the strong nonlinear linearization on the smooth core. -/
theorem globalCandidateANonlinearHilbertRieszLinearization_smooth_pairing
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period
      hPeriod analysis) :
    inner Real
        (globalCandidateANonlinearHilbertRieszLinearization period hPeriod
          configuration data analysis chart sameAction.chartBridge.basePoint
            chartRealization 0
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis first))
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis second) =
      diagonalExtendedBulkMinimalPhysicalLocalCovariantHessianOnCore period
        hPeriod configuration data analysis chart sameAction.chartBridge first
          second := by
  rw [globalCandidateANonlinearHilbertRieszLinearization_pairing period hPeriod
    configuration data analysis chart sameAction.chartBridge.basePoint
      chartRealization 0]
  exact globalCandidateANonlinearHilbertHessian_smooth_eq_covariant period
    hPeriod configuration data analysis chart sameAction chartRealization
      smoothCoreAgreement first second

/-- Strong augmented and nonlinear linearized residuals differ weakly by the
same explicit gauge-fixing Hessian. -/
theorem globalCandidateACommonAugmentedRieszOperator_smooth_eq_nonlinear_add_gaugeFixing
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period
      hPeriod analysis) :
    inner Real
        (globalCandidateACommonAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis first))
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis second) =
      inner Real
          (globalCandidateANonlinearHilbertRieszLinearization period hPeriod
            configuration data analysis chart sameAction.chartBridge.basePoint
              chartRealization 0
            (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
              (globalCandidateAMetricBySector period hPeriod data)
              couplings.matterMassSquared data analysis first))
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis second) +
        diagonalExtendedBulkGaugeFixingHessianOnCore period hPeriod
          configuration data analysis first second := by
  rw [globalCandidateACommonAugmentedRieszOperator_pairing period hPeriod
    configuration data analysis chart sameAction physical]
  rw [globalCandidateACommonAugmentedHessian_smooth_eq_nonlinear_add_gaugeFixing
    period hPeriod configuration data analysis chart sameAction chartRealization
      smoothCoreAgreement physical first second]
  rw [globalCandidateANonlinearHilbertRieszLinearization_pairing period hPeriod]

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeNonlinearHilbertAugmentedLinearizationBridge4D
end JanusFormal
