import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphRieszResidual4D

/-!
# Full-BRST Euler system with all available augmented residuals

The potential, SpinC and three LL weak covectors are replaced by their exact
separating graph-Riesz residuals. The two nonminimal triplets retain their
strong systems; only metric, normal and physical diffeomorphism ghost remain
as weak covectors.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAugmentedResidualEulerSystem4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory Topology
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNonminimalStrongSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalStrongSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTResolvedNonminimalEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphRieszResidual4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldAugmentedResidualEulerSystem :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpaceAugmentedResidualEulerSystem :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldAugmentedResidualEulerSystem :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceAugmentedResidualEulerSystem :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceAugmentedResidualEulerSystem :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section AugmentedResidualEulerSystem

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)

private abbrev FullChart :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
    configuration data analysis chartData

/-- Exact current full-BRST system: five augmented graph residuals, two
nonminimal strong systems, and the three remaining weak physical covectors. -/
def GlobalCandidateAGaugeFixedNonlinearFullBRSTAugmentedResidualEulerSystemAt
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Prop :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector period hPeriod
        configuration data analysis chartData state = 0 ∧
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector period hPeriod
        configuration data analysis chartData state = 0 ∧
      globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector
          period hPeriod configuration data analysis chartData state = 0 ∧
        globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricAugmentedGraphRieszResidual
            period hPeriod configuration data analysis chartData state = 0 ∧
          globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureAugmentedGraphRieszResidual
              period hPeriod configuration data analysis chartData state = 0 ∧
            globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldAugmentedGraphRieszResidual
                period hPeriod configuration data analysis chartData state = 0 ∧
              globalCandidateAGaugeFixedNonlinearFullBRSTSpinCAugmentedGraphRieszResidual
                  period hPeriod configuration data analysis chartData state = 0 ∧
                GlobalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalStrongSystemAt
                    period hPeriod configuration data analysis chartData state ∧
                  globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual
                      period hPeriod configuration data analysis chartData state = 0 ∧
                    GlobalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalStrongSystemAt
                      period hPeriod configuration data analysis chartData state

theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_augmentedResidualEulerSystem
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTAugmentedResidualEulerSystemAt
        period hPeriod configuration data analysis chartData state := by
  rw [
    globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_resolvedNonminimalEulerSystem
      period hPeriod configuration data analysis chartData state]
  unfold
    GlobalCandidateAGaugeFixedNonlinearFullBRSTResolvedNonminimalEulerSystemAt
    GlobalCandidateAGaugeFixedNonlinearFullBRSTAugmentedResidualEulerSystemAt
  constructor
  · rintro ⟨hMetric, hNormal, hPhysicalGhost, hLLAux, hLLMeasure,
      hLLField, hSpinC, hDiffeomorphism, hPotential, hAbelian⟩
    exact ⟨hMetric, hNormal, hPhysicalGhost,
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector_eq_zero_iff_augmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mp hLLAux,
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector_eq_zero_iff_augmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mp hLLMeasure,
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector_eq_zero_iff_augmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mp hLLField,
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector_eq_zero_iff_augmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mp hSpinC,
      hDiffeomorphism,
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector_eq_zero_iff_graphResidual
        period hPeriod configuration data analysis chartData state).mp hPotential,
      hAbelian⟩
  · rintro ⟨hMetric, hNormal, hPhysicalGhost, hLLAux, hLLMeasure,
      hLLField, hSpinC, hDiffeomorphism, hPotential, hAbelian⟩
    exact ⟨hMetric, hNormal, hPhysicalGhost,
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLAuxMetricEulerCovector_eq_zero_iff_augmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mpr hLLAux,
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLMeasureEulerCovector_eq_zero_iff_augmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mpr hLLMeasure,
      (globalCandidateAGaugeFixedNonlinearFullBRSTLLFieldEulerCovector_eq_zero_iff_augmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mpr hLLField,
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector_eq_zero_iff_augmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mpr hSpinC,
      hDiffeomorphism,
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector_eq_zero_iff_graphResidual
        period hPeriod configuration data analysis chartData state).mpr hPotential,
      hAbelian⟩

theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_augmentedResidualEulerSystem
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hCritical : GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period
      hPeriod configuration data analysis chartData state) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTAugmentedResidualEulerSystemAt
      period hPeriod configuration data analysis chartData state :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_augmentedResidualEulerSystem
    period hPeriod configuration data analysis chartData state).mp hCritical

/-- Gate 255: criticality is exactly the current hybrid system with every
available physical augmented residual substituted. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_augmented_residual_euler_system_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTAugmentedResidualEulerSystemAt
        period hPeriod configuration data analysis chartData state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_augmentedResidualEulerSystem
    period hPeriod configuration data analysis chartData state

end AugmentedResidualEulerSystem

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAugmentedResidualEulerSystem4D
end JanusFormal
