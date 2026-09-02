import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianNonminimalEuler4D

/-!
# Euler equation of the diffeomorphism nonminimal fields

Pure diffeomorphism-nonminimal core tests have zero physical and paired
Abelian components.  Their exact full-BRST Euler equation is therefore the
restriction of the diagonal diffeomorphism BRST Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalEuler4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusCompleteVariationGaugeFunctionalTypeBridge4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFactorwiseEulerPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianNonminimalEuler4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldDiffeomorphism :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroatCover :=
  MappingTorusCover (fixedEquatorData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveQuotientChartedSpaceDiffeomorphism :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldDiffeomorphism :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceDiffeomorphism :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceDiffeomorphism :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatCoverChartedSpaceDiffeomorphism :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifoldDiffeomorphism :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpaceDiffeomorphism :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifoldDiffeomorphism :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance canonicalLorentzVolumeFiniteDiffeomorphism :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section DiffeomorphismNonminimalEuler

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

private abbrev BaseMetric :=
  globalCandidateAMetricBySector period hPeriod data

private abbrev FullCore :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTCore4D period hPeriod
    configuration

private abbrev FullChart :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) fullChartAddCommGroupDiffeomorphism :
    AddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartAddCommGroup period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) fullChartModuleDiffeomorphism :
    Module Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartModule period hPeriod (measure := measure)
    configuration data analysis chartData

/-- Pure diffeomorphism-nonminimal inclusion into the full-BRST core. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalOnlyCoreLinearMap :
    GlobalDiffeomorphismNonminimalFields period hPeriod →ₗ[Real]
      FullCore period hPeriod configuration where
  toFun nonminimal := (0, (nonminimal, 0))
  map_add' first second := by
    apply Prod.ext
    · simp
    · apply Prod.ext
      · rfl
      · change (0 : GlobalPairedAbelianBRSTState period hPeriod) = 0 + 0
        simp
  map_smul' scalar nonminimal := by
    apply Prod.ext
    · simp
    · apply Prod.ext
      · rfl
      · change (0 : GlobalPairedAbelianBRSTState period hPeriod) = scalar • 0
        simp

/-- Diagonal diffeomorphism BRST state with only its nonminimal fields
varied. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalOnlyStateLinearMap :
    GlobalDiffeomorphismNonminimalFields period hPeriod →ₗ[Real]
      GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod where
  toFun nonminimal := { metricPerturbation := 0, nonminimal := nonminimal }
  map_add' first second := by
    apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
    · change (0 : Sector → SmoothSymmetricCovariantTwoTensor period hPeriod) =
          0 + 0
      simp
    · rfl
  map_smul' scalar nonminimal := by
    apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
    · change (0 : Sector → SmoothSymmetricCovariantTwoTensor period hPeriod) =
          scalar • 0
      simp
    · rfl

/-- Completed diagonal diffeomorphism graph point underlying one full-BRST
state. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTPoint
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection period
    hPeriod configuration data analysis chartData
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection period
      hPeriod configuration data analysis chartData state)

/-- Diffeomorphism BRST Hessian restricted to nonminimal tests. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalDiffeomorphismNonminimalFields period hPeriod →ₗ[Real] Real :=
  (globalCandidateADiagonalDiffeomorphismOffShellHessian period hPeriod
    couplings (BaseMetric period hPeriod configuration data)
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTPoint period
      hPeriod configuration data analysis chartData state)).toLinearMap.comp
      ((globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period
        hPeriod (BaseMetric period hPeriod configuration data)).comp
          (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalOnlyStateLinearMap
            period hPeriod))

private theorem physicalEulerContribution_diffeomorphismNonminimalOnly_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData)
    (nonminimal : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalEulerContribution period
        hPeriod configuration data analysis chartData state
        (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalOnlyCoreLinearMap
          period hPeriod configuration nonminimal) = 0 := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalEulerContribution
  rw [globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection_core]
  have hPhysicalTangent :
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
        period hPeriod configuration data
        (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalOnlyCoreLinearMap
          period hPeriod configuration nonminimal)).1 = 0 := by
    change (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration.physical) +
      globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
        hPeriod data 0 = 0
    rw [map_zero, add_zero]
  rw [hPhysicalTangent, map_zero, map_zero]

private theorem diffeomorphismState_nonminimalOnly_eq
    (nonminimal : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTStateLinearMap period
        hPeriod configuration
        (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
          period hPeriod configuration data
          (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalOnlyCoreLinearMap
            period hPeriod configuration nonminimal)) =
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalOnlyStateLinearMap
        period hPeriod nonminimal := by
  apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
  · change
      ((0 : GlobalMinimalPhysicalFieldTangent period hPeriod
            configuration.physical) +
          globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
            hPeriod data 0).1.completeVariation.fullMetricPerturbation = 0
    rw [map_zero, add_zero]
    rfl
  · rfl

private theorem diffeomorphismBRSTContribution_nonminimalOnly_eq
    (state : FullChart period hPeriod configuration data analysis chartData)
    (nonminimal : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTContribution
        period hPeriod configuration data analysis chartData state
        (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalOnlyCoreLinearMap
          period hPeriod configuration nonminimal) =
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector
        period hPeriod configuration data analysis chartData state nonminimal := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTContribution
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTPoint
  rw [globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection_core,
    diffeomorphismState_nonminimalOnly_eq]
  rfl

private theorem abelianBRSTContribution_diffeomorphismNonminimalOnly_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData)
    (nonminimal : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianBRSTContribution period
        hPeriod configuration data analysis chartData state
        (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalOnlyCoreLinearMap
          period hPeriod configuration nonminimal) = 0 := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTAbelianBRSTContribution
  change
    globalPairedAbelianOffShellHessian period hPeriod
        (BaseMetric period hPeriod configuration data)
        (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
          hPeriod configuration data analysis chartData state)
        (globalPairedAbelianOffShellSmoothEmbedding period hPeriod
          (BaseMetric period hPeriod configuration data) 0) = 0
  rw [map_zero, map_zero]

/-- The exact diffeomorphism-nonminimal Euler covector is the corresponding
BRST Hessian restriction. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalEulerCovector_eq
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalEulerCovector
        period hPeriod configuration data analysis chartData state =
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector
        period hPeriod configuration data analysis chartData state := by
  apply LinearMap.ext
  intro nonminimal
  change
    globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector period hPeriod
        configuration data analysis chartData state
        (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalOnlyCoreLinearMap
          period hPeriod configuration nonminimal) = _
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector_apply_eq_factorwise,
    physicalEulerContribution_diffeomorphismNonminimalOnly_eq_zero,
    diffeomorphismBRSTContribution_nonminimalOnly_eq,
    abelianBRSTContribution_diffeomorphismNonminimalOnly_eq_zero]
  simp

/-- The restricted Hessian pairing uses the already established strong Riesz
operator of the completed diffeomorphism graph. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector_apply_eq_rieszPairing
    (state : FullChart period hPeriod configuration data analysis chartData)
    (nonminimal : GlobalDiffeomorphismNonminimalFields period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector
        period hPeriod configuration data analysis chartData state nonminimal =
      inner Real
        (globalCandidateADiagonalDiffeomorphismOffShellRieszOperator period
          hPeriod couplings (BaseMetric period hPeriod configuration data)
          (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTPoint
            period hPeriod configuration data analysis chartData state))
        (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period
          hPeriod (BaseMetric period hPeriod configuration data)
          (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalOnlyStateLinearMap
            period hPeriod nonminimal)) := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector
  simp only [LinearMap.comp_apply]
  exact (globalCandidateADiagonalDiffeomorphismOffShellRieszOperator_pairing
    period hPeriod couplings (BaseMetric period hPeriod configuration data)
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTPoint period
      hPeriod configuration data analysis chartData state)
    (globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding period
      hPeriod (BaseMetric period hPeriod configuration data)
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalOnlyStateLinearMap
        period hPeriod nonminimal))).symm

/-- Refined system with both pure nonminimal equations written as their BRST
Hessian restrictions. -/
def GlobalCandidateAGaugeFixedNonlinearFullBRSTResolvedCoreEulerSystemAt
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Prop :=
  globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector
      period hPeriod configuration data analysis chartData state = 0 ∧
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector
        period hPeriod configuration data analysis chartData state = 0 ∧
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector period
          hPeriod configuration data analysis chartData state = 0 ∧
        globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalBRSTCovector
          period hPeriod configuration data analysis chartData state = 0

/-- Exact criticality is equivalent to the resolved four-part system. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_resolvedCoreEulerSystem
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTResolvedCoreEulerSystemAt
        period hPeriod configuration data analysis chartData state := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_refinedCoreEulerSystem]
  unfold GlobalCandidateAGaugeFixedNonlinearFullBRSTRefinedCoreEulerSystemAt
    GlobalCandidateAGaugeFixedNonlinearFullBRSTResolvedCoreEulerSystemAt
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalEulerCovector_eq,
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalEulerCovector_eq]

/-- Gate 228: both pure nonminimal Euler equations are exact restrictions of
their completed BRST Hessians. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_diffeomorphism_nonminimal_euler_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTResolvedCoreEulerSystemAt
        period hPeriod configuration data analysis chartData state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_resolvedCoreEulerSystem
    period hPeriod configuration data analysis chartData state

end DiffeomorphismNonminimalEuler

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalEuler4D
end JanusFormal
