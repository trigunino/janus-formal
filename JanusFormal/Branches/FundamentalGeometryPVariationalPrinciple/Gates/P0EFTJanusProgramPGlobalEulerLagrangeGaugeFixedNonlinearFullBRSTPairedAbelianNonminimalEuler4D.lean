import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D

/-!
# Euler equation of the paired Abelian nonminimal fields

The paired Abelian state splits linearly into its unique shared potential and
its two typed nonminimal triples.  Nonminimal-only full-BRST tests have no
physical or diffeomorphism-BRST component, so their exact Euler covector is
the restriction of the paired Abelian BRST Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianNonminimalEuler4D

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
open P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFactorwiseEulerPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldNonminimal :
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

local instance effectiveQuotientChartedSpaceNonminimal :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldNonminimal :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceNonminimal :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceNonminimal :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatCoverChartedSpaceNonminimal :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifoldNonminimal :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpaceNonminimal :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifoldNonminimal :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance canonicalLorentzVolumeFiniteNonminimal :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section NonminimalEuler

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

private abbrev PairedPotential :=
  Sector → SmoothAbelianGaugePotential period hPeriod

private abbrev PairedNonminimal :=
  Sector → GlobalAbelianNonminimalFields period hPeriod

@[implicit_reducible]
local instance (priority := 10003) fullChartAddCommGroupNonminimal :
    AddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartAddCommGroup period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) fullChartModuleNonminimal :
    Module Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartModule period hPeriod (measure := measure)
    configuration data analysis chartData

/-- Linear product coordinates of the paired Abelian state. -/
def globalPairedAbelianBRSTStateLinearEquiv :
    GlobalPairedAbelianBRSTState period hPeriod ≃ₗ[Real]
      (PairedPotential period hPeriod × PairedNonminimal period hPeriod) where
  toFun state := (state.potential, state.nonminimal)
  invFun fields := ⟨fields.1, fields.2⟩
  left_inv state := by cases state; rfl
  right_inv fields := by cases fields; rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Paired Abelian state with only its typed nonminimal fields varied. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTNonminimalOnlyPairedStateLinearMap :
    PairedNonminimal period hPeriod →ₗ[Real]
      GlobalPairedAbelianBRSTState period hPeriod where
  toFun nonminimal := { potential := 0, nonminimal := nonminimal }
  map_add' first second := by
    apply GlobalPairedAbelianBRSTState.ext
    · change (0 : PairedPotential period hPeriod) = 0 + 0
      simp
    · rfl
  map_smul' scalar nonminimal := by
    apply GlobalPairedAbelianBRSTState.ext
    · change (0 : PairedPotential period hPeriod) = scalar • 0
      simp
    · rfl

/-- Nonminimal-only inclusion into the full-BRST algebraic core. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTNonminimalOnlyCoreLinearMap :
    PairedNonminimal period hPeriod →ₗ[Real]
      FullCore period hPeriod configuration where
  toFun nonminimal :=
    (0, (0,
      globalCandidateAGaugeFixedNonlinearFullBRSTNonminimalOnlyPairedStateLinearMap
        period hPeriod nonminimal))
  map_add' first second := by
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simp
      · exact
          (globalCandidateAGaugeFixedNonlinearFullBRSTNonminimalOnlyPairedStateLinearMap
            period hPeriod).map_add first second
  map_smul' scalar nonminimal := by
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simp
      · exact
          (globalCandidateAGaugeFixedNonlinearFullBRSTNonminimalOnlyPairedStateLinearMap
            period hPeriod).map_smul scalar nonminimal

/-- Exact full-BRST Euler covector restricted to Abelian nonminimal tests. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalEulerCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    PairedNonminimal period hPeriod →ₗ[Real] Real :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector period hPeriod
    configuration data analysis chartData state).comp
      (globalCandidateAGaugeFixedNonlinearFullBRSTNonminimalOnlyCoreLinearMap
        period hPeriod configuration)

/-- Paired Abelian BRST Hessian restricted to nonminimal tests. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalBRSTCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    PairedNonminimal period hPeriod →ₗ[Real] Real :=
  (globalPairedAbelianOffShellHessian period hPeriod
    (BaseMetric period hPeriod configuration data)
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
      hPeriod configuration data analysis chartData state)).toLinearMap.comp
      ((globalPairedAbelianOffShellSmoothEmbedding period hPeriod
        (BaseMetric period hPeriod configuration data)).comp
          (globalCandidateAGaugeFixedNonlinearFullBRSTNonminimalOnlyPairedStateLinearMap
            period hPeriod))

private theorem physicalEulerContribution_nonminimalOnly_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData)
    (nonminimal : PairedNonminimal period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalEulerContribution period
        hPeriod configuration data analysis chartData state
        (globalCandidateAGaugeFixedNonlinearFullBRSTNonminimalOnlyCoreLinearMap
          period hPeriod configuration nonminimal) = 0 := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalEulerContribution
  rw [globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection_core]
  have hPhysicalTangent :
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
        period hPeriod configuration data
        (globalCandidateAGaugeFixedNonlinearFullBRSTNonminimalOnlyCoreLinearMap
          period hPeriod configuration nonminimal)).1 = 0 := by
    change (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration.physical) +
      globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
        hPeriod data 0 = 0
    rw [map_zero, add_zero]
  rw [hPhysicalTangent, map_zero, map_zero]

private theorem diffeomorphismBRSTContribution_nonminimalOnly_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData)
    (nonminimal : PairedNonminimal period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTContribution
        period hPeriod configuration data analysis chartData state
        (globalCandidateAGaugeFixedNonlinearFullBRSTNonminimalOnlyCoreLinearMap
          period hPeriod configuration nonminimal) = 0 := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTContribution
  rw [globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection_core]
  have hDiffeomorphismCore :
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
          period hPeriod configuration data
          (globalCandidateAGaugeFixedNonlinearFullBRSTNonminimalOnlyCoreLinearMap
            period hPeriod configuration nonminimal) = 0 := by
    apply Prod.ext
    · change (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
          configuration.physical) +
        globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
          hPeriod data 0 = 0
      rw [map_zero, add_zero]
    · rfl
  rw [hDiffeomorphismCore, map_zero, map_zero, map_zero]

private theorem abelianBRSTContribution_nonminimalOnly_eq
    (state : FullChart period hPeriod configuration data analysis chartData)
    (nonminimal : PairedNonminimal period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianBRSTContribution period
        hPeriod configuration data analysis chartData state
        (globalCandidateAGaugeFixedNonlinearFullBRSTNonminimalOnlyCoreLinearMap
          period hPeriod configuration nonminimal) =
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalBRSTCovector
        period hPeriod configuration data analysis chartData state
        nonminimal := by
  rfl

/-- Nonminimal-only tests contain exactly the paired Abelian BRST Hessian. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalEulerCovector_eq
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalEulerCovector
        period hPeriod configuration data analysis chartData state =
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalBRSTCovector
        period hPeriod configuration data analysis chartData state := by
  apply LinearMap.ext
  intro nonminimal
  change
    globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector period hPeriod
        configuration data analysis chartData state
        (globalCandidateAGaugeFixedNonlinearFullBRSTNonminimalOnlyCoreLinearMap
          period hPeriod configuration nonminimal) = _
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector_apply_eq_factorwise,
    physicalEulerContribution_nonminimalOnly_eq_zero,
    diffeomorphismBRSTContribution_nonminimalOnly_eq_zero,
    abelianBRSTContribution_nonminimalOnly_eq]
  simp

/-- Product-coordinate form of the paired Abelian Euler covector. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPairedAbelianProductEulerCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    (PairedPotential period hPeriod × PairedNonminimal period hPeriod) →ₗ[Real]
      Real :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTPairedAbelianEulerCovector period
    hPeriod configuration data analysis chartData state).comp
      (globalPairedAbelianBRSTStateLinearEquiv period hPeriod).symm.toLinearMap

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPairedAbelianProductEuler_first
    (state : FullChart period hPeriod configuration data analysis chartData) :
    productCovectorFirst
        (globalCandidateAGaugeFixedNonlinearFullBRSTPairedAbelianProductEulerCovector
          period hPeriod configuration data analysis chartData state) =
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector period
        hPeriod configuration data analysis chartData state := by
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPairedAbelianProductEuler_second
    (state : FullChart period hPeriod configuration data analysis chartData) :
    productCovectorSecond
        (globalCandidateAGaugeFixedNonlinearFullBRSTPairedAbelianProductEulerCovector
          period hPeriod configuration data analysis chartData state) =
      globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalEulerCovector
        period hPeriod configuration data analysis chartData state := by
  rfl

/-- The paired Abelian equation is exactly its shared-potential and
nonminimal restrictions. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTPairedAbelianEulerCovector_eq_zero_iff
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPairedAbelianEulerCovector period
        hPeriod configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector period
          hPeriod configuration data analysis chartData state = 0 ∧
        globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalEulerCovector
          period hPeriod configuration data analysis chartData state = 0 := by
  calc
    _ ↔
        globalCandidateAGaugeFixedNonlinearFullBRSTPairedAbelianProductEulerCovector
          period hPeriod configuration data analysis chartData state = 0 := by
      symm
      exact covector_comp_equiv_symm_eq_zero_iff
        (globalPairedAbelianBRSTStateLinearEquiv period hPeriod)
        (globalCandidateAGaugeFixedNonlinearFullBRSTPairedAbelianEulerCovector
          period hPeriod configuration data analysis chartData state)
    _ ↔ _ := by
      rw [productCovector_eq_zero_iff,
        globalCandidateAGaugeFixedNonlinearFullBRSTPairedAbelianProductEuler_first,
        globalCandidateAGaugeFixedNonlinearFullBRSTPairedAbelianProductEuler_second]

/-- Four exact restrictions of the full-BRST Euler equation. -/
def GlobalCandidateAGaugeFixedNonlinearFullBRSTRefinedCoreEulerSystemAt
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Prop :=
  globalCandidateAGaugeFixedNonlinearFullBRSTGaugeFreePhysicalEulerCovector
      period hPeriod configuration data analysis chartData state = 0 ∧
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalEulerCovector
        period hPeriod configuration data analysis chartData state = 0 ∧
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector period
          hPeriod configuration data analysis chartData state = 0 ∧
        globalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalEulerCovector
          period hPeriod configuration data analysis chartData state = 0

/-- Exact criticality is equivalent to the refined four-part system. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_refinedCoreEulerSystem
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTRefinedCoreEulerSystemAt
        period hPeriod configuration data analysis chartData state := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_coreEulerSystem]
  unfold GlobalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerSystemAt
    GlobalCandidateAGaugeFixedNonlinearFullBRSTRefinedCoreEulerSystemAt
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTPairedAbelianEulerCovector_eq_zero_iff]

/-- Gate 227: the paired Abelian state splits exactly into the coupled
potential equation and the pure BRST nonminimal equation. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_pairedAbelian_nonminimal_euler_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTRefinedCoreEulerSystemAt
        period hPeriod configuration data analysis chartData state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_refinedCoreEulerSystem
    period hPeriod configuration data analysis chartData state

end NonminimalEuler

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianNonminimalEuler4D
end JanusFormal
