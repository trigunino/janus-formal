import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFactorwiseEulerPairing4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalMaxwellGaugeCrossBlockDecomposition4D

/-!
# Euler equation of the unique paired Abelian potential

Potential-only full-BRST core tests vary the same intrinsic potential in the
physical Maxwell slot and the Abelian BRST graph.  Their exact Euler equation
therefore retains the Maxwell block, the named physical cross-block remainder,
and the Abelian BRST Hessian contribution.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSectorSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalMaxwellGaugeCrossBlockDecomposition4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFactorwiseEulerPairing4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldPotential :
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

local instance effectiveQuotientChartedSpacePotential :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldPotential :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpacePotential :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpacePotential :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatCoverChartedSpacePotential :
    ChartedSpace ThroatCoverModel (EffectiveThroatCover period hPeriod) :=
  fixedThroatCoverChartedSpace period hPeriod

local instance effectiveThroatCoverIsManifoldPotential :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroatCover period hPeriod) :=
  fixedThroatCover_isManifold period hPeriod

local instance effectiveThroatChartedSpacePotential :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifoldPotential :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance canonicalLorentzVolumeFinitePotential :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section PotentialEuler

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

@[implicit_reducible]
local instance (priority := 10003) fullChartAddCommGroupPotential :
    AddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartAddCommGroup period hPeriod (measure := measure)
    configuration data analysis chartData

@[implicit_reducible]
local instance (priority := 10003) fullChartModulePotential :
    Module Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartModule period hPeriod (measure := measure)
    configuration data analysis chartData

/-- Potential-only paired Abelian state. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialOnlyPairedStateLinearMap :
    PairedPotential period hPeriod →ₗ[Real]
      GlobalPairedAbelianBRSTState period hPeriod where
  toFun potential := { potential := potential, nonminimal := 0 }
  map_add' first second := by
    apply GlobalPairedAbelianBRSTState.ext
    · rfl
    · change (0 : Sector → GlobalAbelianNonminimalFields period hPeriod) =
          0 + 0
      simp
  map_smul' scalar potential := by
    apply GlobalPairedAbelianBRSTState.ext
    · rfl
    · change (0 : Sector → GlobalAbelianNonminimalFields period hPeriod) =
          scalar • 0
      simp

/-- Potential-only inclusion into the full-BRST algebraic core. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialOnlyCoreLinearMap :
    PairedPotential period hPeriod →ₗ[Real]
      FullCore period hPeriod configuration where
  toFun potential :=
    (0, (0,
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialOnlyPairedStateLinearMap
        period hPeriod potential))
  map_add' first second := by
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simp
      · exact
          (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialOnlyPairedStateLinearMap
            period hPeriod).map_add first second
  map_smul' scalar potential := by
    apply Prod.ext
    · simp
    · apply Prod.ext
      · simp
      · exact
          (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialOnlyPairedStateLinearMap
            period hPeriod).map_smul scalar potential

/-- Exact full-BRST Euler covector restricted to the shared potential. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    PairedPotential period hPeriod →ₗ[Real] Real :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector period hPeriod
    configuration data analysis chartData state).comp
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialOnlyCoreLinearMap
        period hPeriod configuration)

/-- Physical chart point underlying one full-BRST state. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
    period hPeriod configuration data analysis chartData
    (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection
      period hPeriod configuration data analysis chartData state)

/-- Maxwell-block contribution to the shared-potential Euler covector. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialMaxwellEulerCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    PairedPotential period hPeriod →ₗ[Real] Real :=
  (globalCandidateAMinimalPhysicalMaxwellBlockGaugeEulerCovectorAt period
    hPeriod configuration data analysis chartData
    (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
      configuration data analysis chartData state)).comp
      (globalCandidateAPairedGaugePotentialCoefficientLinearMap period hPeriod
        data)

/-- Cross-block physical contribution to the shared-potential Euler
covector. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialCrossBlockEulerCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    PairedPotential period hPeriod →ₗ[Real] Real :=
  (globalCandidateAMinimalPhysicalGaugeCrossBlockEulerCovectorAt period hPeriod
    configuration data analysis chartData
    (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
      configuration data analysis chartData state)).comp
      (globalCandidateAPairedGaugePotentialCoefficientLinearMap period hPeriod
        data)

/-- Abelian BRST Hessian contribution to the shared-potential Euler
covector. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPotentialAbelianBRSTCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    PairedPotential period hPeriod →ₗ[Real] Real :=
  (globalPairedAbelianOffShellHessian period hPeriod
    (BaseMetric period hPeriod configuration data)
    (globalCandidateAGaugeFixedNonlinearFullBRSTAbelianProjection period
      hPeriod configuration data analysis chartData state)).toLinearMap.comp
      ((globalPairedAbelianOffShellSmoothEmbedding period hPeriod
        (BaseMetric period hPeriod configuration data)).comp
          (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialOnlyPairedStateLinearMap
            period hPeriod))

private theorem abelianBRSTContribution_potentialOnly_eq
    (state : FullChart period hPeriod configuration data analysis chartData)
    (potential : PairedPotential period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTAbelianBRSTContribution period
        hPeriod configuration data analysis chartData state
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialOnlyCoreLinearMap
          period hPeriod configuration potential) =
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialAbelianBRSTCovector
        period hPeriod configuration data analysis chartData state potential := by
  rfl

private theorem localEuler_pairedGaugePotential_eq_gaugeEuler
    (point : (globalCandidateAMinimalPhysicalLocalVariationalChart period
      hPeriod configuration data analysis chartData).Model)
    (potential : PairedPotential period hPeriod) :
    globalCandidateALocalEulerLagrangeOperator period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData) point
        (globalCandidateAMinimalPhysicalChartTangentEquiv period hPeriod
          configuration data analysis chartData
          (globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
            hPeriod data potential)) =
      globalCandidateAMinimalPhysicalGaugeEulerCovectorAt period hPeriod
        configuration data analysis chartData point
        (globalCandidateAPairedGaugePotentialCoefficientLinearMap period
          hPeriod data potential) := by
  rfl

private theorem diffeomorphismBRSTContribution_potentialOnly_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData)
    (potential : PairedPotential period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTContribution
        period hPeriod configuration data analysis chartData state
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialOnlyCoreLinearMap
          period hPeriod configuration potential) = 0 := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismBRSTContribution
  rw [globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTGraphProjection_core]
  have hTestState :
      globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTStateLinearMap
          period hPeriod configuration
          (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
            period hPeriod configuration data
            (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialOnlyCoreLinearMap
              period hPeriod configuration potential)) = 0 := by
    apply GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
    · change
        ((0 : GlobalMinimalPhysicalFieldTangent period hPeriod
              configuration.physical) +
            globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
              hPeriod data potential).1.completeVariation.fullMetricPerturbation =
          0
      rw [zero_add]
      rfl
    · rfl
  rw [hTestState, map_zero, map_zero]

private theorem physicalEulerContribution_potentialOnly_eq_gaugeEuler
    (state : FullChart period hPeriod configuration data analysis chartData)
    (potential : PairedPotential period hPeriod) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalEulerContribution period
        hPeriod configuration data analysis chartData state
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialOnlyCoreLinearMap
          period hPeriod configuration potential) =
      globalCandidateAMinimalPhysicalGaugeEulerCovectorAt period hPeriod
        configuration data analysis chartData
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
          configuration data analysis chartData state)
        (globalCandidateAPairedGaugePotentialCoefficientLinearMap period
          hPeriod data potential) := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalEulerContribution
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint
  rw [globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection_core]
  have hPhysicalTangent :
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismCoreLinearMap
        period hPeriod configuration data
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialOnlyCoreLinearMap
          period hPeriod configuration potential)).1 =
        globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
          hPeriod data potential := by
    change (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration.physical) +
      globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
        hPeriod data potential = _
    exact zero_add _
  rw [hPhysicalTangent]
  exact localEuler_pairedGaugePotential_eq_gaugeEuler period hPeriod
    configuration data analysis chartData _ potential

/-- The shared-potential equation is exactly Maxwell plus the named physical
cross-block term plus Abelian BRST gauge fixing. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector_eq
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector period
        hPeriod configuration data analysis chartData state =
      globalCandidateAGaugeFixedNonlinearFullBRSTPotentialMaxwellEulerCovector
          period hPeriod configuration data analysis chartData state +
        globalCandidateAGaugeFixedNonlinearFullBRSTPotentialCrossBlockEulerCovector
          period hPeriod configuration data analysis chartData state +
        globalCandidateAGaugeFixedNonlinearFullBRSTPotentialAbelianBRSTCovector
          period hPeriod configuration data analysis chartData state := by
  apply LinearMap.ext
  intro potential
  change
    globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector period hPeriod
        configuration data analysis chartData state
        (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialOnlyCoreLinearMap
          period hPeriod configuration potential) = _
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTCoreEulerCovector_apply_eq_factorwise,
    physicalEulerContribution_potentialOnly_eq_gaugeEuler,
    diffeomorphismBRSTContribution_potentialOnly_eq_zero,
    abelianBRSTContribution_potentialOnly_eq,
    globalCandidateAMinimalPhysicalGaugeEulerCovector_decomposition]
  simp only [LinearMap.add_apply, LinearMap.comp_apply,
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialMaxwellEulerCovector,
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialCrossBlockEulerCovector,
    add_zero]

/-- Full criticality forces the exact shared-potential equation. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_potentialEuler_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hCritical :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector period
      hPeriod configuration data analysis chartData state = 0 := by
  have hCore :=
    (globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator_eq_zero_iff_core
      period hPeriod configuration data analysis chartData state).mp hCritical
  apply LinearMap.ext
  intro potential
  have hApply := congrArg
    (fun covector => covector
      (globalCandidateAGaugeFixedNonlinearFullBRSTPotentialOnlyCoreLinearMap
        period hPeriod configuration potential)) hCore
  simpa [globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector]
    using hApply

/-- Gate 226: the unique Abelian potential satisfies its coupled Maxwell,
cross-block and BRST Euler equation at every full-BRST critical state. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_pairedAbelian_potential_euler_gate
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hCritical :
      GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPotentialMaxwellEulerCovector
          period hPeriod configuration data analysis chartData state +
        globalCandidateAGaugeFixedNonlinearFullBRSTPotentialCrossBlockEulerCovector
          period hPeriod configuration data analysis chartData state +
        globalCandidateAGaugeFixedNonlinearFullBRSTPotentialAbelianBRSTCovector
          period hPeriod configuration data analysis chartData state = 0 := by
  rw [← globalCandidateAGaugeFixedNonlinearFullBRSTPotentialEulerCovector_eq]
  exact
    globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_potentialEuler_eq_zero
      period hPeriod configuration data analysis chartData state hCritical

end PotentialEuler

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D
end JanusFormal
