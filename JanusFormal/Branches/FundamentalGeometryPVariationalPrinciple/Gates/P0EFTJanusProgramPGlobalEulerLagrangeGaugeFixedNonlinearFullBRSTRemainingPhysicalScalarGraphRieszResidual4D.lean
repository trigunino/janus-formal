import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAugmentedResidualEulerSystem4D

/-!
# Scalar graph-Riesz residuals for the remaining full-BRST physical equations

The metric, normal and physical diffeomorphism-ghost covectors are retained
exactly on state-dependent scalar graphs. These are separating certificates,
not tensorial, local-PDE or fixed-domain residuals.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTRemainingPhysicalScalarGraphRieszResidual4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalRobinNormalCrossBlockDecomposition4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEinsteinMaxwellMetricCrossBlockDecomposition4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNonminimalStrongSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalStrongSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAugmentedResidualEulerSystem4D
open P0EFTJanusProgramPStateDependentAugmentedGraphRieszResidual4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldRemainingPhysicalScalarResidual :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveQuotientChartedSpaceRemainingPhysicalScalarResidual :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldRemainingPhysicalScalarResidual :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceRemainingPhysicalScalarResidual :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceRemainingPhysicalScalarResidual :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance effectiveThroatChartedSpaceRemainingPhysicalScalarResidual :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifoldRemainingPhysicalScalarResidual :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section RemainingPhysicalScalarResidual

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

private abbrev PhysicalPoint
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
    configuration data analysis chartData state

/-- The authentic Einstein--Maxwell metric block is the first scalar graph
coordinate; the physical cross-block and BRST response form the remainder. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTMetricScalarGraphData
    (state : FullChart period hPeriod configuration data analysis chartData) :
    StateDependentAugmentedGraphRieszData
      (Test := GlobalMinimalPhysicalMetricTest period hPeriod)
      (Base := Real) where
  baseMap :=
    globalCandidateAMinimalPhysicalEinsteinMaxwellBlockMetricEulerCovectorAt
      period hPeriod configuration data analysis chartData
      (PhysicalPoint period hPeriod configuration data analysis chartData state)
  remainder :=
    globalCandidateAMinimalPhysicalMetricCrossBlockEulerCovectorAt period
        hPeriod configuration data analysis chartData
        (PhysicalPoint period hPeriod configuration data analysis chartData
          state) +
      globalCandidateAGaugeFixedNonlinearFullBRSTMetricDiffeomorphismBRSTCovector
        period hPeriod configuration data analysis chartData state
  baseCovector := ContinuousLinearMap.id Real Real

/-- The authentic Robin normal block and its physical cross-block are retained
as the two scalar graph coordinates. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTNormalScalarGraphData
    (state : FullChart period hPeriod configuration data analysis chartData) :
    StateDependentAugmentedGraphRieszData
      (Test := GlobalMinimalPhysicalNormalTest period hPeriod)
      (Base := Real) where
  baseMap :=
    globalCandidateAMinimalPhysicalRobinBlockNormalEulerCovectorAt period
      hPeriod configuration data analysis chartData
      (PhysicalPoint period hPeriod configuration data analysis chartData state)
  remainder :=
    globalCandidateAMinimalPhysicalNormalCrossBlockEulerCovectorAt period
      hPeriod configuration data analysis chartData
      (PhysicalPoint period hPeriod configuration data analysis chartData state)
  baseCovector := ContinuousLinearMap.id Real Real

/-- The physical ghost covector is retained as a scalar graph coordinate; its
BRST remainder already vanishes exactly. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostScalarGraphData
    (state : FullChart period hPeriod configuration data analysis chartData) :
    StateDependentAugmentedGraphRieszData
      (Test := GlobalMinimalPhysicalDiffeomorphismGhostTest period hPeriod)
      (Base := Real) where
  baseMap :=
    globalCandidateAMinimalPhysicalDiffeomorphismGhostEulerCovectorAt period
      hPeriod configuration data analysis chartData
      (PhysicalPoint period hPeriod configuration data analysis chartData state)
  remainder := 0
  baseCovector := ContinuousLinearMap.id Real Real

abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricScalarGraphHilbert
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  StateDependentAugmentedGraphHilbert (Base := Real)
    (globalCandidateAGaugeFixedNonlinearFullBRSTMetricScalarGraphData period
      hPeriod configuration data analysis chartData state)

abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalScalarGraphHilbert
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  StateDependentAugmentedGraphHilbert (Base := Real)
    (globalCandidateAGaugeFixedNonlinearFullBRSTNormalScalarGraphData period
      hPeriod configuration data analysis chartData state)

abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostScalarGraphHilbert
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  StateDependentAugmentedGraphHilbert (Base := Real)
    (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostScalarGraphData
      period hPeriod configuration data analysis chartData state)

def globalCandidateAGaugeFixedNonlinearFullBRSTMetricScalarGraphRieszResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricScalarGraphHilbert period
      hPeriod configuration data analysis chartData state :=
  stateDependentAugmentedGraphRieszResidual (Base := Real)
    (globalCandidateAGaugeFixedNonlinearFullBRSTMetricScalarGraphData period
      hPeriod configuration data analysis chartData state)

def globalCandidateAGaugeFixedNonlinearFullBRSTNormalScalarGraphRieszResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalScalarGraphHilbert period
      hPeriod configuration data analysis chartData state :=
  stateDependentAugmentedGraphRieszResidual (Base := Real)
    (globalCandidateAGaugeFixedNonlinearFullBRSTNormalScalarGraphData period
      hPeriod configuration data analysis chartData state)

def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostScalarGraphRieszResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostScalarGraphHilbert
      period hPeriod configuration data analysis chartData state :=
  stateDependentAugmentedGraphRieszResidual (Base := Real)
    (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostScalarGraphData
      period hPeriod configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector_eq_scalarGraphTotalCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector period hPeriod
        configuration data analysis chartData state =
      stateDependentAugmentedTotalCovector
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricScalarGraphData period
          hPeriod configuration data analysis chartData state) := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector_eq]
  apply LinearMap.ext
  intro test
  simp [stateDependentAugmentedTotalCovector,
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricScalarGraphData,
    add_assoc]

theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector_eq_scalarGraphTotalCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector period hPeriod
        configuration data analysis chartData state =
      stateDependentAugmentedTotalCovector
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalScalarGraphData period
          hPeriod configuration data analysis chartData state) := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector_eq]
  apply LinearMap.ext
  intro test
  simp [stateDependentAugmentedTotalCovector,
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalScalarGraphData]

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostEulerCovector_eq_scalarGraphTotalCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector
        period hPeriod configuration data analysis chartData state =
      stateDependentAugmentedTotalCovector
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostScalarGraphData
          period hPeriod configuration data analysis chartData state) := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector_eq]
  apply LinearMap.ext
  intro test
  simp [stateDependentAugmentedTotalCovector,
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostScalarGraphData]

theorem globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector_eq_zero_iff_scalarGraphResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector period hPeriod
          configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTMetricScalarGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTMetricScalarGraphRieszResidual
  constructor
  · intro hEuler
    apply (stateDependentAugmentedTotalCovector_eq_zero_iff_graphResidual
      (Base := Real)
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricScalarGraphData period
        hPeriod configuration data analysis chartData state)).mp
    calc
      _ = globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector period
            hPeriod configuration data analysis chartData state :=
        (globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector_eq_scalarGraphTotalCovector
          period hPeriod configuration data analysis chartData state).symm
      _ = 0 := hEuler
  · intro hResidual
    calc
      _ = stateDependentAugmentedTotalCovector
            (globalCandidateAGaugeFixedNonlinearFullBRSTMetricScalarGraphData
              period hPeriod configuration data analysis chartData state) :=
        globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector_eq_scalarGraphTotalCovector
          period hPeriod configuration data analysis chartData state
      _ = 0 :=
        (stateDependentAugmentedTotalCovector_eq_zero_iff_graphResidual
          (Base := Real)
          (globalCandidateAGaugeFixedNonlinearFullBRSTMetricScalarGraphData
            period hPeriod configuration data analysis chartData state)).mpr
              hResidual

theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector_eq_zero_iff_scalarGraphResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector period hPeriod
          configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTNormalScalarGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 := by
  unfold globalCandidateAGaugeFixedNonlinearFullBRSTNormalScalarGraphRieszResidual
  constructor
  · intro hEuler
    apply (stateDependentAugmentedTotalCovector_eq_zero_iff_graphResidual
      (Base := Real)
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalScalarGraphData period
        hPeriod configuration data analysis chartData state)).mp
    calc
      _ = globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector period
            hPeriod configuration data analysis chartData state :=
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector_eq_scalarGraphTotalCovector
          period hPeriod configuration data analysis chartData state).symm
      _ = 0 := hEuler
  · intro hResidual
    calc
      _ = stateDependentAugmentedTotalCovector
            (globalCandidateAGaugeFixedNonlinearFullBRSTNormalScalarGraphData
              period hPeriod configuration data analysis chartData state) :=
        globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector_eq_scalarGraphTotalCovector
          period hPeriod configuration data analysis chartData state
      _ = 0 :=
        (stateDependentAugmentedTotalCovector_eq_zero_iff_graphResidual
          (Base := Real)
          (globalCandidateAGaugeFixedNonlinearFullBRSTNormalScalarGraphData
            period hPeriod configuration data analysis chartData state)).mpr
              hResidual

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostEulerCovector_eq_zero_iff_scalarGraphResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector
          period hPeriod configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostScalarGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 := by
  unfold
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostScalarGraphRieszResidual
  constructor
  · intro hEuler
    apply (stateDependentAugmentedTotalCovector_eq_zero_iff_graphResidual
      (Base := Real)
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostScalarGraphData
        period hPeriod configuration data analysis chartData state)).mp
    calc
      _ = globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector
            period hPeriod configuration data analysis chartData state :=
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostEulerCovector_eq_scalarGraphTotalCovector
          period hPeriod configuration data analysis chartData state).symm
      _ = 0 := hEuler
  · intro hResidual
    calc
      _ = stateDependentAugmentedTotalCovector
            (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostScalarGraphData
              period hPeriod configuration data analysis chartData state) :=
        globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostEulerCovector_eq_scalarGraphTotalCovector
          period hPeriod configuration data analysis chartData state
      _ = 0 :=
        (stateDependentAugmentedTotalCovector_eq_zero_iff_graphResidual
          (Base := Real)
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostScalarGraphData
            period hPeriod configuration data analysis chartData state)).mpr
              hResidual

/-- Exact full-BRST system with every component represented by a separating
residual or by one of the two already resolved strong nonminimal systems. -/
def GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphResidualEulerSystemAt
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Prop :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricScalarGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 ∧
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalScalarGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 ∧
      globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostScalarGraphRieszResidual
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

theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_graphResidualEulerSystem
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphResidualEulerSystemAt
        period hPeriod configuration data analysis chartData state := by
  rw [
    globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_augmentedResidualEulerSystem
      period hPeriod configuration data analysis chartData state]
  unfold
    GlobalCandidateAGaugeFixedNonlinearFullBRSTAugmentedResidualEulerSystemAt
    GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphResidualEulerSystemAt
  constructor
  · rintro ⟨hMetric, hNormal, hPhysicalGhost, hLLAux, hLLMeasure,
      hLLField, hSpinC, hDiffeomorphism, hPotential, hAbelian⟩
    exact ⟨
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector_eq_zero_iff_scalarGraphResidual
        period hPeriod configuration data analysis chartData state).mp hMetric,
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector_eq_zero_iff_scalarGraphResidual
        period hPeriod configuration data analysis chartData state).mp hNormal,
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostEulerCovector_eq_zero_iff_scalarGraphResidual
        period hPeriod configuration data analysis chartData state).mp
          hPhysicalGhost,
      hLLAux, hLLMeasure, hLLField, hSpinC, hDiffeomorphism, hPotential,
      hAbelian⟩
  · rintro ⟨hMetric, hNormal, hPhysicalGhost, hLLAux, hLLMeasure,
      hLLField, hSpinC, hDiffeomorphism, hPotential, hAbelian⟩
    exact ⟨
      (globalCandidateAGaugeFixedNonlinearFullBRSTMetricEulerCovector_eq_zero_iff_scalarGraphResidual
        period hPeriod configuration data analysis chartData state).mpr hMetric,
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector_eq_zero_iff_scalarGraphResidual
        period hPeriod configuration data analysis chartData state).mpr hNormal,
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostEulerCovector_eq_zero_iff_scalarGraphResidual
        period hPeriod configuration data analysis chartData state).mpr
          hPhysicalGhost,
      hLLAux, hLLMeasure, hLLField, hSpinC, hDiffeomorphism, hPotential,
      hAbelian⟩

theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_graphResidualEulerSystem
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hCritical : GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period
      hPeriod configuration data analysis chartData state) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphResidualEulerSystemAt period
      hPeriod configuration data analysis chartData state :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_graphResidualEulerSystem
    period hPeriod configuration data analysis chartData state).mp hCritical

/-- Gate 256: every full-BRST component has an exact separating residual
system, with the final three explicitly limited to scalar graph certificates. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_remaining_physical_scalar_graph_riesz_residual_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphResidualEulerSystemAt
        period hPeriod configuration data analysis chartData state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_graphResidualEulerSystem
    period hPeriod configuration data analysis chartData state

end RemainingPhysicalScalarResidual

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTRemainingPhysicalScalarGraphRieszResidual4D
end JanusFormal
