import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2Faithfulness4D

/-!
# Faithful L2 augmented residual of the full-BRST physical ghost equation

Pure physical diffeomorphism-ghost tests retain their injective two-sector
finite-frame `L²` coordinate together with the authentic action covector.  The
BRST remainder is exactly zero.  This is not a local Faddeev--Popov PDE.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory Topology
open scoped ENNReal Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
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
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNonminimalStrongSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalStrongSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTRemainingPhysicalScalarGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2Faithfulness4D
open P0EFTJanusProgramPStateDependentAugmentedGraphRieszResidual4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldPhysicalGhostL2Residual :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev PairedPhysicalGhostL2 :=
  WithLp 2
    (PhysicalGhostFiniteFrameL2 period hPeriod ×
      PhysicalGhostFiniteFrameL2 period hPeriod)

private abbrev PhysicalGhostL2EulerBase :=
  WithLp 2 (PairedPhysicalGhostL2 period hPeriod × Real)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance : ChartedSpace ThroatCoverModel
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance : IsManifold throatCoverModelWithCorners ω
    (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section PhysicalGhostL2Residual

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

/-- Faithful finite-frame `L²` realization of both physical ghost sectors. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2LinearMap :
    GlobalMinimalPhysicalDiffeomorphismGhostTest period hPeriod →ₗ[Real]
      PairedPhysicalGhostL2 period hPeriod where
  toFun ghost := WithLp.toLp 2
    (physicalGhostFiniteFrameL2LinearMap period hPeriod (ghost .plus),
      physicalGhostFiniteFrameL2LinearMap period hPeriod (ghost .minus))
  map_add' first second := by
    apply WithLp.ofLp_injective 2
    simp
  map_smul' scalar ghost := by
    apply WithLp.ofLp_injective 2
    simp

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2LinearMap_injective :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2LinearMap
        period hPeriod) := by
  intro first second hEqual
  funext sector
  cases sector with
  | plus =>
      apply physicalGhostFiniteFrameL2LinearMap_injective period hPeriod
      exact congrArg WithLp.fst hEqual
  | minus =>
      apply physicalGhostFiniteFrameL2LinearMap_injective period hPeriod
      exact congrArg WithLp.snd hEqual

/-- Faithful `L²` coordinates paired with the authentic physical ghost
covector. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerBaseMap
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalMinimalPhysicalDiffeomorphismGhostTest period hPeriod →ₗ[Real]
      PhysicalGhostL2EulerBase period hPeriod where
  toFun ghost := WithLp.toLp 2
    (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2LinearMap
        period hPeriod ghost,
      globalCandidateAMinimalPhysicalDiffeomorphismGhostEulerCovectorAt period
        hPeriod configuration data analysis chartData
        (PhysicalPoint period hPeriod configuration data analysis chartData
          state) ghost)
  map_add' first second := by
    apply WithLp.ofLp_injective 2
    simp
  map_smul' scalar ghost := by
    apply WithLp.ofLp_injective 2
    simp

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerBaseMap_injective
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerBaseMap
        period hPeriod configuration data analysis chartData state) := by
  intro first second hEqual
  apply
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostPairedL2LinearMap_injective
      period hPeriod
  simpa [globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerBaseMap]
    using congrArg WithLp.fst hEqual

def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphData
    (state : FullChart period hPeriod configuration data analysis chartData) :
    StateDependentAugmentedGraphRieszData
      (Test := GlobalMinimalPhysicalDiffeomorphismGhostTest period hPeriod)
      (Base := PhysicalGhostL2EulerBase period hPeriod) where
  baseMap :=
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerBaseMap
      period hPeriod configuration data analysis chartData state
  remainder := 0
  baseCovector :=
    WithLp.sndL 2 Real (PairedPhysicalGhostL2 period hPeriod) Real

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphLinearMap_injective
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Function.Injective
      (stateDependentAugmentedGraphLinearMap
        (Base := PhysicalGhostL2EulerBase period hPeriod)
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphData
          period hPeriod configuration data analysis chartData state)) := by
  intro first second hEqual
  apply
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerBaseMap_injective
      period hPeriod configuration data analysis chartData state
  simpa [stateDependentAugmentedGraphLinearMap,
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphData]
    using congrArg WithLp.fst hEqual

abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphHilbert
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  StateDependentAugmentedGraphHilbert
    (Base := PhysicalGhostL2EulerBase period hPeriod)
    (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphData
      period hPeriod configuration data analysis chartData state)

def globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphHilbert
      period hPeriod configuration data analysis chartData state :=
  stateDependentAugmentedGraphRieszResidual
    (Base := PhysicalGhostL2EulerBase period hPeriod)
    (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphData
      period hPeriod configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostEulerCovector_eq_l2AugmentedTotalCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector
        period hPeriod configuration data analysis chartData state =
      stateDependentAugmentedTotalCovector
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphData
          period hPeriod configuration data analysis chartData state) := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector_eq]
  apply LinearMap.ext
  intro ghost
  simp [stateDependentAugmentedTotalCovector,
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphData,
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2EulerBaseMap]

theorem globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostEulerCovector_eq_zero_iff_l2AugmentedGraphResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector
          period hPeriod configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 := by
  unfold
    globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual
  constructor
  · intro hEuler
    apply (stateDependentAugmentedTotalCovector_eq_zero_iff_graphResidual
      (Base := PhysicalGhostL2EulerBase period hPeriod)
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphData
        period hPeriod configuration data analysis chartData state)).mp
    calc
      _ = globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEulerCovector
            period hPeriod configuration data analysis chartData state :=
        (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostEulerCovector_eq_l2AugmentedTotalCovector
          period hPeriod configuration data analysis chartData state).symm
      _ = 0 := hEuler
  · intro hResidual
    calc
      _ = stateDependentAugmentedTotalCovector
            (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphData
              period hPeriod configuration data analysis chartData state) :=
        globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostEulerCovector_eq_l2AugmentedTotalCovector
          period hPeriod configuration data analysis chartData state
      _ = 0 :=
        (stateDependentAugmentedTotalCovector_eq_zero_iff_graphResidual
          (Base := PhysicalGhostL2EulerBase period hPeriod)
          (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphData
            period hPeriod configuration data analysis chartData state)).mpr
              hResidual

def GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricNormalPhysicalGhostL2AugmentedGraphResidualEulerSystemAt
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Prop :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 ∧
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 ∧
      globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual
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

theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_metricNormalPhysicalGhostL2AugmentedGraphResidualEulerSystem
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricNormalPhysicalGhostL2AugmentedGraphResidualEulerSystemAt
        period hPeriod configuration data analysis chartData state := by
  constructor
  · intro hCritical
    rcases
        (globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_metricNormalAugmentedGraphResidualEulerSystem
          period hPeriod configuration data analysis chartData state).mp hCritical with
      ⟨hMetric, hNormal, hPhysicalGhost, hLLAux, hLLMeasure, hLLField,
        hSpinC, hDiffeomorphism, hPotential, hAbelian⟩
    have hPhysicalGhostEuler :=
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostEulerCovector_eq_zero_iff_scalarGraphResidual
        period hPeriod configuration data analysis chartData state).mpr
          hPhysicalGhost
    exact ⟨
      hMetric, hNormal,
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostEulerCovector_eq_zero_iff_l2AugmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mp
          hPhysicalGhostEuler,
      hLLAux, hLLMeasure, hLLField, hSpinC, hDiffeomorphism, hPotential,
      hAbelian⟩
  · rintro ⟨hMetric, hNormal, hPhysicalGhost, hLLAux, hLLMeasure, hLLField,
      hSpinC, hDiffeomorphism, hPotential, hAbelian⟩
    have hPhysicalGhostEuler :=
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostEulerCovector_eq_zero_iff_l2AugmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mpr
          hPhysicalGhost
    apply
      (globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_metricNormalAugmentedGraphResidualEulerSystem
        period hPeriod configuration data analysis chartData state).mpr
    exact ⟨
      hMetric, hNormal,
      (globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalGhostEulerCovector_eq_zero_iff_scalarGraphResidual
        period hPeriod configuration data analysis chartData state).mp
          hPhysicalGhostEuler,
      hLLAux, hLLMeasure, hLLField, hSpinC, hDiffeomorphism, hPotential,
      hAbelian⟩

/-- Gate 261: the exact ten-block system retains a faithful canonical `L²`
coordinate and the authentic covector for the physical ghost. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_physicalGhost_l2_augmented_graph_riesz_residual_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricNormalPhysicalGhostL2AugmentedGraphResidualEulerSystemAt
        period hPeriod configuration data analysis chartData state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_metricNormalPhysicalGhostL2AugmentedGraphResidualEulerSystem
    period hPeriod configuration data analysis chartData state

end PhysicalGhostL2Residual
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual4D
end JanusFormal
