import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaugeFixedSmoothTangentL2Pairing4D

/-!
# Faithful L2--Robin augmented residual of the full-BRST normal equation

Normal tests retain their injective two-sheet orientation-double `L²`
coordinate together with the authentic Robin action covector. The remaining
physical cross-block is appended as a scalar coordinate. This exact graph
certificate does not identify the Robin covector with a local `L²` PDE.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory Topology
open scoped ENNReal Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusScalarRobinJunctionL2Fredholm4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalRobinNormalCrossBlockDecomposition4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNonminimalStrongSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalStrongSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTRemainingPhysicalScalarGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaugeFixedSmoothTangentL2Pairing4D
open P0EFTJanusProgramPStateDependentAugmentedGraphRieszResidual4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldNormalL2RobinResidual :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev OrientationNormalL2 :=
  ThroatScalarL2
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
    (intrinsicCanonicalThroatVolumeMeasure
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod))

private abbrev PairedNormalL2 :=
  WithLp 2
    (OrientationNormalL2 period hPeriod × OrientationNormalL2 period hPeriod)

private abbrev NormalL2RobinBase :=
  WithLp 2 (PairedNormalL2 period hPeriod × Real)

local instance effectiveQuotientChartedSpaceNormalL2RobinResidual :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldNormalL2RobinResidual :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceNormalL2RobinResidual :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceNormalL2RobinResidual :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance orientationCanonicalVolumeFiniteNormalL2RobinResidual :
    IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section NormalL2RobinResidual

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

/-- Faithful two-sheet `L²` realization of pure normal tests. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2LinearMap :
    GlobalMinimalPhysicalNormalTest period hPeriod →ₗ[Real]
      PairedNormalL2 period hPeriod where
  toFun normal :=
    WithLp.toLp 2
      (candidateANormalBoundaryNormalL2LinearMap period hPeriod (normal .plus),
        candidateANormalBoundaryNormalL2LinearMap period hPeriod
          (normal .minus))
  map_add' first second := by
    apply WithLp.ofLp_injective 2
    simp
  map_smul' scalar normal := by
    apply WithLp.ofLp_injective 2
    simp

theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2LinearMap_injective :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2LinearMap period
        hPeriod) := by
  intro first second hEqual
  funext sector
  cases sector with
  | plus =>
      apply candidateANormalBoundaryNormalL2LinearMap_injective period hPeriod
      exact congrArg WithLp.fst hEqual
  | minus =>
      apply candidateANormalBoundaryNormalL2LinearMap_injective period hPeriod
      exact congrArg WithLp.snd hEqual

/-- The faithful normal `L²` coordinate together with the authentic Robin
action covector at the current physical chart point. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinBaseMap
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalMinimalPhysicalNormalTest period hPeriod →ₗ[Real]
      NormalL2RobinBase period hPeriod where
  toFun normal :=
    WithLp.toLp 2
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2LinearMap period
          hPeriod normal,
        globalCandidateAMinimalPhysicalRobinBlockNormalEulerCovectorAt period
          hPeriod configuration data analysis chartData
          (PhysicalPoint period hPeriod configuration data analysis chartData
            state) normal)
  map_add' first second := by
    apply WithLp.ofLp_injective 2
    simp
  map_smul' scalar normal := by
    apply WithLp.ofLp_injective 2
    simp

theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinBaseMap_injective
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinBaseMap period
        hPeriod configuration data analysis chartData state) := by
  intro first second hEqual
  apply
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalPairedL2LinearMap_injective
      period hPeriod
  simpa [globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinBaseMap] using
    congrArg WithLp.fst hEqual

def globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphData
    (state : FullChart period hPeriod configuration data analysis chartData) :
    StateDependentAugmentedGraphRieszData
      (Test := GlobalMinimalPhysicalNormalTest period hPeriod)
      (Base := NormalL2RobinBase period hPeriod) where
  baseMap :=
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinBaseMap period
      hPeriod configuration data analysis chartData state
  remainder :=
    globalCandidateAMinimalPhysicalNormalCrossBlockEulerCovectorAt period
      hPeriod configuration data analysis chartData
      (PhysicalPoint period hPeriod configuration data analysis chartData state)
  baseCovector :=
    WithLp.sndL 2 Real (PairedNormalL2 period hPeriod) Real

theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphLinearMap_injective
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Function.Injective
      (stateDependentAugmentedGraphLinearMap
        (Base := NormalL2RobinBase period hPeriod)
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphData
          period hPeriod configuration data analysis chartData state)) := by
  intro first second hEqual
  apply
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinBaseMap_injective
      period hPeriod configuration data analysis chartData state
  simpa [stateDependentAugmentedGraphLinearMap,
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphData] using
      congrArg WithLp.fst hEqual

abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphHilbert
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  StateDependentAugmentedGraphHilbert
    (Base := NormalL2RobinBase period hPeriod)
    (globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphData
      period hPeriod configuration data analysis chartData state)

def globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphHilbert
      period hPeriod configuration data analysis chartData state :=
  stateDependentAugmentedGraphRieszResidual
    (Base := NormalL2RobinBase period hPeriod)
    (globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphData
      period hPeriod configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector_eq_l2RobinAugmentedTotalCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector period hPeriod
        configuration data analysis chartData state =
      stateDependentAugmentedTotalCovector
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphData
          period hPeriod configuration data analysis chartData state) := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector_eq]
  apply LinearMap.ext
  intro normal
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector_eq_zero_iff_l2RobinAugmentedGraphResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector period hPeriod
          configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 := by
  unfold
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual
  constructor
  · intro hEuler
    apply (stateDependentAugmentedTotalCovector_eq_zero_iff_graphResidual
      (Base := NormalL2RobinBase period hPeriod)
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphData
        period hPeriod configuration data analysis chartData state)).mp
    calc
      _ = globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector period
            hPeriod configuration data analysis chartData state :=
        (globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector_eq_l2RobinAugmentedTotalCovector
          period hPeriod configuration data analysis chartData state).symm
      _ = 0 := hEuler
  · intro hResidual
    calc
      _ = stateDependentAugmentedTotalCovector
            (globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphData
              period hPeriod configuration data analysis chartData state) :=
        globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector_eq_l2RobinAugmentedTotalCovector
          period hPeriod configuration data analysis chartData state
      _ = 0 :=
        (stateDependentAugmentedTotalCovector_eq_zero_iff_graphResidual
          (Base := NormalL2RobinBase period hPeriod)
          (globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphData
            period hPeriod configuration data analysis chartData state)).mpr
              hResidual

def GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricNormalAugmentedGraphResidualEulerSystemAt
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Prop :=
  globalCandidateAGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 ∧
    globalCandidateAGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual
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

theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_metricNormalAugmentedGraphResidualEulerSystem
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricNormalAugmentedGraphResidualEulerSystemAt
        period hPeriod configuration data analysis chartData state := by
  constructor
  · intro hCritical
    rcases
        (globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_metricAugmentedGraphResidualEulerSystem
          period hPeriod configuration data analysis chartData state).mp hCritical with
      ⟨hMetric, hNormal, hPhysicalGhost, hLLAux, hLLMeasure, hLLField,
        hSpinC, hDiffeomorphism, hPotential, hAbelian⟩
    have hNormalEuler :=
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector_eq_zero_iff_scalarGraphResidual
        period hPeriod configuration data analysis chartData state).mpr hNormal
    exact ⟨
      hMetric,
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector_eq_zero_iff_l2RobinAugmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mp
          hNormalEuler,
      hPhysicalGhost, hLLAux, hLLMeasure, hLLField, hSpinC,
      hDiffeomorphism, hPotential, hAbelian⟩
  · intro hSystem
    rcases hSystem with
      ⟨hMetric, hNormal, hPhysicalGhost, hLLAux, hLLMeasure, hLLField,
        hSpinC, hDiffeomorphism, hPotential, hAbelian⟩
    have hNormalEuler :=
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector_eq_zero_iff_l2RobinAugmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mpr hNormal
    apply
      (globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_metricAugmentedGraphResidualEulerSystem
        period hPeriod configuration data analysis chartData state).mpr
    exact ⟨
      hMetric,
      (globalCandidateAGaugeFixedNonlinearFullBRSTNormalEulerCovector_eq_zero_iff_scalarGraphResidual
        period hPeriod configuration data analysis chartData state).mp
          hNormalEuler,
      hPhysicalGhost, hLLAux, hLLMeasure, hLLField, hSpinC,
      hDiffeomorphism, hPotential, hAbelian⟩

theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_metricNormalAugmentedGraphResidualEulerSystem
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hCritical : GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period
      hPeriod configuration data analysis chartData state) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricNormalAugmentedGraphResidualEulerSystemAt
      period hPeriod configuration data analysis chartData state :=
  (globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_metricNormalAugmentedGraphResidualEulerSystem
    period hPeriod configuration data analysis chartData state).mp hCritical

/-- Gate 258: the exact ten-block residual system now retains the faithful
two-sheet normal `L²` coordinate and the authentic Robin action covector. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_normal_l2_robin_augmented_graph_riesz_residual_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricNormalAugmentedGraphResidualEulerSystemAt
        period hPeriod configuration data analysis chartData state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_metricNormalAugmentedGraphResidualEulerSystem
    period hPeriod configuration data analysis chartData state

end NormalL2RobinResidual

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual4D
end JanusFormal
