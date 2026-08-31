import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalWeakEightSectorSystem4D

/-!
# Nonlinear Euler residual on the reduced physical Hilbert space

The reduced Hilbert-chart equivalence pulls back the exact local action and
Euler covector.  Frechet--Riesz then gives a strong nonlinear residual whose
pairing on the quotient core is the genuine minimal-chart Euler pairing.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertResidual4D

set_option autoImplicit false
set_option maxHeartbeats 3200000
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
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalWeakEightSectorSystem4D

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
    (chartData : ProgramPGlobalMinimalPhysicalActionChartData4D period hPeriod
      (measure := measure) configuration data analysis)
    (reducedChart : ProgramPGlobalMinimalPhysicalReducedHilbertChart4D period
      hPeriod configuration data analysis chartData)

/-- Bounded realization of the reduced Hilbert space in the minimal chart. -/
def globalCandidateAMinimalPhysicalReducedHilbertChartRealization :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis →L[Real]
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model :=
  reducedChart.toChart.toContinuousLinearMap

@[simp]
theorem globalCandidateAMinimalPhysicalReducedHilbertChartRealization_core
    (core : GlobalCandidateAMinimalPhysicalReducedSmoothCore period hPeriod
      configuration data analysis) :
    globalCandidateAMinimalPhysicalReducedHilbertChartRealization period hPeriod
        configuration data analysis chartData reducedChart
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis core) =
      globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
        configuration data analysis chartData core :=
  reducedChart.quotient_core_compatibility core

/-- Affine chart point represented by a reduced Hilbert state. -/
def globalCandidateAMinimalPhysicalReducedHilbertChartPoint
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) :
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData).Model :=
  (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
    configuration data analysis chartData).chartBridge.basePoint +
      globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
        hPeriod configuration data analysis chartData reducedChart state

/-- Exact nonlinear local action pulled back to the reduced Hilbert space. -/
def globalCandidateAMinimalPhysicalReducedHilbertAction :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis → Real :=
  fun state ↦ globalCandidateALocalActionPullback period hPeriod
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData)
    (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
      configuration data analysis chartData reducedChart state)

/-- Nonlinear Euler covector on the reduced Hilbert carrier. -/
noncomputable def globalCandidateAMinimalPhysicalReducedHilbertEulerCovector
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis →L[Real] Real :=
  (globalCandidateALocalEulerLagrangeOperator period hPeriod
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData)
    (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
      configuration data analysis chartData reducedChart state)).comp
        (globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
          hPeriod configuration data analysis chartData reducedChart)

/-- Strong nonlinear Euler residual on the reduced physical Hilbert space. -/
noncomputable def globalCandidateAMinimalPhysicalReducedHilbertRieszResidual
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis :=
  (InnerProductSpace.toDual Real
    (GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)).symm
        (globalCandidateAMinimalPhysicalReducedHilbertEulerCovector period
          hPeriod configuration data analysis chartData reducedChart state)

def GlobalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) : Prop :=
  globalCandidateAMinimalPhysicalReducedHilbertRieszResidual period hPeriod
    configuration data analysis chartData reducedChart state = 0

theorem globalCandidateAMinimalPhysicalReducedHilbertAction_hasFDerivAt
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)
    (hState : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
      hPeriod configuration data analysis chartData reducedChart state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).family.domain) :
    HasFDerivAt
      (globalCandidateAMinimalPhysicalReducedHilbertAction period hPeriod
        configuration data analysis chartData reducedChart)
      (globalCandidateAMinimalPhysicalReducedHilbertEulerCovector period
        hPeriod configuration data analysis chartData reducedChart state)
      state := by
  have hDerivative :=
    (globalCandidateALocalAction_hasFDerivAt period hPeriod
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
        configuration data analysis chartData reducedChart state) hState).comp
          state
          ((globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
            hPeriod configuration data analysis chartData reducedChart).hasFDerivAt.const_add
                (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period
                  hPeriod configuration data analysis chartData).chartBridge.basePoint)
  convert hDerivative using 1 <;> rfl

theorem globalCandidateAMinimalPhysicalReducedHilbertAction_fderiv
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)
    (hState : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
      hPeriod configuration data analysis chartData reducedChart state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).family.domain) :
    fderiv Real
        (globalCandidateAMinimalPhysicalReducedHilbertAction period hPeriod
          configuration data analysis chartData reducedChart) state =
      globalCandidateAMinimalPhysicalReducedHilbertEulerCovector period hPeriod
        configuration data analysis chartData reducedChart state :=
  (globalCandidateAMinimalPhysicalReducedHilbertAction_hasFDerivAt period
    hPeriod configuration data analysis chartData reducedChart state hState).fderiv

theorem globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_pairing
    (state test : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedHilbertRieszResidual period
          hPeriod configuration data analysis chartData reducedChart state)
        test =
      globalCandidateAMinimalPhysicalReducedHilbertEulerCovector period hPeriod
        configuration data analysis chartData reducedChart state test := by
  unfold globalCandidateAMinimalPhysicalReducedHilbertRieszResidual
  exact InnerProductSpace.toDual_symm_apply

/-- On quotient-core tests the strong residual pairing is exactly the genuine
minimal-chart Euler pairing. -/
theorem globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_pairing_core
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)
    (core : GlobalCandidateAMinimalPhysicalReducedSmoothCore period hPeriod
      configuration data analysis) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedHilbertRieszResidual period
          hPeriod configuration data analysis chartData reducedChart state)
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis core) =
      globalCandidateALocalEulerLagrangeOperator period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
          configuration data analysis chartData reducedChart state)
        (globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
          configuration data analysis chartData core) := by
  rw [globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_pairing]
  exact congrArg
    (globalCandidateALocalEulerLagrangeOperator period hPeriod
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
        configuration data analysis chartData reducedChart state))
    (globalCandidateAMinimalPhysicalReducedHilbertChartRealization_core period
      hPeriod configuration data analysis chartData reducedChart core)

theorem globalCandidateAMinimalPhysicalReducedHilbertAction_fderiv_eq_zero_iff_residual
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)
    (hState : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
      hPeriod configuration data analysis chartData reducedChart state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).family.domain) :
    fderiv Real
        (globalCandidateAMinimalPhysicalReducedHilbertAction period hPeriod
          configuration data analysis chartData reducedChart) state = 0 ↔
      GlobalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical period
        hPeriod configuration data analysis chartData reducedChart state := by
  rw [globalCandidateAMinimalPhysicalReducedHilbertAction_fderiv period hPeriod
    configuration data analysis chartData reducedChart state hState]
  constructor
  · intro hCovector
    unfold GlobalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical
    simp [globalCandidateAMinimalPhysicalReducedHilbertRieszResidual, hCovector]
  · intro hResidual
    apply ContinuousLinearMap.ext
    intro test
    rw [← globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_pairing
      period hPeriod configuration data analysis chartData reducedChart state
      test]
    unfold GlobalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical at hResidual
    rw [hResidual, inner_zero_left]
    rfl

/-- Density of the quotient core makes the strong reduced Euler equation
equivalent to its genuine weak chart equations on every quotient-core test. -/
theorem globalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical_iff_quotientCore
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) :
    GlobalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical period
        hPeriod configuration data analysis chartData reducedChart state ↔
      ∀ core : GlobalCandidateAMinimalPhysicalReducedSmoothCore period
          hPeriod configuration data analysis,
        globalCandidateALocalEulerLagrangeOperator period hPeriod
          (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
            configuration data analysis chartData)
          (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
            hPeriod configuration data analysis chartData reducedChart state)
          (globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
            configuration data analysis chartData core) = 0 := by
  constructor
  · intro hCritical core
    rw [← globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_pairing_core
      period hPeriod configuration data analysis chartData reducedChart state
      core]
    unfold GlobalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical at hCritical
    rw [hCritical, inner_zero_left]
  · intro hCore
    unfold GlobalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical
    apply
      (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_denseRange
        period hPeriod configuration data analysis).eq_zero_of_inner_left
        (𝕜 := Real)
    intro core
    rw [globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_pairing_core]
    exact hCore core

/-- Because the chart realization is an equivalence, the strong reduced
residual vanishes exactly when the genuine local Euler covector vanishes. -/
theorem globalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical_iff_localEuler
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) :
    GlobalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical period
        hPeriod configuration data analysis chartData reducedChart state ↔
      globalCandidateALocalEulerLagrangeOperator period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
          configuration data analysis chartData reducedChart state) = 0 := by
  constructor
  · intro hCritical
    apply ContinuousLinearMap.ext
    intro direction
    obtain ⟨test, hTest⟩ :=
      reducedChart.toChart.surjective direction
    rw [← hTest]
    have hPair :=
      globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_pairing period
        hPeriod configuration data analysis chartData reducedChart state test
    unfold GlobalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical at hCritical
    rw [hCritical, inner_zero_left] at hPair
    simpa [globalCandidateAMinimalPhysicalReducedHilbertEulerCovector,
      globalCandidateAMinimalPhysicalReducedHilbertChartRealization] using
        hPair.symm
  · intro hEuler
    unfold GlobalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical
    simp [globalCandidateAMinimalPhysicalReducedHilbertRieszResidual,
      globalCandidateAMinimalPhysicalReducedHilbertEulerCovector, hEuler]

/-- At every admissible reduced state, strong criticality is exactly the
existing weak eight-sector system of the nine action blocks. -/
theorem globalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical_iff_weakEightSectorSystem
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)
    (hState : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
      hPeriod configuration data analysis chartData reducedChart state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).family.domain) :
    GlobalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical period
        hPeriod configuration data analysis chartData reducedChart state ↔
      GlobalCandidateAMinimalPhysicalWeakEightSectorSystemAt period hPeriod
        configuration data analysis chartData
          (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
            hPeriod configuration data analysis chartData reducedChart state) :=
  (globalCandidateAMinimalPhysicalReducedHilbertIsEulerCritical_iff_localEuler
    period hPeriod configuration data analysis chartData reducedChart state).trans
      (globalCandidateAMinimalPhysicalEuler_eq_zero_iff_weakEightSectorSystem
        period hPeriod configuration data analysis chartData _ hState)

/-- On admissible states the reduced action is the genuine covariant action. -/
theorem globalCandidateAMinimalPhysicalReducedHilbertAction_eq_covariant_of_mem
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)
    (hState : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
      hPeriod configuration data analysis chartData reducedChart state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).family.domain) :
    globalCandidateAMinimalPhysicalReducedHilbertAction period hPeriod
        configuration data analysis chartData reducedChart state =
      globalCandidateACovariantAction period hPeriod
        ((globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).family.datumAt
            (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
              hPeriod configuration data analysis chartData reducedChart state)
            hState).2 measure := by
  exact globalCandidateALocalActionPullback_eq_covariant_of_mem period hPeriod
    (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
      configuration data analysis chartData) _ hState

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertResidual4D
end JanusFormal
