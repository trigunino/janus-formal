import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbertComponentPDEPairing4D

/-!
# Linearization of the reduced nonlinear Hilbert residual

The derivative of the reduced Euler covector is the genuine local Hessian
pulled through the reduced Hilbert chart.  Its Riesz representative is the
derivative of the reduced strong residual and agrees on the smooth core with
the covariant minimal-physical Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertLinearization4D

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
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertResidual4D

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

private def realRieszInverseCLM
    (H : Type*) [NormedAddCommGroup H] [InnerProductSpace Real H]
    [CompleteSpace H] : (H →L[Real] Real) →L[Real] H :=
  (InnerProductSpace.toDual Real H).symm.toContinuousLinearEquiv.toContinuousLinearMap

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

/-- Genuine local Hessian pulled through the reduced realization in both
slots. -/
noncomputable def globalCandidateAMinimalPhysicalReducedNonlinearHilbertHessian
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod configuration
        data analysis →L[Real]
      GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod configuration
        data analysis →L[Real] Real :=
  ((ContinuousLinearMap.compL Real
      (GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
        configuration data analysis)
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData).Model Real).flip
          (globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
            hPeriod configuration data analysis chartData reducedChart)).comp
    ((globalCandidateALocalHessian period hPeriod
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
        configuration data analysis chartData reducedChart state)).comp
      (globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
        hPeriod configuration data analysis chartData reducedChart))

theorem globalCandidateAMinimalPhysicalReducedHilbertEulerCovector_hasFDerivAt
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)
    (hState : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
      hPeriod configuration data analysis chartData reducedChart state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).family.domain) :
    HasFDerivAt
      (globalCandidateAMinimalPhysicalReducedHilbertEulerCovector period hPeriod
        configuration data analysis chartData reducedChart)
      (globalCandidateAMinimalPhysicalReducedNonlinearHilbertHessian period
        hPeriod configuration data analysis chartData reducedChart state)
      state := by
  have hEuler :=
    (globalCandidateALocalHessian_hasFDerivAt period hPeriod
      (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
        configuration data analysis chartData)
      (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
        configuration data analysis chartData reducedChart state) hState).comp
      state
      ((globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
        hPeriod configuration data analysis chartData reducedChart).hasFDerivAt.const_add
          (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
            configuration data analysis chartData).chartBridge.basePoint)
  have hConstant : HasFDerivAt
      (fun _ : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
          configuration data analysis ↦
        globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
          hPeriod configuration data analysis chartData reducedChart)
      0 state :=
    hasFDerivAt_const (𝕜 := Real) _ state
  have hComposed := hEuler.clm_comp hConstant
  simp only [ContinuousLinearMap.comp_zero, zero_add] at hComposed
  convert hComposed using 1 <;> rfl

theorem globalCandidateAMinimalPhysicalReducedHilbertEulerCovector_fderiv
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)
    (hState : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
      hPeriod configuration data analysis chartData reducedChart state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).family.domain) :
    fderiv Real
        (globalCandidateAMinimalPhysicalReducedHilbertEulerCovector period hPeriod
          configuration data analysis chartData reducedChart) state =
      globalCandidateAMinimalPhysicalReducedNonlinearHilbertHessian period
        hPeriod configuration data analysis chartData reducedChart state :=
  (globalCandidateAMinimalPhysicalReducedHilbertEulerCovector_hasFDerivAt period
    hPeriod configuration data analysis chartData reducedChart state hState).fderiv

theorem globalCandidateAMinimalPhysicalReducedNonlinearHilbertHessian_pairing
    (state first second : GlobalCandidateAMinimalPhysicalReducedHilbert period
      hPeriod configuration data analysis) :
    globalCandidateAMinimalPhysicalReducedNonlinearHilbertHessian period hPeriod
        configuration data analysis chartData reducedChart state first second =
      globalCandidateALocalHessian period hPeriod
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalReducedHilbertChartPoint period hPeriod
          configuration data analysis chartData reducedChart state)
        (globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
          hPeriod configuration data analysis chartData reducedChart first)
        (globalCandidateAMinimalPhysicalReducedHilbertChartRealization period
          hPeriod configuration data analysis chartData reducedChart second) := by
  rfl

theorem globalCandidateAMinimalPhysicalReducedNonlinearHilbertHessian_symmetric
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)
    (hState : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
      hPeriod configuration data analysis chartData reducedChart state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).family.domain)
    (first second : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) :
    globalCandidateAMinimalPhysicalReducedNonlinearHilbertHessian period hPeriod
        configuration data analysis chartData reducedChart state first second =
      globalCandidateAMinimalPhysicalReducedNonlinearHilbertHessian period hPeriod
        configuration data analysis chartData reducedChart state second first := by
  rw [globalCandidateAMinimalPhysicalReducedNonlinearHilbertHessian_pairing,
    globalCandidateAMinimalPhysicalReducedNonlinearHilbertHessian_pairing]
  exact globalCandidateALocalHessian_symmetric period hPeriod _ _ hState _ _

/-- Riesz representative of the reduced nonlinear Hessian. -/
noncomputable def globalCandidateAMinimalPhysicalReducedNonlinearHilbertRieszLinearization
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis) :
    GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod configuration
        data analysis →L[Real]
      GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod configuration
        data analysis :=
  (realRieszInverseCLM
    (GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod configuration
      data analysis)).comp
    (globalCandidateAMinimalPhysicalReducedNonlinearHilbertHessian period hPeriod
      configuration data analysis chartData reducedChart state)

theorem globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_hasFDerivAt
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)
    (hState : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
      hPeriod configuration data analysis chartData reducedChart state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).family.domain) :
    HasFDerivAt
      (globalCandidateAMinimalPhysicalReducedHilbertRieszResidual period hPeriod
        configuration data analysis chartData reducedChart)
      (globalCandidateAMinimalPhysicalReducedNonlinearHilbertRieszLinearization
        period hPeriod configuration data analysis chartData reducedChart state)
      state := by
  let rieszInverse := realRieszInverseCLM
    (GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod configuration
      data analysis)
  have hRiesz : HasFDerivAt (fun covector ↦ rieszInverse covector) rieszInverse
      (globalCandidateAMinimalPhysicalReducedHilbertEulerCovector period hPeriod
        configuration data analysis chartData reducedChart state) :=
    rieszInverse.hasFDerivAt
  have hDerivative := hRiesz.comp state
    (globalCandidateAMinimalPhysicalReducedHilbertEulerCovector_hasFDerivAt period
      hPeriod configuration data analysis chartData reducedChart state hState)
  convert hDerivative using 1 <;> rfl

theorem globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_fderiv
    (state : GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod
      configuration data analysis)
    (hState : globalCandidateAMinimalPhysicalReducedHilbertChartPoint period
      hPeriod configuration data analysis chartData reducedChart state ∈
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData).family.domain) :
    fderiv Real
        (globalCandidateAMinimalPhysicalReducedHilbertRieszResidual period hPeriod
          configuration data analysis chartData reducedChart) state =
      globalCandidateAMinimalPhysicalReducedNonlinearHilbertRieszLinearization
        period hPeriod configuration data analysis chartData reducedChart state :=
  (globalCandidateAMinimalPhysicalReducedHilbertRieszResidual_hasFDerivAt period
    hPeriod configuration data analysis chartData reducedChart state hState).fderiv

theorem globalCandidateAMinimalPhysicalReducedNonlinearHilbertRieszLinearization_pairing
    (state first second : GlobalCandidateAMinimalPhysicalReducedHilbert period
      hPeriod configuration data analysis) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedNonlinearHilbertRieszLinearization
          period hPeriod configuration data analysis chartData reducedChart state
            first) second =
      globalCandidateAMinimalPhysicalReducedNonlinearHilbertHessian period hPeriod
        configuration data analysis chartData reducedChart state first second := by
  unfold globalCandidateAMinimalPhysicalReducedNonlinearHilbertRieszLinearization
  exact InnerProductSpace.toDual_symm_apply

@[simp]
theorem globalCandidateAMinimalPhysicalReducedHilbertChartRealization_smooth
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateAMinimalPhysicalReducedHilbertChartRealization period hPeriod
        configuration data analysis chartData reducedChart
        (globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding period hPeriod
          configuration data analysis core) =
      globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData) core := by
  rw [← globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding_mk]
  rw [globalCandidateAMinimalPhysicalReducedHilbertChartRealization_core]
  rw [globalCandidateAMinimalPhysicalReducedCoreToChart_mk]

/-- On raw smooth directions the reduced Hessian is exactly the genuine
minimal-physical covariant Hessian. -/
theorem globalCandidateAMinimalPhysicalReducedNonlinearHilbertHessian_smooth_eq_covariant
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    globalCandidateAMinimalPhysicalReducedNonlinearHilbertHessian period hPeriod
        configuration data analysis chartData reducedChart 0
        (globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding period hPeriod
          configuration data analysis first)
        (globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding period hPeriod
          configuration data analysis second) =
      diagonalExtendedBulkMinimalPhysicalLocalCovariantHessianOnCore period
        hPeriod configuration data analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData).chartBridge first second := by
  rw [globalCandidateAMinimalPhysicalReducedNonlinearHilbertHessian_pairing]
  simp only [globalCandidateAMinimalPhysicalReducedHilbertChartPoint, map_zero,
    add_zero]
  rw [globalCandidateAMinimalPhysicalReducedHilbertChartRealization_smooth,
    globalCandidateAMinimalPhysicalReducedHilbertChartRealization_smooth]
  rfl

theorem globalCandidateAMinimalPhysicalReducedNonlinearHilbertRieszLinearization_smooth_pairing
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedNonlinearHilbertRieszLinearization
          period hPeriod configuration data analysis chartData reducedChart 0
          (globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding period hPeriod
            configuration data analysis first))
        (globalCandidateAMinimalPhysicalReducedSmoothCoreEmbedding period hPeriod
          configuration data analysis second) =
      diagonalExtendedBulkMinimalPhysicalLocalCovariantHessianOnCore period
        hPeriod configuration data analysis
        (globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
          configuration data analysis chartData)
        (globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
          configuration data analysis chartData).chartBridge first second := by
  rw [globalCandidateAMinimalPhysicalReducedNonlinearHilbertRieszLinearization_pairing]
  exact globalCandidateAMinimalPhysicalReducedNonlinearHilbertHessian_smooth_eq_covariant
    period hPeriod configuration data analysis chartData reducedChart first second

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedNonlinearHilbertLinearization4D
end JanusFormal
