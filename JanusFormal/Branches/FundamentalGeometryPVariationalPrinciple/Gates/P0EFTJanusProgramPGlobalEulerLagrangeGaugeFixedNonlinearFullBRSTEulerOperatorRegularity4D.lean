import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator4D

/-!
# Regularity of the full-BRST Euler operator

The exact full-BRST action is `C²` on its open chart domain. Its Fréchet
derivative is the established Euler operator, which is therefore `C¹` there.
The fixed-ambient residual operator has the same zero locus as that derivative.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTEulerOperatorRegularity4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory Topology
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

section Regularity

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

private abbrev RegularityChartNormedAddCommGroup :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.nonlinearFullBRSTChartNormedAddCommGroupCalculus
    period hPeriod (measure := measure) configuration data analysis chartData

private abbrev RegularityChartNormedSpace :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.nonlinearFullBRSTChartNormedSpaceCalculus
    period hPeriod (measure := measure) configuration data analysis chartData

private abbrev RegularityChartModule :
    Module Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  (RegularityChartNormedSpace period hPeriod configuration data analysis
    chartData).toModule

private abbrev RegularityChartAddCommGroup :
    AddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
    chartData).toAddCommGroup

private abbrev RegularityChartTopologicalSpace :
    TopologicalSpace
      (FullChart period hPeriod configuration data analysis chartData) :=
  (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
    chartData).toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

@[implicit_reducible]
private noncomputable def RegularityChartContinuousSMul :
    @ContinuousSMul Real
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartModule period hPeriod configuration data analysis
        chartData).toSMul inferInstance
      (RegularityChartTopologicalSpace period hPeriod configuration data analysis
        chartData) :=
  @IsBoundedSMul.continuousSMul Real
    (FullChart period hPeriod configuration data analysis chartData)
    inferInstance
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData).toPseudoMetricSpace inferInstance
    (RegularityChartAddCommGroup period hPeriod configuration data analysis
      chartData).toZero
    (RegularityChartModule period hPeriod configuration data analysis
      chartData).toSMul
    (@NormedSpace.toIsBoundedSMul Real
      (FullChart period hPeriod configuration data analysis chartData)
      inferInstance
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData).toSeminormedAddCommGroup
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData))

@[implicit_reducible]
private noncomputable def RegularityEulerTargetNormedAddCommGroup :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData →L[Real]
        Real) :=
  @ContinuousLinearMap.toNormedAddCommGroup Real Real
    (FullChart period hPeriod configuration data analysis chartData) Real
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData) inferInstance
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData) inferInstance (RingHom.id Real) inferInstance

@[implicit_reducible]
private noncomputable def RegularityEulerTargetNormedSpace :
    @NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData →L[Real]
        Real) inferInstance
      (RegularityEulerTargetNormedAddCommGroup period hPeriod configuration data
        analysis chartData).toSeminormedAddCommGroup :=
  @ContinuousLinearMap.toNormedSpace Real Real
    (FullChart period hPeriod configuration data analysis chartData) Real
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData).toSeminormedAddCommGroup inferInstance
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData) inferInstance (RingHom.id Real) inferInstance Real inferInstance
      inferInstance inferInstance

/-- The exact full-BRST action is `C²` throughout its open chart domain. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAction_contDiffOn_two :
    @ContDiffOn Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      Real inferInstance inferInstance 2
      (globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod
        configuration data analysis chartData)
      (globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis chartData) := by
  intro state hState
  exact @ContDiffAt.contDiffWithinAt Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    Real inferInstance inferInstance
    (globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
      configuration data analysis chartData)
    (globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod
      configuration data analysis chartData) state 2
    (globalCandidateAGaugeFixedNonlinearFullBRSTAction_contDiffAt_two period
      hPeriod (measure := measure) configuration data analysis chartData state
        hState)

/-- The chart Euler operator is the actual Fréchet derivative of the
full-BRST action at every admissible state. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTAction_fderiv_eq_eulerOperator
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hState : state ∈
      globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis chartData) :
    @fderiv Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartAddCommGroup period hPeriod configuration data analysis
          chartData)
        (RegularityChartModule period hPeriod configuration data analysis
          chartData)
        (RegularityChartTopologicalSpace period hPeriod configuration data
          analysis chartData)
        Real inferInstance inferInstance inferInstance
        (globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod
          configuration data analysis chartData) state =
      globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
        configuration data analysis chartData state := by
  letI : NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
    RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData
  letI : NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
    RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData
  letI : AddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
    RegularityChartAddCommGroup period hPeriod configuration data analysis
      chartData
  letI : Module Real
      (FullChart period hPeriod configuration data analysis chartData) :=
    RegularityChartModule period hPeriod configuration data analysis chartData
  letI : TopologicalSpace
      (FullChart period hPeriod configuration data analysis chartData) :=
    RegularityChartTopologicalSpace period hPeriod configuration data analysis
      chartData
  exact @HasFDerivAt.fderiv Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartModule period hPeriod configuration data analysis chartData)
    (RegularityChartTopologicalSpace period hPeriod configuration data analysis
      chartData)
    Real inferInstance inferInstance inferInstance
    (globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod
      configuration data analysis chartData)
    (globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
      configuration data analysis chartData state)
    state inferInstance
      (RegularityChartContinuousSMul period hPeriod configuration data analysis
        chartData)
      inferInstance inferInstance inferInstance
    (globalCandidateAGaugeFixedNonlinearFullBRSTAction_hasFDerivAt period hPeriod
      (measure := measure) configuration data analysis chartData state hState)

/-- The exact full-BRST Euler covector varies `C¹` on the admissible domain. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator_contDiffOn_one :
    @ContDiffOn Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (FullChart period hPeriod configuration data analysis chartData →L[Real]
        Real)
      (RegularityEulerTargetNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityEulerTargetNormedSpace period hPeriod configuration data
        analysis chartData)
      1
      (globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
        configuration data analysis chartData)
      (globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis chartData) := by
  letI : NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
    RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData
  letI : NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
    RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData
  letI : AddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
    RegularityChartAddCommGroup period hPeriod configuration data analysis
      chartData
  letI : Module Real
      (FullChart period hPeriod configuration data analysis chartData) :=
    RegularityChartModule period hPeriod configuration data analysis chartData
  letI : TopologicalSpace
      (FullChart period hPeriod configuration data analysis chartData) :=
    RegularityChartTopologicalSpace period hPeriod configuration data analysis
      chartData
  have hFDeriv : @ContDiffOn Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (FullChart period hPeriod configuration data analysis chartData →L[Real]
        Real)
      (RegularityEulerTargetNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityEulerTargetNormedSpace period hPeriod configuration data
        analysis chartData)
      1
      (@fderiv Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartAddCommGroup period hPeriod configuration data analysis
          chartData)
        (RegularityChartModule period hPeriod configuration data analysis
          chartData)
        (RegularityChartTopologicalSpace period hPeriod configuration data
          analysis chartData)
        Real inferInstance inferInstance inferInstance
        (globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod
          configuration data analysis chartData))
      (globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis chartData) :=
    @ContDiffOn.fderiv_of_isOpen Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      Real inferInstance inferInstance
      (globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis chartData)
      (globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod
        configuration data analysis chartData)
      1 2
      (globalCandidateAGaugeFixedNonlinearFullBRSTAction_contDiffOn_two period
        hPeriod (measure := measure) configuration data analysis chartData)
      (globalCandidateAGaugeFixedNonlinearFullBRSTDomain_isOpen period hPeriod
        (measure := measure) configuration data analysis chartData) (by norm_num)
  exact @ContDiffOn.congr Real
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (FullChart period hPeriod configuration data analysis chartData)
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    (FullChart period hPeriod configuration data analysis chartData →L[Real]
      Real)
    (RegularityEulerTargetNormedAddCommGroup period hPeriod configuration data
      analysis chartData)
    (RegularityEulerTargetNormedSpace period hPeriod configuration data analysis
      chartData)
    (globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
      configuration data analysis chartData)
    (@fderiv Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartAddCommGroup period hPeriod configuration data analysis
        chartData)
      (RegularityChartModule period hPeriod configuration data analysis chartData)
      (RegularityChartTopologicalSpace period hPeriod configuration data analysis
        chartData)
      Real inferInstance inferInstance inferInstance
      (globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod
        configuration data analysis chartData))
    (globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
      configuration data analysis chartData)
    1 hFDeriv
    (fun state hState =>
      (globalCandidateAGaugeFixedNonlinearFullBRSTAction_fderiv_eq_eulerOperator
        period hPeriod (measure := measure) configuration data analysis chartData
          state hState).symm)

/-- On the admissible domain, the fixed-ambient residual equation is exactly
the vanishing of the Fréchet derivative of the full-BRST action. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator_eq_zero_iff_fderiv_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hState : state ∈
      globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
        configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator
          period hPeriod configuration data analysis chartData state = 0 ↔
      @fderiv Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartAddCommGroup period hPeriod configuration data analysis
          chartData)
        (RegularityChartModule period hPeriod configuration data analysis
          chartData)
        (RegularityChartTopologicalSpace period hPeriod configuration data
          analysis chartData)
        Real inferInstance inferInstance inferInstance
        (globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod
          configuration data analysis chartData) state = 0 := by
  rw [← global_candidateA_gaugeFixed_nonlinear_full_BRST_fixed_ambient_euler_residual_operator_gate]
  unfold GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTAction_fderiv_eq_eulerOperator
    period hPeriod (measure := measure) configuration data analysis chartData
      state hState]
  rfl

/-- Gate 269: the full-BRST action is `C²`, its exact Euler operator is `C¹`,
and the fixed-ambient residual equation is its critical-point equation. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_euler_operator_regularity_gate :
    @ContDiffOn Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData)
        Real inferInstance inferInstance 2
        (globalCandidateAGaugeFixedNonlinearFullBRSTAction period hPeriod
          configuration data analysis chartData)
        (globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
          configuration data analysis chartData) ∧
      @ContDiffOn Real
        P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
        (FullChart period hPeriod configuration data analysis chartData)
        (RegularityChartNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityChartNormedSpace period hPeriod configuration data analysis
          chartData)
        (FullChart period hPeriod configuration data analysis chartData →L[Real]
          Real)
        (RegularityEulerTargetNormedAddCommGroup period hPeriod configuration data
          analysis chartData)
        (RegularityEulerTargetNormedSpace period hPeriod configuration data
          analysis chartData)
        1
        (globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator period hPeriod
          configuration data analysis chartData)
        (globalCandidateAGaugeFixedNonlinearFullBRSTDomain period hPeriod
          configuration data analysis chartData) :=
  ⟨globalCandidateAGaugeFixedNonlinearFullBRSTAction_contDiffOn_two period
      hPeriod (measure := measure) configuration data analysis chartData,
    globalCandidateAGaugeFixedNonlinearFullBRSTEulerOperator_contDiffOn_one period
      hPeriod (measure := measure) configuration data analysis chartData⟩

end Regularity
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTEulerOperatorRegularity4D
end JanusFormal
