import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongErasedSectorEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator4D

/-! # T03 full-BRST scope decision

The normal and physical diffeomorphism-ghost coordinates of the minimal
projection are recorded as erased coordinates, not as derived dynamics.  The
dynamic closure used by T03 is instead the full-BRST chart, whose fixed
fourteen-component residual contains both nonminimal triplets.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPT03FullBRSTNonminimalScopeDecision4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set MeasureTheory
open scoped Manifold ContDiff ENNReal
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalConfigurationAt4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionDatum4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNonminimalStrongSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalStrongSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongErasedSectorEuler4D

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

private abbrev FullChart :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
    configuration data analysis chartData

/-- Exact statement that the two minimal coordinates are projection
artifacts: every corresponding affine line has constant physical target. -/
def ProgramPT03MinimalNormalGhostProjectionArtifactAt
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase) : Prop :=
  ∀ (test : RegularGeneralMetricC2PairedMinimalPhysicalStrongErasedTest
        period hPeriod) (t : Real),
    regularGeneralMetricC2PairedMinimalPhysicalTarget period hPeriod
        configuration.physical plusBase minusBase
        (point + t •
          regularGeneralMetricC2PairedMinimalPhysicalStrongErasedDirection
            period hPeriod configuration.physical test)
        (regularGeneralMetricC2PairedMinimalPhysicalStrongErasedLine_mem period
          hPeriod configuration.physical plusBase minusBase point hPoint test t) =
      regularGeneralMetricC2PairedMinimalPhysicalTarget period hPeriod
        configuration.physical plusBase minusBase point hPoint

/-- The full-BRST residual, rather than the erased minimal coordinates,
supplies the two genuine nonminimal dynamic triplets. -/
def ProgramPT03FullBRSTNonminimalDynamicScopeAt
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Prop :=
  (GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator
        period hPeriod configuration data analysis chartData state = 0) ∧
    (globalCandidateAGaugeFixedNonlinearFullBRSTFixedAmbientEulerResidualOperator
          period hPeriod configuration data analysis chartData state = 0 →
      GlobalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalStrongSystemAt
          period hPeriod configuration data analysis chartData state ∧
        GlobalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalStrongSystemAt
          period hPeriod configuration data analysis chartData state)

/-- Gate: the minimal normal/ghost equations are explicitly classified as
projection degeneracies, while full-BRST criticality supplies both nonminimal
strong systems through one fixed residual operator. -/
theorem program_p_t03_full_BRST_nonminimal_scope_decision_gate
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (point : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period hPeriod
        configuration.physical plusBase minusBase)
    (state : FullChart period hPeriod configuration data analysis chartData) :
    ProgramPT03MinimalNormalGhostProjectionArtifactAt period hPeriod
        configuration plusBase minusBase point hPoint ∧
      ProgramPT03FullBRSTNonminimalDynamicScopeAt period hPeriod configuration
        data analysis chartData state := by
  constructor
  · intro test t
    exact regularGeneralMetricC2PairedMinimalPhysicalStrongErasedTarget_line
      period hPeriod configuration.physical plusBase minusBase point hPoint test t
  · constructor
    · exact
        global_candidateA_gaugeFixed_nonlinear_full_BRST_fixed_ambient_euler_residual_operator_gate
          period hPeriod configuration data analysis chartData state
    · intro hResidual
      have hCritical :
          GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
            configuration data analysis chartData state :=
        (global_candidateA_gaugeFixed_nonlinear_full_BRST_fixed_ambient_euler_residual_operator_gate
          period hPeriod configuration data analysis chartData state).mpr hResidual
      exact ⟨
        globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_diffeomorphismNonminimalStrongSystem
          period hPeriod configuration data analysis chartData state hCritical,
        globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_abelianNonminimalStrongSystem
          period hPeriod configuration data analysis chartData state hCritical⟩

end
end
end P0EFTJanusProgramPT03FullBRSTNonminimalScopeDecision4D
end JanusFormal
