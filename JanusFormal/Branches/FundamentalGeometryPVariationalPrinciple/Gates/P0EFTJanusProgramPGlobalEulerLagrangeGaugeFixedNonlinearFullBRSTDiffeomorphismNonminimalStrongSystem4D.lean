import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphRieszResidual4D

/-!
# Strong diffeomorphism nonminimal system

The three fieldwise diffeomorphism nonminimal covectors are replaced exactly
by their separating graph-Riesz residuals. No PDE or `L²` identification is
asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalStrongSystem4D

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
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalComponentEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldDiffeomorphismNonminimalStrongSystem :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpaceDiffeomorphismNonminimalStrongSystem :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldDiffeomorphismNonminimalStrongSystem :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceDiffeomorphismNonminimalStrongSystem :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceDiffeomorphismNonminimalStrongSystem :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section StrongSystem

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

/-- Exact graph-Riesz system for the three diffeomorphism nonminimal fields. -/
def GlobalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalStrongSystemAt
    (state : FullChart period hPeriod configuration data analysis chartData) : Prop :=
  globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 ∧
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphRieszResidual
          period hPeriod configuration data analysis chartData state = 0 ∧
      globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0

/-- The aggregated weak covector vanishes exactly when the three graph-Riesz
residuals vanish. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector_eq_zero_iff_strongSystem
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector
          period hPeriod configuration data analysis chartData state = 0 ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalStrongSystemAt
        period hPeriod configuration data analysis chartData state := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector_eq_zero_iff_components]
  unfold GlobalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalStrongSystemAt
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismGhostBRSTCovector_eq_zero_iff_graphResidual,
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostBRSTCovector_eq_zero_iff_graphResidual,
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupBRSTCovector_eq_zero_iff_graphResidual]

/-- Full-BRST criticality forces the complete strong diffeomorphism
nonminimal system. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_diffeomorphismNonminimalStrongSystem
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hCritical : GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period
      hPeriod configuration data analysis chartData state) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalStrongSystemAt
      period hPeriod configuration data analysis chartData state := by
  exact ⟨
    globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_diffeomorphismGhostGraphResidual_eq_zero
      period hPeriod configuration data analysis chartData state hCritical,
    globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_diffeomorphismAntighostGraphResidual_eq_zero
      period hPeriod configuration data analysis chartData state hCritical,
    globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_diffeomorphismNakanishiLautrupGraphResidual_eq_zero
      period hPeriod configuration data analysis chartData state hCritical⟩

/-- Gate 249: all three diffeomorphism nonminimal weak equations are exactly
replaced by their separating graph-Riesz residual system. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_diffeomorphism_nonminimal_strong_system_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector
          period hPeriod configuration data analysis chartData state = 0 ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalStrongSystemAt
        period hPeriod configuration data analysis chartData state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalBRSTCovector_eq_zero_iff_strongSystem
    period hPeriod configuration data analysis chartData state

end StrongSystem

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalStrongSystem4D
end JanusFormal
