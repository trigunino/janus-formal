import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPStateDependentAugmentedGraphRieszResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCMatterEuler4D

/-!
# Augmented graph-Riesz residual of the full-BRST SpinC equation

The authentic maximal spectral matter residual is retained as the Hilbert
coordinate and the exact physical cross-block as a scalar graph coordinate.
Their combined residual is separating without asserting that either summand
vanishes separately.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCAugmentedGraphRieszResidual4D

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
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalEulerLagrangeMatterGraphMaximalSpectralResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalEightSectorBlockSum4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSpinCMatterGraphResidualBridge4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCMatterEuler4D
open P0EFTJanusProgramPStateDependentAugmentedGraphRieszResidual4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldSpinCAugmentedResidual :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpaceSpinCAugmentedResidual :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifoldSpinCAugmentedResidual :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpaceSpinCAugmentedResidual :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpaceSpinCAugmentedResidual :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance matterHilbertRealInnerProductSpaceSpinCAugmentedResidual :
    InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  { InnerProductSpace.complexToReal with
    toNormedSpace := inferInstance }

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section SpinCAugmentedResidual

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

private abbrev SpinCTest :=
  Sector → D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter

private abbrev FullChart :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTGraphChart4D period hPeriod
    configuration data analysis chartData

private abbrev PhysicalPoint
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTPhysicalPoint period hPeriod
    configuration data analysis chartData state

/-- Primitive SpinC test mapped into the ambient coefficient Hilbert space. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCSpectralBaseMap :
    SpinCTest period hPeriod →ₗ[Real]
      ProgramPPrimitiveSpinCMatterHilbert :=
  (programPPrimitiveSpinCMatterGraphFstRealCLM period hPeriod
      couplings.matterMassSquared).toLinearMap.comp
    ((globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
        configuration data analysis chartData).matterProjection.toLinearMap.comp
      (globalCandidateAMinimalPhysicalSpinCMatterChartDirection period hPeriod
        configuration data analysis chartData))

/-- Authentic maximal spectral output of the matter block at the full-BRST
physical point. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCMaximalSpectralResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    ProgramPPrimitiveSpinCMatterHilbert :=
  programPPrimitiveSpinCMatterGraphMaximalSpectralResidual period hPeriod
    couplings.matterMassSquared
    ((globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
      configuration data analysis chartData).matterProjection
        (PhysicalPoint period hPeriod configuration data analysis chartData state))

/-- Generic augmented-graph data for the coupled SpinC equation. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCAugmentedGraphData
    (state : FullChart period hPeriod configuration data analysis chartData) :
    StateDependentAugmentedGraphRieszData
      (Test := SpinCTest period hPeriod)
      (Base := ProgramPPrimitiveSpinCMatterHilbert) where
  baseMap :=
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCSpectralBaseMap period
      hPeriod configuration data analysis chartData
  remainder :=
    globalCandidateAMinimalPhysicalSpinCCrossBlockEulerCovectorAt period hPeriod
      configuration data analysis chartData
      (PhysicalPoint period hPeriod configuration data analysis chartData state)
  baseCovector :=
    InnerProductSpace.toDual Real ProgramPPrimitiveSpinCMatterHilbert
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCMaximalSpectralResidual
        period hPeriod configuration data analysis chartData state)

abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCAugmentedGraphHilbert
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  StateDependentAugmentedGraphHilbert
    (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCAugmentedGraphData period
      hPeriod configuration data analysis chartData state)

/-- Exact Riesz representative on the SpinC spectral-plus-cross-block graph. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCAugmentedGraphRieszResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCAugmentedGraphHilbert period
      hPeriod configuration data analysis chartData state :=
  stateDependentAugmentedGraphRieszResidual
    (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCAugmentedGraphData period
      hPeriod configuration data analysis chartData state)

/-- The matter-block SpinC covector is exactly the pullback of the authentic
spectral residual. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTMatterBlockSpinCEulerCovector_eq_spectralBaseCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAMinimalPhysicalMatterBlockSpinCEulerCovectorAt period hPeriod
        configuration data analysis chartData
        (PhysicalPoint period hPeriod configuration data analysis chartData state) =
      (InnerProductSpace.toDual Real ProgramPPrimitiveSpinCMatterHilbert
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCMaximalSpectralResidual
          period hPeriod configuration data analysis chartData state)
        ).toLinearMap.comp
          (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCSpectralBaseMap period
            hPeriod configuration data analysis chartData) := by
  apply LinearMap.ext
  intro test
  unfold globalCandidateAMinimalPhysicalMatterBlockSpinCEulerCovectorAt
  simp only [LinearMap.comp_apply]
  calc
    _ = globalCandidateAMinimalPhysicalMatterBlockSpectralResidualPairing
          period hPeriod configuration data analysis chartData
          (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCMaximalSpectralResidual
            period hPeriod configuration data analysis chartData state)
          (globalCandidateAMinimalPhysicalSpinCMatterChartDirection period hPeriod
            configuration data analysis chartData test) :=
      globalCandidateAMinimalPhysicalMatterBlockEuler_eq_spectralResidualPairing
        period hPeriod configuration data analysis chartData _ _
    _ = _ := by
      unfold globalCandidateAMinimalPhysicalMatterBlockSpectralResidualPairing
        programPPrimitiveSpinCMatterGraphMaximalSpectralResidualPairing
        globalCandidateAGaugeFixedNonlinearFullBRSTSpinCMaximalSpectralResidual
        globalCandidateAGaugeFixedNonlinearFullBRSTSpinCSpectralBaseMap
      simp only [LinearMap.comp_apply]
      exact real_inner_comm _ _

/-- The generic augmented total covector is definitionally the authentic
matter block plus its named cross-block. -/
theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector_eq_augmentedTotalCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector period hPeriod
        configuration data analysis chartData state =
      stateDependentAugmentedTotalCovector
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCAugmentedGraphData
          period hPeriod configuration data analysis chartData state) := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector_eq,
    globalCandidateAGaugeFixedNonlinearFullBRSTMatterBlockSpinCEulerCovector_eq_spectralBaseCovector]
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector_eq_zero_iff_augmentedGraphResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector period hPeriod
          configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTSpinCAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector_eq_augmentedTotalCovector]
  exact stateDependentAugmentedTotalCovector_eq_zero_iff_graphResidual _

theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_spinCAugmentedGraphResidual_eq_zero
    (state : FullChart period hPeriod configuration data analysis chartData)
    (hCritical : GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period
      hPeriod configuration data analysis chartData state) :
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 := by
  apply
    (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector_eq_zero_iff_augmentedGraphResidual
      period hPeriod configuration data analysis chartData state).mp
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector_eq]
  exact globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_imp_spinCEuler_eq_zero
    period hPeriod configuration data analysis chartData state hCritical

/-- Gate 253: the complete SpinC equation has an exact separating residual
that retains both the spectral block and its physical cross-block. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_spinC_augmented_graph_riesz_residual_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector period hPeriod
          configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTSpinCAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 :=
  globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector_eq_zero_iff_augmentedGraphResidual
    period hPeriod configuration data analysis chartData state

end SpinCAugmentedResidual

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCAugmentedGraphRieszResidual4D
end JanusFormal
