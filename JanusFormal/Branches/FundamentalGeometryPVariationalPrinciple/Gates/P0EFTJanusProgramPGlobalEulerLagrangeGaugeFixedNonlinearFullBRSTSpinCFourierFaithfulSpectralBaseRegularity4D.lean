import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulRemainderRegularityData4D

/-!
# Canonical fixed-carrier regularity of the SpinC spectral base

The spectral base residual is a composition of existing continuous linear maps.
Restricting its covector to the fixed SpinC carrier and applying Riesz therefore
gives a canonical globally smooth representative without extra assumptions.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulSpectralBaseRegularity4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory Topology
open scoped Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearDiffeomorphismBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedCarrier4D

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

local instance matterHilbertRealInnerProductSpaceSpinCSpectralBase :
    InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  { InnerProductSpace.complexToReal with
    toNormedSpace := inferInstance }

section SpectralBase

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
    (measure := measure) configuration data analysis chartData

private abbrev SpinCHilbert :=
  GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedHilbert
    period hPeriod configuration data analysis chartData

private abbrev SpinCClosure :=
  globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedClosure
    period hPeriod configuration data analysis chartData

private abbrev RegularityChartNormedAddCommGroup :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartNormedAddCommGroup period hPeriod configuration data
    analysis chartData

private abbrev RegularityChartNormedSpace :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  nonlinearFullBRSTChartNormedSpace period hPeriod configuration data analysis
    chartData

@[implicit_reducible]
local instance (priority := 12000) regularityChartNormedAddCommGroup :
    NormedAddCommGroup
      (FullChart period hPeriod configuration data analysis chartData) :=
  RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
    chartData

@[implicit_reducible]
local instance (priority := 12000) regularityChartNormedSpace :
    NormedSpace Real
      (FullChart period hPeriod configuration data analysis chartData) :=
  RegularityChartNormedSpace period hPeriod configuration data analysis
    chartData

local instance spinCHilbertCompleteSpace :
    CompleteSpace
      (SpinCHilbert period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedCompleteSpace
    period hPeriod configuration data analysis chartData

/-- The full-chart-to-spectral-residual map as one continuous linear map. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCSpectralResidualCLM :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      ProgramPPrimitiveSpinCMatterHilbert :=
  (programPPrimitiveSpinCMatterGraphOperatorRealCLM period hPeriod
      couplings.matterMassSquared).comp
    ((globalCandidateAMinimalPhysicalQuadraticChartBridge period hPeriod
        configuration data analysis chartData).matterProjection.comp
      ((globalCandidateAGaugeFixedNonlinearDiffeomorphismBRSTPhysicalProjection
          period hPeriod configuration data analysis chartData).comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismProjection
          period hPeriod configuration data analysis chartData)))

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCSpectralResidualCLM_apply
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCSpectralResidualCLM period
        hPeriod configuration data analysis chartData state =
      globalCandidateAGaugeFixedNonlinearFullBRSTSpinCMaximalSpectralResidual
        period hPeriod configuration data analysis chartData state := by
  rfl

/-- First Fourier component restricted from the ambient pair to the carrier. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedFstCLM :
    SpinCHilbert period hPeriod configuration data analysis chartData →L[Real]
      ProgramPPrimitiveSpinCMatterHilbert :=
  (WithLp.fstL 2 Real ProgramPPrimitiveSpinCMatterHilbert
      ProgramPPrimitiveSpinCMatterHilbert).comp
    (SpinCClosure period hPeriod configuration data analysis chartData).subtypeL

/-- Canonical spectral base covector restricted to the fixed carrier. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseCarrierCovectorCLM :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      (SpinCHilbert period hPeriod configuration data analysis chartData →L[Real]
        Real) :=
  ((globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedFstCLM
      period hPeriod configuration data analysis chartData).precomp Real).comp
    ((InnerProductSpace.toDual Real ProgramPPrimitiveSpinCMatterHilbert
      ).toContinuousLinearEquiv.toContinuousLinearMap.comp
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCSpectralResidualCLM
          period hPeriod configuration data analysis chartData))

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseCarrierCovectorCLM_apply
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseCarrierCovectorCLM
        period hPeriod configuration data analysis chartData state =
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphData
        period hPeriod configuration data analysis chartData state).baseCovector.comp
        (SpinCClosure period hPeriod configuration data analysis chartData
          ).subtypeL := by
  apply ContinuousLinearMap.ext
  intro value
  rfl

/-- Canonical Riesz representative of the spectral base covector on the fixed
carrier. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseRieszCLM :
    FullChart period hPeriod configuration data analysis chartData →L[Real]
      SpinCHilbert period hPeriod configuration data analysis chartData :=
  (InnerProductSpace.toDual Real
      (SpinCHilbert period hPeriod configuration data analysis chartData)
    ).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseCarrierCovectorCLM
        period hPeriod configuration data analysis chartData)

def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseRieszRepresentative
    (state : FullChart period hPeriod configuration data analysis chartData) :
    SpinCHilbert period hPeriod configuration data analysis chartData :=
  globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseRieszCLM
    period hPeriod configuration data analysis chartData state

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseRieszRepresentative_pairing
    (state : FullChart period hPeriod configuration data analysis chartData)
    (test : SpinCHilbert period hPeriod configuration data analysis chartData) :
    inner Real
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseRieszRepresentative
          period hPeriod configuration data analysis chartData state) test =
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphData
        period hPeriod configuration data analysis chartData state).baseCovector
        ((SpinCClosure period hPeriod configuration data analysis chartData
          ).subtypeL test) := by
  change inner Real
      ((InnerProductSpace.toDual Real
        (SpinCHilbert period hPeriod configuration data analysis chartData)
        ).symm
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseCarrierCovectorCLM
          period hPeriod configuration data analysis chartData state)) test = _
  rw [InnerProductSpace.toDual_symm_apply]
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseCarrierCovectorCLM_apply]
  rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseRieszRepresentative_contDiff :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (SpinCHilbert period hPeriod configuration data analysis chartData)
      inferInstance inferInstance ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseRieszRepresentative
        period hPeriod configuration data analysis chartData) := by
  exact @ContinuousLinearMap.contDiff Real
    (FullChart period hPeriod configuration data analysis chartData)
    (SpinCHilbert period hPeriod configuration data analysis chartData)
    P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
    (RegularityChartNormedAddCommGroup period hPeriod configuration data analysis
      chartData)
    (RegularityChartNormedSpace period hPeriod configuration data analysis
      chartData)
    inferInstance inferInstance ∞
    (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseRieszCLM
      period hPeriod configuration data analysis chartData)

/-- Gate 294: the spectral base has a canonical globally smooth fixed-carrier
Riesz representative. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_spinC_fourier_faithful_spectral_base_regularity_gate :
    @ContDiff Real
      P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D.alignedRealNontriviallyNormedFieldCalculus
      (FullChart period hPeriod configuration data analysis chartData)
      (RegularityChartNormedAddCommGroup period hPeriod configuration data
        analysis chartData)
      (RegularityChartNormedSpace period hPeriod configuration data analysis
        chartData)
      (SpinCHilbert period hPeriod configuration data analysis chartData)
      inferInstance inferInstance ∞
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseRieszRepresentative
        period hPeriod configuration data analysis chartData) :=
  globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulFixedBaseRieszRepresentative_contDiff
    period hPeriod configuration data analysis chartData

end SpectralBase
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulSpectralBaseRegularity4D
end JanusFormal
