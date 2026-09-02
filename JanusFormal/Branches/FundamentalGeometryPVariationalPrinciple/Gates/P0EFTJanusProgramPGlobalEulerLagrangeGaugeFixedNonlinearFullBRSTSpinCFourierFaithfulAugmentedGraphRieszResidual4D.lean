import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialGraphFaithfulness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalFourierGraph4D

/-!
# Fourier-faithful augmented graph residual of the full-BRST SpinC equation

The authentic maximal spectral coordinate is retained and paired with the
injective canonical two-sector Fourier coordinate.  The physical cross-block
remains the scalar graph coordinate.  No local Dirac PDE is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphRieszResidual4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 1200000
noncomputable section

open Set MeasureTheory Topology
open scoped ENNReal Manifold ContDiff InnerProductSpace Topology
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPD9PrimitiveSpinCSmoothSectionCore4D
open P0EFTJanusProgramPD9PrimitiveSpinCGlobalComplexScalarAction4D
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
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalComponentPDEBlockPairing4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSpinCMatterGraphResidualBridge4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTGraphChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTCoreEulerSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPairedAbelianPotentialEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCMatterEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalDiffeomorphismGhostEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianNonminimalStrongSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalStrongSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTPhysicalGhostL2AugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTRemainingPhysicalScalarGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTMetricAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNormalL2RobinAugmentedGraphRieszResidual4D
open P0EFTJanusProgramPPrimitiveSpinCMatterCanonicalFourierGraph4D
open P0EFTJanusProgramPStateDependentAugmentedGraphRieszResidual4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldSpinCFourierResidual :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev SpinCTest :=
  Sector → D9PrimitiveSpinCSmoothSection period hPeriod .positiveQuarter

private abbrev SpinCFourierFaithfulBase :=
  WithLp 2
    (ProgramPPrimitiveSpinCMatterHilbert ×
      ProgramPPrimitiveSpinCMatterHilbert)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance matterHilbertRealInnerProductSpaceSpinCFourierResidual :
    InnerProductSpace Real ProgramPPrimitiveSpinCMatterHilbert :=
  { InnerProductSpace.complexToReal with
    toNormedSpace := inferInstance }

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

section SpinCFourierResidual

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

/-- Canonical two-sector Fourier coefficients, viewed as a real linear map. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCCanonicalFourierRealMap :
    SpinCTest period hPeriod →ₗ[Real]
      ProgramPPrimitiveSpinCMatterHilbert where
  toFun := programPPrimitiveSpinCMatterCanonicalFourierCoefficients period
    hPeriod
  map_add' first second := map_add
    (programPPrimitiveSpinCMatterCanonicalFourierCoefficients period hPeriod)
    first second
  map_smul' scalar field := by
    have hSource : scalar • field = (scalar : Complex) • field := by
      funext sector
      change scalar • field sector =
        d9PrimitiveSpinCComplexScalarSection period hPeriod .positiveQuarter
          (scalar : Complex) (field sector)
      exact
        (d9PrimitiveSpinCComplexScalarSection_ofReal period hPeriod
          .positiveQuarter scalar (field sector)).symm
    have hTarget (coefficients : ProgramPPrimitiveSpinCMatterHilbert) :
        (scalar : Complex) • coefficients = scalar • coefficients := by
      apply Subtype.ext
      rfl
    rw [hSource, map_smul, hTarget]
    rfl

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCCanonicalFourierRealMap_injective :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCCanonicalFourierRealMap
        period hPeriod) := by
  intro first second hEqual
  exact
    programPPrimitiveSpinCMatterCanonicalFourierCoefficients_injective period
      hPeriod hEqual

/-- The authentic spectral coordinate paired with a faithful Fourier
coordinate on the same smooth SpinC test. -/
def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulBaseMap :
    SpinCTest period hPeriod →ₗ[Real]
      SpinCFourierFaithfulBase where
  toFun test := WithLp.toLp 2
    (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCSpectralBaseMap period
        hPeriod configuration data analysis chartData test,
      globalCandidateAGaugeFixedNonlinearFullBRSTSpinCCanonicalFourierRealMap
        period hPeriod test)
  map_add' first second := by
    apply WithLp.ofLp_injective 2
    simp
  map_smul' scalar test := by
    apply WithLp.ofLp_injective 2
    simp

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulBaseMap_injective :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulBaseMap
        period hPeriod configuration data analysis chartData) := by
  intro first second hEqual
  apply
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCCanonicalFourierRealMap_injective
      period hPeriod
  simpa [globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulBaseMap]
    using congrArg WithLp.snd hEqual

def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphData
    (state : FullChart period hPeriod configuration data analysis chartData) :
    StateDependentAugmentedGraphRieszData
      (Test := SpinCTest period hPeriod)
      (Base := SpinCFourierFaithfulBase) where
  baseMap :=
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulBaseMap
      period hPeriod configuration data analysis chartData
  remainder :=
    globalCandidateAMinimalPhysicalSpinCCrossBlockEulerCovectorAt period hPeriod
      configuration data analysis chartData
      (PhysicalPoint period hPeriod configuration data analysis chartData state)
  baseCovector :=
    (InnerProductSpace.toDual Real ProgramPPrimitiveSpinCMatterHilbert
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCMaximalSpectralResidual
        period hPeriod configuration data analysis chartData state)).comp
      (WithLp.fstL 2 Real ProgramPPrimitiveSpinCMatterHilbert
        ProgramPPrimitiveSpinCMatterHilbert)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphLinearMap_injective
    (state : FullChart period hPeriod configuration data analysis chartData) :
    Function.Injective
      (stateDependentAugmentedGraphLinearMap
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphData
          period hPeriod configuration data analysis chartData state)) := by
  intro first second hEqual
  apply
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulBaseMap_injective
      period hPeriod configuration data analysis chartData
  simpa [stateDependentAugmentedGraphLinearMap,
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphData]
    using congrArg WithLp.fst hEqual

abbrev GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphHilbert
    (state : FullChart period hPeriod configuration data analysis chartData) :=
  StateDependentAugmentedGraphHilbert
    (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphData
      period hPeriod configuration data analysis chartData state)

def globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphRieszResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphHilbert
      period hPeriod configuration data analysis chartData state :=
  stateDependentAugmentedGraphRieszResidual
    (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphData
      period hPeriod configuration data analysis chartData state)

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector_eq_fourierFaithfulAugmentedTotalCovector
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector period hPeriod
        configuration data analysis chartData state =
      stateDependentAugmentedTotalCovector
        (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphData
          period hPeriod configuration data analysis chartData state) := by
  rw [globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector_eq,
    globalCandidateAGaugeFixedNonlinearFullBRSTMatterBlockSpinCEulerCovector_eq_spectralBaseCovector]
  apply LinearMap.ext
  intro test
  simp [stateDependentAugmentedTotalCovector,
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphData,
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulBaseMap]

theorem globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector_eq_zero_iff_fourierFaithfulAugmentedGraphResidual
    (state : FullChart period hPeriod configuration data analysis chartData) :
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector period hPeriod
          configuration data analysis chartData state = 0 ↔
      globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphRieszResidual
        period hPeriod configuration data analysis chartData state = 0 := by
  rw [
    globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector_eq_fourierFaithfulAugmentedTotalCovector]
  exact stateDependentAugmentedTotalCovector_eq_zero_iff_graphResidual _

def GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricNormalPhysicalGhostL2SpinCFourierFaithfulAugmentedGraphResidualEulerSystemAt
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
              globalCandidateAGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphRieszResidual
                  period hPeriod configuration data analysis chartData state = 0 ∧
                GlobalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalStrongSystemAt
                    period hPeriod configuration data analysis chartData state ∧
                  globalCandidateAGaugeFixedNonlinearFullBRSTPotentialGraphRieszResidual
                      period hPeriod configuration data analysis chartData state = 0 ∧
                    GlobalCandidateAGaugeFixedNonlinearFullBRSTAbelianNonminimalStrongSystemAt
                      period hPeriod configuration data analysis chartData state

theorem globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_metricNormalPhysicalGhostL2SpinCFourierFaithfulAugmentedGraphResidualEulerSystem
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricNormalPhysicalGhostL2SpinCFourierFaithfulAugmentedGraphResidualEulerSystemAt
        period hPeriod configuration data analysis chartData state := by
  constructor
  · intro hCritical
    rcases
        (globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_metricNormalPhysicalGhostL2AugmentedGraphResidualEulerSystem
          period hPeriod configuration data analysis chartData state).mp hCritical with
      ⟨hMetric, hNormal, hPhysicalGhost, hLLAux, hLLMeasure, hLLField,
        hSpinC, hDiffeomorphism, hPotential, hAbelian⟩
    have hSpinCEuler :=
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector_eq_zero_iff_augmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mpr hSpinC
    exact ⟨
      hMetric, hNormal, hPhysicalGhost, hLLAux, hLLMeasure, hLLField,
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector_eq_zero_iff_fourierFaithfulAugmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mp
          hSpinCEuler,
      hDiffeomorphism, hPotential, hAbelian⟩
  · rintro ⟨hMetric, hNormal, hPhysicalGhost, hLLAux, hLLMeasure, hLLField,
      hSpinC, hDiffeomorphism, hPotential, hAbelian⟩
    have hSpinCEuler :=
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector_eq_zero_iff_fourierFaithfulAugmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mpr hSpinC
    apply
      (globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_metricNormalPhysicalGhostL2AugmentedGraphResidualEulerSystem
        period hPeriod configuration data analysis chartData state).mpr
    exact ⟨
      hMetric, hNormal, hPhysicalGhost, hLLAux, hLLMeasure, hLLField,
      (globalCandidateAGaugeFixedNonlinearFullBRSTSpinCEulerCovector_eq_zero_iff_augmentedGraphResidual
        period hPeriod configuration data analysis chartData state).mp
          hSpinCEuler,
      hDiffeomorphism, hPotential, hAbelian⟩

/-- Gate 263: the exact ten-block system retains both the authentic SpinC
spectral coordinate and an injective canonical Fourier coordinate. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_spinC_fourier_faithful_augmented_graph_riesz_residual_gate
    (state : FullChart period hPeriod configuration data analysis chartData) :
    GlobalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt period hPeriod
        configuration data analysis chartData state ↔
      GlobalCandidateAGaugeFixedNonlinearFullBRSTMetricNormalPhysicalGhostL2SpinCFourierFaithfulAugmentedGraphResidualEulerSystemAt
        period hPeriod configuration data analysis chartData state :=
  globalCandidateAGaugeFixedNonlinearFullBRSTIsCriticalAt_iff_metricNormalPhysicalGhostL2SpinCFourierFaithfulAugmentedGraphResidualEulerSystem
    period hPeriod configuration data analysis chartData state

end SpinCFourierResidual
end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTSpinCFourierFaithfulAugmentedGraphRieszResidual4D
end JanusFormal
