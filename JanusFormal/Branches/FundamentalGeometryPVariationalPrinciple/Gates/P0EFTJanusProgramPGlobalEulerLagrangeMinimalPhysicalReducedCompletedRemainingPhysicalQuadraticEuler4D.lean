import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticEuler4D

/-!
# Remaining reduced physical Hessian quadratic Euler operator

The supplied interaction, Einstein--Hilbert plus/minus, and finite-BV H11
extensions descend to the minimal physical reduced Hilbert completion.  Their
sum defines a smooth base-point quadratic energy, its exact Frechet gradient,
and its strong Riesz representative.  Adding this energy to the graph, genuine
Robin, and Maxwell-quadratic action of the preceding gate gives the strongest
currently available reduced action and Euler operator.

This is explicitly a Hessian-quadratic completion.  It does not construct the
missing nonlinear interaction, Einstein--Hilbert, Maxwell, or finite-BV
actions on the Hilbert completion.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticEuler4D

set_option autoImplicit false
set_option maxHeartbeats 4200000
set_option synthInstance.maxHeartbeats 2100000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockExtensions4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAH10RobinProjectionCore4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedHilbert4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCoreToChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedMatterLLAction4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedGaugeAction4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedRobinAction4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedMaxwellQuadraticAction4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedSevenPhysicalQuadraticAction4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticEuler4D

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

private abbrev MinimalChart :=
  globalCandidateAMinimalPhysicalLocalVariationalChart period hPeriod
    configuration data analysis chartData

private abbrev SameAction :=
  globalCandidateAMinimalPhysicalMatterLLSameActionBridge period hPeriod
    configuration data analysis chartData

variable
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (projection : GlobalCandidateAH10RobinProjectionCoreData4D period hPeriod
      configuration data analysis
      (MinimalChart period hPeriod configuration data analysis chartData)
      (SameAction period hPeriod configuration data analysis chartData)
      einsteinScale)
    (blocks : GlobalCandidateASevenPhysicalBlockExtensions4D period hPeriod
      configuration data analysis
      (MinimalChart period hPeriod configuration data analysis chartData)
      (SameAction period hPeriod configuration data analysis chartData))

private abbrev Core :=
  GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod analysis

private abbrev Reduced :=
  GlobalCandidateAMinimalPhysicalReducedHilbert period hPeriod configuration
    data analysis

private theorem interaction_core_left_zero
    (first second : Core period hPeriod configuration analysis)
    (hFirst : first ∈
      globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
        configuration data analysis) :
    diagonalExtendedBulkH11InteractionHessianOnCore period hPeriod
        configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData)
        first second = 0 := by
  have hTangent := LinearMap.mem_ker.mp hFirst
  unfold diagonalExtendedBulkH11InteractionHessianOnCore
  change
    globalCandidateAH11LocalInteractionHessian period hPeriod
      (MinimalChart period hPeriod configuration data analysis chartData)
      (SameAction period hPeriod configuration data analysis
        chartData).chartBridge.basePoint
      ((SameAction period hPeriod configuration data analysis
        chartData).chartBridge.tangentAnalysis
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis first))
      ((SameAction period hPeriod configuration data analysis
        chartData).chartBridge.tangentAnalysis
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis second)) = 0
  simp [hTangent]

private theorem einsteinHilbertPlus_core_left_zero
    (first second : Core period hPeriod configuration analysis)
    (hFirst : first ∈
      globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
        configuration data analysis) :
    diagonalExtendedBulkH11EinsteinHilbertPlusHessianOnCore period hPeriod
        configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData)
        first second = 0 := by
  have hTangent := LinearMap.mem_ker.mp hFirst
  unfold diagonalExtendedBulkH11EinsteinHilbertPlusHessianOnCore
  change
    globalCandidateAH11LocalEinsteinHilbertPlusHessian period hPeriod
      (MinimalChart period hPeriod configuration data analysis chartData)
      (SameAction period hPeriod configuration data analysis
        chartData).chartBridge.basePoint
      ((SameAction period hPeriod configuration data analysis
        chartData).chartBridge.tangentAnalysis
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis first))
      ((SameAction period hPeriod configuration data analysis
        chartData).chartBridge.tangentAnalysis
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis second)) = 0
  simp [hTangent]

private theorem einsteinHilbertMinus_core_left_zero
    (first second : Core period hPeriod configuration analysis)
    (hFirst : first ∈
      globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
        configuration data analysis) :
    diagonalExtendedBulkH11EinsteinHilbertMinusHessianOnCore period hPeriod
        configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData)
        first second = 0 := by
  have hTangent := LinearMap.mem_ker.mp hFirst
  unfold diagonalExtendedBulkH11EinsteinHilbertMinusHessianOnCore
  change
    globalCandidateAH11LocalEinsteinHilbertMinusHessian period hPeriod
      (MinimalChart period hPeriod configuration data analysis chartData)
      (SameAction period hPeriod configuration data analysis
        chartData).chartBridge.basePoint
      ((SameAction period hPeriod configuration data analysis
        chartData).chartBridge.tangentAnalysis
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis first))
      ((SameAction period hPeriod configuration data analysis
        chartData).chartBridge.tangentAnalysis
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis second)) = 0
  simp [hTangent]

private theorem finiteBV_core_left_zero
    (first second : Core period hPeriod configuration analysis)
    (hFirst : first ∈
      globalCandidateAMinimalPhysicalSmoothCoreKernel period hPeriod
        configuration data analysis) :
    diagonalExtendedBulkH11FiniteBVHessianOnCore period hPeriod
        configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData)
        first second = 0 := by
  have hTangent := LinearMap.mem_ker.mp hFirst
  unfold diagonalExtendedBulkH11FiniteBVHessianOnCore
  change
    globalCandidateAH11LocalFiniteBVHessian period hPeriod
      (MinimalChart period hPeriod configuration data analysis chartData)
      (SameAction period hPeriod configuration data analysis
        chartData).chartBridge.basePoint
      ((SameAction period hPeriod configuration data analysis
        chartData).chartBridge.tangentAnalysis
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis first))
      ((SameAction period hPeriod configuration data analysis
        chartData).chartBridge.tangentAnalysis
          (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
            configuration data analysis second)) = 0
  simp [hTangent]

/-- Reduced interaction Hessian supplied by the interaction H11 block. -/
def globalCandidateAMinimalPhysicalReducedCompletedInteractionHessian :
    Reduced period hPeriod configuration data analysis →L[Real]
      Reduced period hPeriod configuration data analysis →L[Real] Real :=
  reducedBlockForm period hPeriod configuration data analysis blocks.interaction

/-- Reduced positive-sector Einstein--Hilbert Hessian supplied by H11. -/
def globalCandidateAMinimalPhysicalReducedCompletedEinsteinHilbertPlusHessian :
    Reduced period hPeriod configuration data analysis →L[Real]
      Reduced period hPeriod configuration data analysis →L[Real] Real :=
  reducedBlockForm period hPeriod configuration data analysis
    blocks.einsteinHilbertPlus

/-- Reduced negative-sector Einstein--Hilbert Hessian supplied by H11. -/
def globalCandidateAMinimalPhysicalReducedCompletedEinsteinHilbertMinusHessian :
    Reduced period hPeriod configuration data analysis →L[Real]
      Reduced period hPeriod configuration data analysis →L[Real] Real :=
  reducedBlockForm period hPeriod configuration data analysis
    blocks.einsteinHilbertMinus

/-- Reduced finite-BV Hessian supplied by the finite-BV H11 block. -/
def globalCandidateAMinimalPhysicalReducedCompletedFiniteBVHessian :
    Reduced period hPeriod configuration data analysis →L[Real]
      Reduced period hPeriod configuration data analysis →L[Real] Real :=
  reducedBlockForm period hPeriod configuration data analysis blocks.finiteBV

theorem globalCandidateAMinimalPhysicalReducedCompletedInteractionHessian_symmetric
    (first second : Reduced period hPeriod configuration data analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedInteractionHessian period
        hPeriod configuration data analysis chartData blocks first second =
      globalCandidateAMinimalPhysicalReducedCompletedInteractionHessian period
        hPeriod configuration data analysis chartData blocks second first :=
  blocks.interaction.symmetric _ _

theorem globalCandidateAMinimalPhysicalReducedCompletedEinsteinHilbertPlusHessian_symmetric
    (first second : Reduced period hPeriod configuration data analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedEinsteinHilbertPlusHessian
        period hPeriod configuration data analysis chartData blocks first second =
      globalCandidateAMinimalPhysicalReducedCompletedEinsteinHilbertPlusHessian
        period hPeriod configuration data analysis chartData blocks second first :=
  blocks.einsteinHilbertPlus.symmetric _ _

theorem globalCandidateAMinimalPhysicalReducedCompletedEinsteinHilbertMinusHessian_symmetric
    (first second : Reduced period hPeriod configuration data analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedEinsteinHilbertMinusHessian
        period hPeriod configuration data analysis chartData blocks first second =
      globalCandidateAMinimalPhysicalReducedCompletedEinsteinHilbertMinusHessian
        period hPeriod configuration data analysis chartData blocks second first :=
  blocks.einsteinHilbertMinus.symmetric _ _

theorem globalCandidateAMinimalPhysicalReducedCompletedFiniteBVHessian_symmetric
    (first second : Reduced period hPeriod configuration data analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedFiniteBVHessian period
        hPeriod configuration data analysis chartData blocks first second =
      globalCandidateAMinimalPhysicalReducedCompletedFiniteBVHessian period
        hPeriod configuration data analysis chartData blocks second first :=
  blocks.finiteBV.symmetric _ _

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedInteractionHessian_core
    (first second : Core period hPeriod configuration analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedInteractionHessian period
        hPeriod configuration data analysis chartData blocks
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk first))
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk second)) =
      diagonalExtendedBulkH11InteractionHessianOnCore period hPeriod
        configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData)
        first second := by
  exact reducedBlockForm_core period hPeriod configuration data analysis
    (diagonalExtendedBulkH11InteractionHessianOnCore period hPeriod
      configuration data analysis
      (MinimalChart period hPeriod configuration data analysis chartData)
      (SameAction period hPeriod configuration data analysis chartData))
    blocks.interaction
    (interaction_core_left_zero period hPeriod configuration data analysis
      chartData) first second

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedEinsteinHilbertPlusHessian_core
    (first second : Core period hPeriod configuration analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedEinsteinHilbertPlusHessian
        period hPeriod configuration data analysis chartData blocks
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk first))
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk second)) =
      diagonalExtendedBulkH11EinsteinHilbertPlusHessianOnCore period hPeriod
        configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData)
        first second := by
  exact reducedBlockForm_core period hPeriod configuration data analysis
    (diagonalExtendedBulkH11EinsteinHilbertPlusHessianOnCore period hPeriod
      configuration data analysis
      (MinimalChart period hPeriod configuration data analysis chartData)
      (SameAction period hPeriod configuration data analysis chartData))
    blocks.einsteinHilbertPlus
    (einsteinHilbertPlus_core_left_zero period hPeriod configuration data
      analysis chartData) first second

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedEinsteinHilbertMinusHessian_core
    (first second : Core period hPeriod configuration analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedEinsteinHilbertMinusHessian
        period hPeriod configuration data analysis chartData blocks
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk first))
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk second)) =
      diagonalExtendedBulkH11EinsteinHilbertMinusHessianOnCore period hPeriod
        configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData)
        first second := by
  exact reducedBlockForm_core period hPeriod configuration data analysis
    (diagonalExtendedBulkH11EinsteinHilbertMinusHessianOnCore period hPeriod
      configuration data analysis
      (MinimalChart period hPeriod configuration data analysis chartData)
      (SameAction period hPeriod configuration data analysis chartData))
    blocks.einsteinHilbertMinus
    (einsteinHilbertMinus_core_left_zero period hPeriod configuration data
      analysis chartData) first second

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedFiniteBVHessian_core
    (first second : Core period hPeriod configuration analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedFiniteBVHessian period
        hPeriod configuration data analysis chartData blocks
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk first))
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk second)) =
      diagonalExtendedBulkH11FiniteBVHessianOnCore period hPeriod
        configuration data analysis
        (MinimalChart period hPeriod configuration data analysis chartData)
        (SameAction period hPeriod configuration data analysis chartData)
        first second := by
  exact reducedBlockForm_core period hPeriod configuration data analysis
    (diagonalExtendedBulkH11FiniteBVHessianOnCore period hPeriod
      configuration data analysis
      (MinimalChart period hPeriod configuration data analysis chartData)
      (SameAction period hPeriod configuration data analysis chartData))
    blocks.finiteBV
    (finiteBV_core_left_zero period hPeriod configuration data analysis
      chartData) first second

/-- Sum of the four still-nonlinearly-uncompleted physical Hessians. -/
def globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalHessian :
    Reduced period hPeriod configuration data analysis →L[Real]
      Reduced period hPeriod configuration data analysis →L[Real] Real :=
  (((globalCandidateAMinimalPhysicalReducedCompletedInteractionHessian period
      hPeriod configuration data analysis chartData blocks +
    globalCandidateAMinimalPhysicalReducedCompletedEinsteinHilbertPlusHessian
      period hPeriod configuration data analysis chartData blocks) +
    globalCandidateAMinimalPhysicalReducedCompletedEinsteinHilbertMinusHessian
      period hPeriod configuration data analysis chartData blocks) +
    globalCandidateAMinimalPhysicalReducedCompletedFiniteBVHessian period
      hPeriod configuration data analysis chartData blocks)

theorem globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalHessian_symmetric
    (first second : Reduced period hPeriod configuration data analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalHessian
        period hPeriod configuration data analysis chartData blocks first second =
      globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalHessian
        period hPeriod configuration data analysis chartData blocks second first := by
  simp only [globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalHessian,
    add_apply]
  rw [globalCandidateAMinimalPhysicalReducedCompletedInteractionHessian_symmetric,
    globalCandidateAMinimalPhysicalReducedCompletedEinsteinHilbertPlusHessian_symmetric,
    globalCandidateAMinimalPhysicalReducedCompletedEinsteinHilbertMinusHessian_symmetric,
    globalCandidateAMinimalPhysicalReducedCompletedFiniteBVHessian_symmetric]

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalHessian_core
    (first second : Core period hPeriod configuration analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalHessian
        period hPeriod configuration data analysis chartData blocks
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk first))
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk second)) =
      (((diagonalExtendedBulkH11InteractionHessianOnCore period hPeriod
          configuration data analysis
          (MinimalChart period hPeriod configuration data analysis chartData)
          (SameAction period hPeriod configuration data analysis chartData)
          first second +
        diagonalExtendedBulkH11EinsteinHilbertPlusHessianOnCore period hPeriod
          configuration data analysis
          (MinimalChart period hPeriod configuration data analysis chartData)
          (SameAction period hPeriod configuration data analysis chartData)
          first second) +
        diagonalExtendedBulkH11EinsteinHilbertMinusHessianOnCore period hPeriod
          configuration data analysis
          (MinimalChart period hPeriod configuration data analysis chartData)
          (SameAction period hPeriod configuration data analysis chartData)
          first second) +
        diagonalExtendedBulkH11FiniteBVHessianOnCore period hPeriod
          configuration data analysis
          (MinimalChart period hPeriod configuration data analysis chartData)
          (SameAction period hPeriod configuration data analysis chartData)
          first second) := by
  simp only [globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalHessian,
    add_apply]
  rw [globalCandidateAMinimalPhysicalReducedCompletedInteractionHessian_core,
    globalCandidateAMinimalPhysicalReducedCompletedEinsteinHilbertPlusHessian_core,
    globalCandidateAMinimalPhysicalReducedCompletedEinsteinHilbertMinusHessian_core,
    globalCandidateAMinimalPhysicalReducedCompletedFiniteBVHessian_core]

/-- Base-point quadratic energy of the four remaining physical blocks. -/
def globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticAction :
    Reduced period hPeriod configuration data analysis → Real :=
  fun state => (1 / 2 : Real) *
    globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalHessian
      period hPeriod configuration data analysis chartData blocks state state

theorem globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticAction_contDiff :
    ContDiff Real ⊤
      (globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticAction
        period hPeriod configuration data analysis chartData blocks) := by
  unfold globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticAction
  exact contDiff_const.mul
    ((globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalHessian
      period hPeriod configuration data analysis chartData blocks
      ).contDiff.clm_apply contDiff_id)

theorem globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticAction_contDiff_two :
    ContDiff Real 2
      (globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticAction
        period hPeriod configuration data analysis chartData blocks) :=
  (globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticAction_contDiff
    period hPeriod configuration data analysis chartData blocks).of_le (by simp)

theorem globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticAction_fderiv
    (state : Reduced period hPeriod configuration data analysis) :
    fderiv Real
        (globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticAction
          period hPeriod configuration data analysis chartData blocks) state =
      globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalHessian
        period hPeriod configuration data analysis chartData blocks state := by
  exact (symmetricQuadratic_hasFDerivAt
    (globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalHessian
      period hPeriod configuration data analysis chartData blocks)
    (globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalHessian_symmetric
      period hPeriod configuration data analysis chartData blocks) state).fderiv

/-- Strong Riesz representative of the remaining physical Hessian. -/
def globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalRieszOperator :
    Reduced period hPeriod configuration data analysis →L[Real]
      Reduced period hPeriod configuration data analysis :=
  @InnerProductSpace.continuousLinearMapOfBilin
    Real (Reduced period hPeriod configuration data analysis)
    inferInstance inferInstance inferInstance inferInstance
    (globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalHessian
      period hPeriod configuration data analysis chartData blocks)

theorem globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalRieszOperator_pairing
    (state test : Reduced period hPeriod configuration data analysis) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalRieszOperator
          period hPeriod configuration data analysis chartData blocks state) test =
      globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalHessian
        period hPeriod configuration data analysis chartData blocks state test := by
  exact @InnerProductSpace.continuousLinearMapOfBilin_apply
    Real (Reduced period hPeriod configuration data analysis)
    inferInstance inferInstance inferInstance inferInstance
    (globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalHessian
      period hPeriod configuration data analysis chartData blocks) state test

theorem globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalRieszOperator_gradient_pairing
    (state test : Reduced period hPeriod configuration data analysis) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalRieszOperator
          period hPeriod configuration data analysis chartData blocks state) test =
      fderiv Real
        (globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticAction
          period hPeriod configuration data analysis chartData blocks) state test := by
  rw [globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalRieszOperator_pairing,
    globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticAction_fderiv]

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticAction_core
    (core : Core period hPeriod configuration analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticAction
        period hPeriod configuration data analysis chartData blocks
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk core)) =
      (1 / 2 : Real) *
        (((diagonalExtendedBulkH11InteractionHessianOnCore period hPeriod
            configuration data analysis
            (MinimalChart period hPeriod configuration data analysis chartData)
            (SameAction period hPeriod configuration data analysis chartData)
            core core +
          diagonalExtendedBulkH11EinsteinHilbertPlusHessianOnCore period hPeriod
            configuration data analysis
            (MinimalChart period hPeriod configuration data analysis chartData)
            (SameAction period hPeriod configuration data analysis chartData)
            core core) +
          diagonalExtendedBulkH11EinsteinHilbertMinusHessianOnCore period hPeriod
            configuration data analysis
            (MinimalChart period hPeriod configuration data analysis chartData)
            (SameAction period hPeriod configuration data analysis chartData)
            core core) +
          diagonalExtendedBulkH11FiniteBVHessianOnCore period hPeriod
            configuration data analysis
            (MinimalChart period hPeriod configuration data analysis chartData)
            (SameAction period hPeriod configuration data analysis chartData)
            core core) := by
  rw [globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticAction,
    globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalHessian_core]

/-! ## Strongest presently available reduced action and Euler operator -/

/-- The genuine Robin domain remains the domain of the strengthened action. -/
def globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticDomain :
    Set (Reduced period hPeriod configuration data analysis) :=
  globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticDomain
    period hPeriod configuration data analysis chartData einsteinScale projection

theorem globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticDomain_isOpen :
    IsOpen
      (globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticDomain
        period hPeriod configuration data analysis chartData einsteinScale
          projection) :=
  globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticDomain_isOpen
    period hPeriod configuration data analysis chartData einsteinScale projection

include hTransverse in
theorem globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticDomain_zero_mem :
    (0 : Reduced period hPeriod configuration data analysis) ∈
      globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticDomain
        period hPeriod configuration data analysis chartData einsteinScale
          projection :=
  globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticDomain_zero_mem
    period hPeriod configuration data analysis chartData einsteinScale
      hTransverse projection

/-- Strongest available reduced action: exact graph and Robin terms together
with Maxwell and remaining physical base-point Hessian quadratics. -/
def globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticAction :
    Reduced period hPeriod configuration data analysis → Real :=
  fun state =>
    globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticAction
        period hPeriod configuration data analysis chartData einsteinScale
          projection blocks.maxwellPlus blocks.maxwellMinus state +
      globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticAction
        period hPeriod configuration data analysis chartData blocks state

include hTransverse in
theorem globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticAction_contDiffOn_two :
    ContDiffOn Real 2
      (globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticAction
        period hPeriod configuration data analysis chartData einsteinScale
          projection blocks)
      (globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticDomain
        period hPeriod configuration data analysis chartData einsteinScale
          projection) := by
  exact
    (globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticAction_contDiffOn_two
      period hPeriod configuration data analysis chartData einsteinScale
        hTransverse projection blocks.maxwellPlus blocks.maxwellMinus).add
      (globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticAction_contDiff_two
        period hPeriod configuration data analysis chartData blocks).contDiffOn

include hTransverse in
theorem globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticAction_contDiffAt_zero :
    ContDiffAt Real 2
      (globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticAction
        period hPeriod configuration data analysis chartData einsteinScale
          projection blocks) 0 :=
  (globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticAction_contDiffOn_two
    period hPeriod configuration data analysis chartData einsteinScale
      hTransverse projection blocks).contDiffAt
    ((globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticDomain_isOpen
      period hPeriod configuration data analysis chartData einsteinScale
        projection).mem_nhds
      (globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticDomain_zero_mem
        period hPeriod configuration data analysis chartData einsteinScale
          hTransverse projection))

/-- Frechet Euler covector of the strongest currently available action. -/
noncomputable def globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticEulerCovector
    (state : Reduced period hPeriod configuration data analysis) :
    Reduced period hPeriod configuration data analysis →L[Real] Real :=
  fderiv Real
    (globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticAction
      period hPeriod configuration data analysis chartData einsteinScale
        projection blocks) state

/-- Strong Riesz residual of the strongest currently available action. -/
noncomputable def globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticRieszResidual
    (state : Reduced period hPeriod configuration data analysis) :
    Reduced period hPeriod configuration data analysis :=
  (InnerProductSpace.toDual Real
    (Reduced period hPeriod configuration data analysis)).symm
      (globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticEulerCovector
        period hPeriod configuration data analysis chartData einsteinScale
          projection blocks state)

theorem globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticRieszResidual_pairing
    (state test : Reduced period hPeriod configuration data analysis) :
    inner Real
        (globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticRieszResidual
          period hPeriod configuration data analysis chartData einsteinScale
            projection blocks state) test =
      globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticEulerCovector
        period hPeriod configuration data analysis chartData einsteinScale
          projection blocks state test := by
  unfold globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticRieszResidual
  exact InnerProductSpace.toDual_symm_apply

include hTransverse in
theorem globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticAction_fderiv_add
    (state : Reduced period hPeriod configuration data analysis)
    (hState : state ∈
      globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticDomain
        period hPeriod configuration data analysis chartData einsteinScale
          projection) :
    fderiv Real
        (globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticAction
          period hPeriod configuration data analysis chartData einsteinScale
            projection blocks) state =
      fderiv Real
          (globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticAction
            period hPeriod configuration data analysis chartData einsteinScale
              projection blocks.maxwellPlus blocks.maxwellMinus) state +
        globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalHessian
          period hPeriod configuration data analysis chartData blocks state := by
  have hBase : DifferentiableAt Real
      (globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticAction
        period hPeriod configuration data analysis chartData einsteinScale
          projection blocks.maxwellPlus blocks.maxwellMinus) state :=
    ((globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticAction_contDiffOn_two
      period hPeriod configuration data analysis chartData einsteinScale
        hTransverse projection blocks.maxwellPlus blocks.maxwellMinus).contDiffAt
      ((globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticDomain_isOpen
        period hPeriod configuration data analysis chartData einsteinScale
          projection).mem_nhds hState)).differentiableAt (by norm_num)
  have hRemaining : DifferentiableAt Real
      (globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticAction
        period hPeriod configuration data analysis chartData blocks) state :=
    ((globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticAction_contDiff_two
      period hPeriod configuration data analysis chartData blocks).differentiable
        (by norm_num)).differentiableAt
  unfold globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticAction
  change fderiv Real
      (globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticAction
          period hPeriod configuration data analysis chartData einsteinScale
            projection blocks.maxwellPlus blocks.maxwellMinus +
        globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticAction
          period hPeriod configuration data analysis chartData blocks) state = _
  rw [fderiv_add hBase hRemaining,
    globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticAction_fderiv]

def GlobalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticIsCritical
    (state : Reduced period hPeriod configuration data analysis) : Prop :=
  globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticRieszResidual
    period hPeriod configuration data analysis chartData einsteinScale projection
      blocks state = 0

theorem globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticIsCritical_iff_fderiv_eq_zero
    (state : Reduced period hPeriod configuration data analysis) :
    GlobalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticIsCritical
        period hPeriod configuration data analysis chartData einsteinScale
          projection blocks state ↔
      fderiv Real
          (globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticAction
            period hPeriod configuration data analysis chartData einsteinScale
              projection blocks) state = 0 := by
  unfold GlobalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticIsCritical
    globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticRieszResidual
    globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticEulerCovector
  exact (InnerProductSpace.toDual Real
    (Reduced period hPeriod configuration data analysis)).symm.map_eq_zero_iff

@[simp]
theorem globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticAction_core
    (core : Core period hPeriod configuration analysis) :
    globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticAction
        period hPeriod configuration data analysis chartData einsteinScale
          projection blocks
        (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
          period hPeriod configuration data analysis
          (Submodule.Quotient.mk core)) =
      (globalCandidateAMinimalPhysicalReducedCompletedGraphAction period hPeriod
          configuration data analysis
          (globalCandidateAMinimalPhysicalReducedSmoothCoreQuotientEmbedding
            period hPeriod configuration data analysis
            (Submodule.Quotient.mk core)) +
        (globalCandidateACanonicalSixLocalBlocks period hPeriod
          (MinimalChart period hPeriod configuration data analysis chartData)).robin
          (globalCandidateAMinimalPhysicalReducedCoreToChart period hPeriod
            configuration data analysis chartData
            (Submodule.Quotient.mk core)) +
        ((1 / 2 : Real) *
            diagonalExtendedBulkH11MaxwellPlusHessianOnCore period hPeriod
              configuration data analysis
              (MinimalChart period hPeriod configuration data analysis chartData)
              (SameAction period hPeriod configuration data analysis chartData)
              core core +
          (1 / 2 : Real) *
            diagonalExtendedBulkH11MaxwellMinusHessianOnCore period hPeriod
              configuration data analysis
              (MinimalChart period hPeriod configuration data analysis chartData)
              (SameAction period hPeriod configuration data analysis chartData)
              core core)) +
        (1 / 2 : Real) *
          (((diagonalExtendedBulkH11InteractionHessianOnCore period hPeriod
              configuration data analysis
              (MinimalChart period hPeriod configuration data analysis chartData)
              (SameAction period hPeriod configuration data analysis chartData)
              core core +
            diagonalExtendedBulkH11EinsteinHilbertPlusHessianOnCore period hPeriod
              configuration data analysis
              (MinimalChart period hPeriod configuration data analysis chartData)
              (SameAction period hPeriod configuration data analysis chartData)
              core core) +
            diagonalExtendedBulkH11EinsteinHilbertMinusHessianOnCore period hPeriod
              configuration data analysis
              (MinimalChart period hPeriod configuration data analysis chartData)
              (SameAction period hPeriod configuration data analysis chartData)
              core core) +
            diagonalExtendedBulkH11FiniteBVHessianOnCore period hPeriod
              configuration data analysis
              (MinimalChart period hPeriod configuration data analysis chartData)
              (SameAction period hPeriod configuration data analysis chartData)
              core core) := by
  rw [globalCandidateAMinimalPhysicalReducedCompletedAvailableQuadraticAction,
    globalCandidateAMinimalPhysicalReducedCompletedGraphRobinMaxwellQuadraticAction_core,
    globalCandidateAMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticAction_core]

end

end
end P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalReducedCompletedRemainingPhysicalQuadraticEuler4D
end JanusFormal
