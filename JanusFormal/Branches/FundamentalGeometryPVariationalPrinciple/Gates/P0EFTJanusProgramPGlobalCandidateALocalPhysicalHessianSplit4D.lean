import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalLocalCovariantHessianResidualBridge4D

/-!
# Physical/matter--LL split of the local Candidate-A Hessian

The diagonal graph contains the BRST gauge-fixing, primitive matter and LL
blocks.  It does not contain the physical Einstein--Hilbert, interaction,
Maxwell or boundary Hessians.  Consequently the former comparison residual
must not be set to zero: it contains genuine physical dynamics.

This gate splits the exact local nine-block Hessian into its physical and
matter--LL parts.  On the diagonal smooth core, the old residual is exactly
the physical Hessian plus the sole matter--LL same-action mismatch.  The
correct augmented graph comparison is therefore equivalent only to the
vanishing of that mismatch, while retaining the full physical Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open Filter MeasureTheory Set
open scoped Manifold ContDiff Topology
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalHessianFrontier4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalLocalCovariantHessianResidualBridge4D

universe u

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

/-! ## Exact split of the nine action blocks -/

/-- The seven genuinely physical blocks not already represented by the
matter--LL graph. -/
def fullCoupledPhysicalAction
    {Model : Type u}
    (blocks : FullCoupledActionBlocks Model) (point : Model) : Real :=
  ((((((blocks.candidateA point + blocks.robin point) +
    blocks.einsteinHilbertPlus point) +
    blocks.einsteinHilbertMinus point) +
    blocks.maxwellPlus point) +
    blocks.maxwellMinus point) +
    blocks.finiteBV point)

/-- The two physical action blocks whose graph Hessians are already closed. -/
def fullCoupledMatterLLAction
    {Model : Type u}
    (blocks : FullCoupledActionBlocks Model) (point : Model) : Real :=
  blocks.matter point + blocks.ll point

theorem fullCoupledAction_eq_physical_add_matterLL
    {Model : Type u}
    (blocks : FullCoupledActionBlocks Model) :
    fullCoupledAction blocks = fun point =>
      fullCoupledPhysicalAction blocks point +
        fullCoupledMatterLLAction blocks point := by
  funext point
  unfold fullCoupledAction fullCoupledPhysicalAction
    fullCoupledMatterLLAction
  ring

theorem fullCoupledPhysicalAction_contDiffAt
    {Model : Type u}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (blocks : FullCoupledActionBlocks Model) (point : Model)
    (hC2 : FullCoupledC2At blocks point) :
    ContDiffAt Real 2 (fullCoupledPhysicalAction blocks) point := by
  exact ((((((hC2.candidateA.add hC2.robin).add
    hC2.einsteinHilbertPlus).add hC2.einsteinHilbertMinus).add
    hC2.maxwellPlus).add hC2.maxwellMinus).add hC2.finiteBV)

theorem fullCoupledMatterLLAction_contDiffAt
    {Model : Type u}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (blocks : FullCoupledActionBlocks Model) (point : Model)
    (hC2 : FullCoupledC2At blocks point) :
    ContDiffAt Real 2 (fullCoupledMatterLLAction blocks) point :=
  hC2.matter.add hC2.ll

/-! ## Local physical and matter--LL Hessians -/

/-- Hessian of the seven physical blocks on the ambient local model. -/
noncomputable def globalCandidateALocalPhysicalHessian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model) :
    chart.Model →L[Real] chart.Model →L[Real] Real :=
  fderiv Real
    (actionGradient
      (fullCoupledPhysicalAction
        (globalCandidateAActionBlocks period hPeriod
          (chart.family.toActionFamily period hPeriod 0
            chart.zero_mem_domain) measure))) point

/-- Hessian of the exact matter and LL summands on the same local model. -/
noncomputable def globalCandidateALocalMatterLLHessian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model) :
    chart.Model →L[Real] chart.Model →L[Real] Real :=
  fderiv Real
    (actionGradient
      (fullCoupledMatterLLAction
        (globalCandidateAActionBlocks period hPeriod
          (chart.family.toActionFamily period hPeriod 0
            chart.zero_mem_domain) measure))) point

/-- The actual local Hessian is the sum of the physical and matter--LL
Hessians.  This is Frechet calculus on the exact nine-block action. -/
theorem globalCandidateALocalHessian_eq_physical_add_matterLL
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model) (hPoint : point ∈ chart.family.domain) :
    globalCandidateALocalHessian period hPeriod chart point =
      globalCandidateALocalPhysicalHessian period hPeriod chart point +
        globalCandidateALocalMatterLLHessian period hPeriod chart point := by
  let blocks := globalCandidateAActionBlocks period hPeriod
    (chart.family.toActionFamily period hPeriod 0 chart.zero_mem_domain) measure
  have hC2 : FullCoupledC2At blocks point :=
    fullCoupledC2WithinAt_toAt
      (chart.blocksC2Within point hPoint) chart.isOpen_domain hPoint
  have hPhysical : ContDiffAt Real 2
      (fullCoupledPhysicalAction blocks) point :=
    fullCoupledPhysicalAction_contDiffAt blocks point hC2
  have hMatterLL : ContDiffAt Real 2
      (fullCoupledMatterLLAction blocks) point :=
    fullCoupledMatterLLAction_contDiffAt blocks point hC2
  have hGradient :
      actionGradient
          (fun state => fullCoupledPhysicalAction blocks state +
            fullCoupledMatterLLAction blocks state) =ᶠ[𝓝 point]
        fun state =>
          actionGradient (fullCoupledPhysicalAction blocks) state +
            actionGradient (fullCoupledMatterLLAction blocks) state := by
    change
      fderiv Real
          (fun state => fullCoupledPhysicalAction blocks state +
            fullCoupledMatterLLAction blocks state) =ᶠ[𝓝 point]
        fun state =>
          fderiv Real (fullCoupledPhysicalAction blocks) state +
            fderiv Real (fullCoupledMatterLLAction blocks) state
    filter_upwards [hPhysical.eventually (by norm_num),
      hMatterLL.eventually (by norm_num)] with state hPhysicalState hMatterLLState
    exact fderiv_add
      (hPhysicalState.differentiableAt (by norm_num))
      (hMatterLLState.differentiableAt (by norm_num))
  have hPhysicalGradientC1 : ContDiffAt Real 1
      (actionGradient (fullCoupledPhysicalAction blocks)) point := by
    change ContDiffAt Real 1
      (fderiv Real (fullCoupledPhysicalAction blocks)) point
    exact hPhysical.fderiv_right (by norm_num)
  have hMatterLLGradientC1 : ContDiffAt Real 1
      (actionGradient (fullCoupledMatterLLAction blocks)) point := by
    change ContDiffAt Real 1
      (fderiv Real (fullCoupledMatterLLAction blocks)) point
    exact hMatterLL.fderiv_right (by norm_num)
  have hPhysicalGradient : DifferentiableAt Real
      (actionGradient (fullCoupledPhysicalAction blocks)) point :=
    hPhysicalGradientC1.differentiableAt (by norm_num)
  have hMatterLLGradient : DifferentiableAt Real
      (actionGradient (fullCoupledMatterLLAction blocks)) point :=
    hMatterLLGradientC1.differentiableAt (by norm_num)
  unfold globalCandidateALocalHessian
    globalCandidateALocalEulerLagrangeOperator
    globalCandidateALocalActionPullback
    globalCandidateALocalPhysicalHessian
    globalCandidateALocalMatterLLHessian
  change
    fderiv Real (actionGradient (fullCoupledAction blocks)) point = _
  rw [fullCoupledAction_eq_physical_add_matterLL]
  rw [hGradient.fderiv_eq]
  exact fderiv_add hPhysicalGradient hMatterLLGradient

/-! ## Correct comparison on the diagonal smooth core -/

/-- Pullback of the seven-block physical Hessian to the diagonal core. -/
def diagonalExtendedBulkLocalPhysicalCovariantHessianOnCore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge : ProgramPGlobalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) : Real :=
  globalCandidateALocalPhysicalHessian period hPeriod chart bridge.basePoint
    (bridge.tangentAnalysis
      (diagonalExtendedBulkLegacyTangentLinearMap period hPeriod
        configuration data analysis first))
    (bridge.tangentAnalysis
      (diagonalExtendedBulkLegacyTangentLinearMap period hPeriod
        configuration data analysis second))

/-- Pullback of the exact matter--LL Hessian to the same core. -/
def diagonalExtendedBulkLocalMatterLLCovariantHessianOnCore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge : ProgramPGlobalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) : Real :=
  globalCandidateALocalMatterLLHessian period hPeriod chart bridge.basePoint
    (bridge.tangentAnalysis
      (diagonalExtendedBulkLegacyTangentLinearMap period hPeriod
        configuration data analysis first))
    (bridge.tangentAnalysis
      (diagonalExtendedBulkLegacyTangentLinearMap period hPeriod
        configuration data analysis second))

theorem diagonalExtendedBulkLocalCovariantHessian_split
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge : ProgramPGlobalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkLocalCovariantHessianOnCore period hPeriod
        configuration data analysis chart bridge first second =
      diagonalExtendedBulkLocalPhysicalCovariantHessianOnCore period hPeriod
          configuration data analysis chart bridge first second +
        diagonalExtendedBulkLocalMatterLLCovariantHessianOnCore period hPeriod
          configuration data analysis chart bridge first second := by
  unfold diagonalExtendedBulkLocalCovariantHessianOnCore
    globalCandidateALocalHessianOnSmoothGlobalCore
    diagonalExtendedBulkLocalPhysicalCovariantHessianOnCore
    diagonalExtendedBulkLocalMatterLLCovariantHessianOnCore
  rw [globalCandidateALocalHessian_eq_physical_add_matterLL
    period hPeriod chart bridge.basePoint bridge.basePoint_mem]
  rfl

/-- The only mismatch with the already closed matter--LL graph blocks. -/
def diagonalExtendedBulkLocalMatterLLSameActionMismatchOnCore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge : ProgramPGlobalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) : Real :=
  diagonalExtendedBulkLocalMatterLLCovariantHessianOnCore period hPeriod
      configuration data analysis chart bridge first second -
    diagonalExtendedBulkMatterLLHessianOnCore period hPeriod
      configuration data analysis first second

/-- The former “physical residual” is not expected to vanish: it is the
physical Hessian plus the matter--LL same-action mismatch. -/
theorem diagonalExtendedBulkLocalPhysicalHessianResidual_split
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge : ProgramPGlobalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkLocalPhysicalHessianResidualOnCore period hPeriod
        configuration data analysis chart bridge first second =
      diagonalExtendedBulkLocalPhysicalCovariantHessianOnCore period hPeriod
          configuration data analysis chart bridge first second +
        diagonalExtendedBulkLocalMatterLLSameActionMismatchOnCore period hPeriod
          configuration data analysis chart bridge first second := by
  unfold diagonalExtendedBulkLocalPhysicalHessianResidualOnCore
    diagonalExtendedBulkLocalMatterLLSameActionMismatchOnCore
  rw [diagonalExtendedBulkLocalCovariantHessian_split]
  ring

/-- Correct target: BRST graph plus the retained physical Hessian. -/
def diagonalExtendedBulkLocalAugmentedGraphHessianOnCore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge : ProgramPGlobalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) : Real :=
  diagonalExtendedBulkGraphHessianOnCore period hPeriod configuration
      data analysis first second +
    diagonalExtendedBulkLocalPhysicalCovariantHessianOnCore period hPeriod
      configuration data analysis chart bridge first second

theorem diagonalExtendedBulkLocalGaugeFixedCovariantHessian_correct_decomposition
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge : ProgramPGlobalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkLocalGaugeFixedCovariantHessianOnCore period hPeriod
        configuration data analysis chart bridge first second =
      diagonalExtendedBulkLocalAugmentedGraphHessianOnCore period hPeriod
          configuration data analysis chart bridge first second +
        diagonalExtendedBulkLocalMatterLLSameActionMismatchOnCore period hPeriod
          configuration data analysis chart bridge first second := by
  rw [diagonalExtendedBulkLocalGaugeFixedCovariantHessian_decomposition,
    diagonalExtendedBulkLocalPhysicalHessianResidual_split]
  unfold diagonalExtendedBulkLocalAugmentedGraphHessianOnCore
  ring

/-- Agreement with the correct augmented graph is equivalent only to the
already sectorially proved matter--LL identification. -/
theorem diagonalExtendedBulkLocalGaugeFixedCovariantHessian_eq_augmented_iff
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (bridge : ProgramPGlobalLocalVariationalChartCoreBridge4D
      period hPeriod configuration.physical chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkLocalGaugeFixedCovariantHessianOnCore period hPeriod
        configuration data analysis chart bridge first second =
        diagonalExtendedBulkLocalAugmentedGraphHessianOnCore period hPeriod
          configuration data analysis chart bridge first second ↔
      diagonalExtendedBulkLocalMatterLLSameActionMismatchOnCore period hPeriod
        configuration data analysis chart bridge first second = 0 := by
  rw [diagonalExtendedBulkLocalGaugeFixedCovariantHessian_correct_decomposition]
  constructor <;> intro h <;> linarith

end
end P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D
end JanusFormal
