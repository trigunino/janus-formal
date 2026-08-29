import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D

/-!
# Blockwise construction of the seven H11 physical extensions

H11 requires one bounded symmetric form carrying the seven physical action
blocks on the already existing diagonal `L²` graph completion.  This file
splits that single contract into seven independently auditable extensions:
interaction, GHY/Robin, the two Einstein--Hilbert sectors, the two Maxwell
sectors, and the finite null/BV block.

Each component stores exact agreement with the corresponding second Frechet
derivative on the existing dense smooth core.  Their sum constructs the
original `GlobalCandidateASevenPhysicalCommonDomainExtension4D`; no new action,
field, completion, coupling, or physical hypothesis is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockExtensions4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open Filter MeasureTheory Set Topology
open scoped Manifold ContDiff InnerProductSpace
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
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D

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

private abbrev SevenBlockHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  CommonAugmentedHilbert period hPeriod configuration data analysis

/-! ## A reusable Hessian-addition lemma -/

private theorem actionHessian_add
    {E : Type u} [NormedAddCommGroup E] [NormedSpace Real E]
    (first second : E → Real) (point : E)
    (hFirst : ContDiffAt Real 2 first point)
    (hSecond : ContDiffAt Real 2 second point) :
    fderiv Real (actionGradient (fun state => first state + second state)) point =
      fderiv Real (actionGradient first) point +
        fderiv Real (actionGradient second) point := by
  have hGradient :
      actionGradient (fun state => first state + second state) =ᶠ[𝓝 point]
        fun state => actionGradient first state + actionGradient second state := by
    change
      fderiv Real (fun state => first state + second state) =ᶠ[𝓝 point]
        fun state => fderiv Real first state + fderiv Real second state
    filter_upwards [hFirst.eventually (by norm_num),
      hSecond.eventually (by norm_num)] with state hFirstState hSecondState
    exact fderiv_add
      (hFirstState.differentiableAt (by norm_num))
      (hSecondState.differentiableAt (by norm_num))
  have hFirstGradient : DifferentiableAt Real (actionGradient first) point :=
    (hFirst.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hSecondGradient : DifferentiableAt Real (actionGradient second) point :=
    (hSecond.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [hGradient.fderiv_eq]
  exact fderiv_add hFirstGradient hSecondGradient

/-! ## The seven actual local block Hessians -/

private def h11LocalBlocks
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :=
  globalCandidateAActionBlocks period hPeriod
    (chart.family.toActionFamily period hPeriod 0 chart.zero_mem_domain) measure

noncomputable def globalCandidateAH11LocalInteractionHessian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) (point : chart.Model) :=
  fderiv Real
    (actionGradient (h11LocalBlocks period hPeriod chart).candidateA) point

noncomputable def globalCandidateAH11LocalGHYHessian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) (point : chart.Model) :=
  fderiv Real (actionGradient (h11LocalBlocks period hPeriod chart).robin) point

noncomputable def globalCandidateAH11LocalEinsteinHilbertPlusHessian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) (point : chart.Model) :=
  fderiv Real
    (actionGradient
      (h11LocalBlocks period hPeriod chart).einsteinHilbertPlus) point

noncomputable def globalCandidateAH11LocalEinsteinHilbertMinusHessian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) (point : chart.Model) :=
  fderiv Real
    (actionGradient
      (h11LocalBlocks period hPeriod chart).einsteinHilbertMinus) point

noncomputable def globalCandidateAH11LocalMaxwellPlusHessian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) (point : chart.Model) :=
  fderiv Real
    (actionGradient (h11LocalBlocks period hPeriod chart).maxwellPlus) point

noncomputable def globalCandidateAH11LocalMaxwellMinusHessian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) (point : chart.Model) :=
  fderiv Real
    (actionGradient (h11LocalBlocks period hPeriod chart).maxwellMinus) point

noncomputable def globalCandidateAH11LocalFiniteBVHessian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) (point : chart.Model) :=
  fderiv Real
    (actionGradient (h11LocalBlocks period hPeriod chart).finiteBV) point

/-- The seven-block local Hessian is exactly the sum of the seven separately
named second Frechet derivatives. -/
theorem globalCandidateAH11LocalPhysicalHessian_eq_seven
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model) (hPoint : point ∈ chart.family.domain) :
    globalCandidateALocalPhysicalHessian period hPeriod chart point =
      ((((((globalCandidateAH11LocalInteractionHessian period hPeriod chart point +
        globalCandidateAH11LocalGHYHessian period hPeriod chart point) +
        globalCandidateAH11LocalEinsteinHilbertPlusHessian period hPeriod chart
          point) +
        globalCandidateAH11LocalEinsteinHilbertMinusHessian period hPeriod chart
          point) +
        globalCandidateAH11LocalMaxwellPlusHessian period hPeriod chart point) +
        globalCandidateAH11LocalMaxwellMinusHessian period hPeriod chart point) +
        globalCandidateAH11LocalFiniteBVHessian period hPeriod chart point) := by
  let blocks := h11LocalBlocks period hPeriod chart
  have hC2 : FullCoupledC2At blocks point :=
    fullCoupledC2WithinAt_toAt
      (chart.blocksC2Within point hPoint) chart.isOpen_domain hPoint
  unfold globalCandidateALocalPhysicalHessian fullCoupledPhysicalAction
    globalCandidateAH11LocalInteractionHessian
    globalCandidateAH11LocalGHYHessian
    globalCandidateAH11LocalEinsteinHilbertPlusHessian
    globalCandidateAH11LocalEinsteinHilbertMinusHessian
    globalCandidateAH11LocalMaxwellPlusHessian
    globalCandidateAH11LocalMaxwellMinusHessian
    globalCandidateAH11LocalFiniteBVHessian
  change
    fderiv Real
        (actionGradient
          (fun state =>
            ((((((blocks.candidateA state + blocks.robin state) +
              blocks.einsteinHilbertPlus state) +
              blocks.einsteinHilbertMinus state) +
              blocks.maxwellPlus state) + blocks.maxwellMinus state) +
              blocks.finiteBV state))) point = _
  rw [actionHessian_add
      (fun state => (((((blocks.candidateA state + blocks.robin state) +
        blocks.einsteinHilbertPlus state) + blocks.einsteinHilbertMinus state) +
        blocks.maxwellPlus state) + blocks.maxwellMinus state))
      blocks.finiteBV point
      (((((hC2.candidateA.add hC2.robin).add hC2.einsteinHilbertPlus).add
        hC2.einsteinHilbertMinus).add hC2.maxwellPlus).add hC2.maxwellMinus)
      hC2.finiteBV]
  rw [actionHessian_add
      (fun state => ((((blocks.candidateA state + blocks.robin state) +
        blocks.einsteinHilbertPlus state) + blocks.einsteinHilbertMinus state) +
        blocks.maxwellPlus state))
      blocks.maxwellMinus point
      ((((hC2.candidateA.add hC2.robin).add hC2.einsteinHilbertPlus).add
        hC2.einsteinHilbertMinus).add hC2.maxwellPlus)
      hC2.maxwellMinus]
  rw [actionHessian_add
      (fun state => (((blocks.candidateA state + blocks.robin state) +
        blocks.einsteinHilbertPlus state) + blocks.einsteinHilbertMinus state))
      blocks.maxwellPlus point
      (((hC2.candidateA.add hC2.robin).add hC2.einsteinHilbertPlus).add
        hC2.einsteinHilbertMinus)
      hC2.maxwellPlus]
  rw [actionHessian_add
      (fun state => ((blocks.candidateA state + blocks.robin state) +
        blocks.einsteinHilbertPlus state))
      blocks.einsteinHilbertMinus point
      ((hC2.candidateA.add hC2.robin).add hC2.einsteinHilbertPlus)
      hC2.einsteinHilbertMinus]
  rw [actionHessian_add
      (fun state => blocks.candidateA state + blocks.robin state)
      blocks.einsteinHilbertPlus point
      (hC2.candidateA.add hC2.robin) hC2.einsteinHilbertPlus]
  rw [actionHessian_add blocks.candidateA blocks.robin point
      hC2.candidateA hC2.robin]

/-! ## Pullback of each block to the existing diagonal smooth core -/

private def h11CoreDirection
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
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (core : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) : chart.Model :=
  sameAction.chartBridge.tangentAnalysis
    (diagonalExtendedBulkMinimalPhysicalTangentLinearMap period hPeriod
      configuration data analysis core)

noncomputable def diagonalExtendedBulkH11InteractionHessianOnCore
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
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) : Real :=
  globalCandidateAH11LocalInteractionHessian period hPeriod chart
    sameAction.chartBridge.basePoint
    (h11CoreDirection period hPeriod configuration data analysis chart sameAction
      first)
    (h11CoreDirection period hPeriod configuration data analysis chart sameAction
      second)

noncomputable def diagonalExtendedBulkH11GHYHessianOnCore
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
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) : Real :=
  globalCandidateAH11LocalGHYHessian period hPeriod chart
    sameAction.chartBridge.basePoint
    (h11CoreDirection period hPeriod configuration data analysis chart sameAction
      first)
    (h11CoreDirection period hPeriod configuration data analysis chart sameAction
      second)

noncomputable def diagonalExtendedBulkH11EinsteinHilbertPlusHessianOnCore
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
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) : Real :=
  globalCandidateAH11LocalEinsteinHilbertPlusHessian period hPeriod chart
    sameAction.chartBridge.basePoint
    (h11CoreDirection period hPeriod configuration data analysis chart sameAction
      first)
    (h11CoreDirection period hPeriod configuration data analysis chart sameAction
      second)

noncomputable def diagonalExtendedBulkH11EinsteinHilbertMinusHessianOnCore
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
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) : Real :=
  globalCandidateAH11LocalEinsteinHilbertMinusHessian period hPeriod chart
    sameAction.chartBridge.basePoint
    (h11CoreDirection period hPeriod configuration data analysis chart sameAction
      first)
    (h11CoreDirection period hPeriod configuration data analysis chart sameAction
      second)

noncomputable def diagonalExtendedBulkH11MaxwellPlusHessianOnCore
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
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) : Real :=
  globalCandidateAH11LocalMaxwellPlusHessian period hPeriod chart
    sameAction.chartBridge.basePoint
    (h11CoreDirection period hPeriod configuration data analysis chart sameAction
      first)
    (h11CoreDirection period hPeriod configuration data analysis chart sameAction
      second)

noncomputable def diagonalExtendedBulkH11MaxwellMinusHessianOnCore
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
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) : Real :=
  globalCandidateAH11LocalMaxwellMinusHessian period hPeriod chart
    sameAction.chartBridge.basePoint
    (h11CoreDirection period hPeriod configuration data analysis chart sameAction
      first)
    (h11CoreDirection period hPeriod configuration data analysis chart sameAction
      second)

noncomputable def diagonalExtendedBulkH11FiniteBVHessianOnCore
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
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) : Real :=
  globalCandidateAH11LocalFiniteBVHessian period hPeriod chart
    sameAction.chartBridge.basePoint
    (h11CoreDirection period hPeriod configuration data analysis chart sameAction
      first)
    (h11CoreDirection period hPeriod configuration data analysis chart sameAction
      second)

/-- Exact blockwise decomposition after pullback to the corrected core. -/
theorem diagonalExtendedBulkH11PhysicalHessian_eq_seven
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
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis) :
    diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period hPeriod
        configuration data analysis chart sameAction.chartBridge first second =
      ((((((diagonalExtendedBulkH11InteractionHessianOnCore period hPeriod
          configuration data analysis chart sameAction first second +
        diagonalExtendedBulkH11GHYHessianOnCore period hPeriod configuration
          data analysis chart sameAction first second) +
        diagonalExtendedBulkH11EinsteinHilbertPlusHessianOnCore period hPeriod
          configuration data analysis chart sameAction first second) +
        diagonalExtendedBulkH11EinsteinHilbertMinusHessianOnCore period hPeriod
          configuration data analysis chart sameAction first second) +
        diagonalExtendedBulkH11MaxwellPlusHessianOnCore period hPeriod
          configuration data analysis chart sameAction first second) +
        diagonalExtendedBulkH11MaxwellMinusHessianOnCore period hPeriod
          configuration data analysis chart sameAction first second) +
        diagonalExtendedBulkH11FiniteBVHessianOnCore period hPeriod
          configuration data analysis chart sameAction first second) := by
  unfold diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore
    diagonalExtendedBulkH11InteractionHessianOnCore
    diagonalExtendedBulkH11GHYHessianOnCore
    diagonalExtendedBulkH11EinsteinHilbertPlusHessianOnCore
    diagonalExtendedBulkH11EinsteinHilbertMinusHessianOnCore
    diagonalExtendedBulkH11MaxwellPlusHessianOnCore
    diagonalExtendedBulkH11MaxwellMinusHessianOnCore
    diagonalExtendedBulkH11FiniteBVHessianOnCore
    h11CoreDirection
  rw [globalCandidateAH11LocalPhysicalHessian_eq_seven period hPeriod chart
    sameAction.chartBridge.basePoint sameAction.chartBridge.basePoint_mem]
  rfl

/-! ## Seven small extension contracts and their canonical sum -/

structure GlobalCandidateAPhysicalBlockCommonDomainExtension4D
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (target : GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
      analysis → GlobalCandidateADiagonalExtendedBulkSmoothCore period hPeriod
        analysis → Real) where
  form :
    SevenBlockHilbert period hPeriod configuration data analysis →L[Real]
      SevenBlockHilbert period hPeriod configuration data analysis →L[Real] Real
  symmetric : ∀ first second, form first second = form second first
  smooth_agreement : ∀ first second,
    form
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis first)
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis second) =
      target first second

structure GlobalCandidateASevenPhysicalBlockExtensions4D
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
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart) where
  interaction : GlobalCandidateAPhysicalBlockCommonDomainExtension4D period
    hPeriod (measure := measure) configuration data analysis
      (diagonalExtendedBulkH11InteractionHessianOnCore period hPeriod
        configuration data analysis chart sameAction)
  ghy : GlobalCandidateAPhysicalBlockCommonDomainExtension4D period hPeriod
    (measure := measure) configuration data analysis
      (diagonalExtendedBulkH11GHYHessianOnCore period hPeriod configuration data
        analysis chart sameAction)
  einsteinHilbertPlus :
    GlobalCandidateAPhysicalBlockCommonDomainExtension4D period hPeriod
      (measure := measure) configuration data analysis
      (diagonalExtendedBulkH11EinsteinHilbertPlusHessianOnCore period hPeriod
        configuration data analysis chart sameAction)
  einsteinHilbertMinus :
    GlobalCandidateAPhysicalBlockCommonDomainExtension4D period hPeriod
      (measure := measure) configuration data analysis
      (diagonalExtendedBulkH11EinsteinHilbertMinusHessianOnCore period hPeriod
        configuration data analysis chart sameAction)
  maxwellPlus : GlobalCandidateAPhysicalBlockCommonDomainExtension4D period
    hPeriod (measure := measure) configuration data analysis
      (diagonalExtendedBulkH11MaxwellPlusHessianOnCore period hPeriod
        configuration data analysis chart sameAction)
  maxwellMinus : GlobalCandidateAPhysicalBlockCommonDomainExtension4D period
    hPeriod (measure := measure) configuration data analysis
      (diagonalExtendedBulkH11MaxwellMinusHessianOnCore period hPeriod
        configuration data analysis chart sameAction)
  finiteBV : GlobalCandidateAPhysicalBlockCommonDomainExtension4D period hPeriod
    (measure := measure) configuration data analysis
      (diagonalExtendedBulkH11FiniteBVHessianOnCore period hPeriod configuration
        data analysis chart sameAction)

private def GlobalCandidateASevenPhysicalBlockExtensions4D.sumForm
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure}
    {sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart}
    (blocks : GlobalCandidateASevenPhysicalBlockExtensions4D period hPeriod
      (measure := measure) configuration data analysis chart sameAction) :=
  ((((((blocks.interaction.form + blocks.ghy.form) +
    blocks.einsteinHilbertPlus.form) + blocks.einsteinHilbertMinus.form) +
    blocks.maxwellPlus.form) + blocks.maxwellMinus.form) + blocks.finiteBV.form)

/-- Seven independently proved bounded extensions canonically construct the
single H11 extension expected by the augmented-domain gate. -/
def globalCandidateASevenPhysicalCommonDomainExtension_of_blocks
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
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (blocks : GlobalCandidateASevenPhysicalBlockExtensions4D period hPeriod
      (measure := measure) configuration data analysis chart sameAction) :
    GlobalCandidateASevenPhysicalCommonDomainExtension4D period hPeriod
      configuration data analysis chart sameAction where
  form := blocks.sumForm period hPeriod (measure := measure)
  symmetric := by
    intro first second
    unfold GlobalCandidateASevenPhysicalBlockExtensions4D.sumForm
    simp only [ContinuousLinearMap.add_apply]
    rw [blocks.interaction.symmetric first second,
      blocks.ghy.symmetric first second,
      blocks.einsteinHilbertPlus.symmetric first second,
      blocks.einsteinHilbertMinus.symmetric first second,
      blocks.maxwellPlus.symmetric first second,
      blocks.maxwellMinus.symmetric first second,
      blocks.finiteBV.symmetric first second]
  smooth_agreement := by
    intro first second
    unfold GlobalCandidateASevenPhysicalBlockExtensions4D.sumForm
    simp only [ContinuousLinearMap.add_apply]
    rw [blocks.interaction.smooth_agreement first second,
      blocks.ghy.smooth_agreement first second,
      blocks.einsteinHilbertPlus.smooth_agreement first second,
      blocks.einsteinHilbertMinus.smooth_agreement first second,
      blocks.maxwellPlus.smooth_agreement first second,
      blocks.maxwellMinus.smooth_agreement first second,
      blocks.finiteBV.smooth_agreement first second]
    exact (diagonalExtendedBulkH11PhysicalHessian_eq_seven period hPeriod
      configuration data analysis chart sameAction first second).symm

/-- Direct H11 gate from seven blockwise analytic extensions. -/
theorem global_candidateA_h11_common_augmented_domain_gate_of_blocks
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
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (blocks : GlobalCandidateASevenPhysicalBlockExtensions4D period hPeriod
      (measure := measure) configuration data analysis chart sameAction) :
    GlobalCandidateACommonAugmentedAnalyticDomainCertificate4D period hPeriod
      configuration data analysis chart sameAction
        (globalCandidateASevenPhysicalCommonDomainExtension_of_blocks period
          hPeriod configuration data analysis chart sameAction blocks) :=
  global_candidateA_h11_common_augmented_domain_gate period hPeriod
    configuration data analysis chart sameAction
      (globalCandidateASevenPhysicalCommonDomainExtension_of_blocks period
        hPeriod configuration data analysis chart sameAction blocks)

end
end P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockExtensions4D
end JanusFormal
