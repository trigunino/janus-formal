import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateACommonAnalyticDomainClosure4D

/-!
# H11 common augmented analytic domain

The diagonal BRST--SpinC--LL graph already has one complete real Hilbert space,
a dense injective smooth core, a genuine quadratic action and a bounded
self-adjoint Riesz representative.  H13 identifies the true gauge-fixed local
Hessian with that graph Hessian plus the seven physical action blocks.

This file installs those seven blocks on the *same* completed Hilbert space.
The only analytic input is a bounded symmetric extension whose values on the
existing dense smooth core are exactly the seven-block local action Hessian.
No second completion, independent physical action or D10 coordinate is added.

The sum of the old graph Riesz operator and the seven-block Riesz operator is
then bounded, self-adjoint and closed.  Its quadratic action is `C²`, and its
genuine second Frechet derivative agrees on the dense smooth core with the
H13 gauge-fixed covariant Hessian.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAnalyticDomainClosure4D

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

private def CommonAugmentedHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateADiagonalExtendedBulkL2Hilbert period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

local instance (priority := 30000) commonAugmentedNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) commonAugmentedInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) commonAugmentedNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  (commonAugmentedInnerProductSpace period hPeriod configuration data
    analysis).toNormedSpace

local instance (priority := 30000) commonAugmentedModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  (commonAugmentedNormedSpace period hPeriod configuration data
    analysis).toModule

local instance (priority := 30000) commonAugmentedCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (CommonAugmentedHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

private def diagonalHessianCommon
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
      CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
        Real := by
  unfold CommonAugmentedHilbert
  exact diagonalExtendedBulkL2Hessian period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

private def diagonalRieszCommon
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
      CommonAugmentedHilbert period hPeriod configuration data analysis := by
  unfold CommonAugmentedHilbert
  exact diagonalExtendedBulkL2RieszOperator period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis

private theorem diagonalRieszCommon_pairing
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (first second : CommonAugmentedHilbert period hPeriod configuration data
      analysis) :
    inner Real (diagonalRieszCommon period hPeriod configuration data analysis first)
        second =
      diagonalHessianCommon period hPeriod configuration data analysis first second := by
  unfold diagonalRieszCommon diagonalHessianCommon CommonAugmentedHilbert
  exact diagonalExtendedBulkL2RieszOperator_pairing period hPeriod
    (globalCandidateAMetricBySector period hPeriod data)
    couplings.matterMassSquared data analysis first second

/-! ## The seven physical blocks on the unchanged completion -/

/-- A bounded symmetric extension of the seven genuine physical action blocks
to the already existing diagonal graph Hilbert space.  The dense-core equality
prevents this interface from storing an unrelated bilinear form. -/
structure GlobalCandidateASevenPhysicalCommonDomainExtension4D
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
  form :
    CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
      CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
        Real
  symmetric : ∀ first second, form first second = form second first
  smooth_agreement :
    ∀ first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
        period hPeriod analysis,
      form
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis first)
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis second) =
        diagonalExtendedBulkMinimalPhysicalLocalActionHessianOnCore period hPeriod
          configuration data analysis chart sameAction.chartBridge first second

/-- Riesz representative of the bounded seven-block extension. -/
def globalCandidateASevenPhysicalCommonRieszOperator
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction) :
    CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
      CommonAugmentedHilbert period hPeriod configuration data analysis :=
  @InnerProductSpace.continuousLinearMapOfBilin
    Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis)
    inferInstance inferInstance
    (commonAugmentedInnerProductSpace period hPeriod configuration data analysis)
    (commonAugmentedCompleteSpace period hPeriod configuration data analysis)
    physical.form

/-- The preceding Riesz representative pairs to exactly the supplied seven
physical blocks. -/
theorem globalCandidateASevenPhysicalCommonRieszOperator_pairing
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (first second : CommonAugmentedHilbert period hPeriod configuration data
      analysis) :
    inner Real
        (globalCandidateASevenPhysicalCommonRieszOperator period hPeriod
          configuration data analysis chart sameAction physical first)
        second = physical.form first second := by
  exact @InnerProductSpace.continuousLinearMapOfBilin_apply
    Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis)
    inferInstance inferInstance
    (commonAugmentedInnerProductSpace period hPeriod configuration data analysis)
    (commonAugmentedCompleteSpace period hPeriod configuration data analysis)
    physical.form first second

/-! ## Augmented same-action Hessian on the common Hilbert space -/

/-- Sum of the existing BRST--SpinC--LL graph Hessian and all seven physical
blocks, on one unchanged Hilbert completion. -/
def globalCandidateACommonAugmentedHessian
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction) :
    CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
      CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
        Real :=
  diagonalHessianCommon period hPeriod configuration data analysis +
    physical.form

/-- Symmetry of the full augmented Hessian. -/
theorem globalCandidateACommonAugmentedHessian_comm
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (first second : CommonAugmentedHilbert period hPeriod configuration data
      analysis) :
    globalCandidateACommonAugmentedHessian period hPeriod configuration data
        analysis chart sameAction physical first second =
      globalCandidateACommonAugmentedHessian period hPeriod configuration data
        analysis chart sameAction physical second first := by
  unfold globalCandidateACommonAugmentedHessian diagonalHessianCommon
  simp only [ContinuousLinearMap.add_apply]
  exact congrArg₂ (· + ·)
    (diagonalExtendedBulkL2Hessian_comm period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis first second)
    (physical.symmetric first second)

/-- Bounded Riesz representative of the complete augmented Hessian. -/
def globalCandidateACommonAugmentedRieszOperator
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction) :
    CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
      CommonAugmentedHilbert period hPeriod configuration data analysis :=
  diagonalRieszCommon period hPeriod configuration data analysis +
    globalCandidateASevenPhysicalCommonRieszOperator period hPeriod
      configuration data analysis chart sameAction physical

/-- The augmented Riesz representative pairs to the augmented Hessian. -/
theorem globalCandidateACommonAugmentedRieszOperator_pairing
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (first second : CommonAugmentedHilbert period hPeriod configuration data
      analysis) :
    inner Real
        (globalCandidateACommonAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical first)
        second =
      globalCandidateACommonAugmentedHessian period hPeriod configuration data
        analysis chart sameAction physical first second := by
  calc
    _ = inner Real
          (diagonalRieszCommon period hPeriod configuration data analysis first)
          second +
        inner Real
          (globalCandidateASevenPhysicalCommonRieszOperator period hPeriod
            configuration data analysis chart sameAction physical first)
          second := by
      rw [globalCandidateACommonAugmentedRieszOperator,
        ContinuousLinearMap.add_apply, inner_add_left]
    _ = diagonalHessianCommon period hPeriod configuration data analysis
          first second +
        physical.form first second := by
      rw [diagonalRieszCommon_pairing period hPeriod configuration data analysis
          first second,
        globalCandidateASevenPhysicalCommonRieszOperator_pairing period hPeriod
          configuration data analysis chart sameAction physical first second]
    _ = _ := rfl

/-- Symmetry criterion for the complete augmented Riesz representative. -/
theorem globalCandidateACommonAugmentedRieszOperator_isSymmetric
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (first second : CommonAugmentedHilbert period hPeriod configuration data
      analysis) :
    inner Real
        (globalCandidateACommonAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical first)
        second =
      inner Real first
        (globalCandidateACommonAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical second) := by
  calc
    _ = globalCandidateACommonAugmentedHessian period hPeriod configuration data
          analysis chart sameAction physical first second :=
      globalCandidateACommonAugmentedRieszOperator_pairing period hPeriod
        configuration data analysis chart sameAction physical first second
    _ = globalCandidateACommonAugmentedHessian period hPeriod configuration data
          analysis chart sameAction physical second first :=
      globalCandidateACommonAugmentedHessian_comm period hPeriod configuration
        data analysis chart sameAction physical first second
    _ = inner Real
          (globalCandidateACommonAugmentedRieszOperator period hPeriod
            configuration data analysis chart sameAction physical second)
          first :=
      (globalCandidateACommonAugmentedRieszOperator_pairing period hPeriod
        configuration data analysis chart sameAction physical second first).symm
    _ = _ := real_inner_comm _ _

/-- The complete augmented representative is self-adjoint on the unchanged
Hilbert space. -/
theorem globalCandidateACommonAugmentedRieszOperator_isSelfAdjoint
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction) :
    @IsSelfAdjoint
      (CommonAugmentedHilbert period hPeriod configuration data analysis →L[Real]
        CommonAugmentedHilbert period hPeriod configuration data analysis)
      (@ContinuousLinearMap.instStarId
        Real
        (CommonAugmentedHilbert period hPeriod configuration data analysis)
        inferInstance inferInstance
        (commonAugmentedInnerProductSpace period hPeriod configuration data
          analysis)
        (commonAugmentedCompleteSpace period hPeriod configuration data analysis))
      (globalCandidateACommonAugmentedRieszOperator period hPeriod configuration
        data analysis chart sameAction physical) := by
  apply (@ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric
    Real
    (CommonAugmentedHilbert period hPeriod configuration data analysis)
    inferInstance inferInstance
    (commonAugmentedInnerProductSpace period hPeriod configuration data analysis)
    (commonAugmentedCompleteSpace period hPeriod configuration data analysis)
    (globalCandidateACommonAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical)).2
  exact globalCandidateACommonAugmentedRieszOperator_isSymmetric period hPeriod
    configuration data analysis chart sameAction physical

/-- The graph of the bounded augmented representative is closed. -/
theorem globalCandidateACommonAugmentedRieszOperator_graph_isClosed
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction) :
    IsClosed
      ((globalCandidateACommonAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical).toLinearMap.graph :
        Set
          (CommonAugmentedHilbert period hPeriod configuration data analysis ×
            CommonAugmentedHilbert period hPeriod configuration data analysis)) := by
  rw [show
      ((globalCandidateACommonAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical).toLinearMap.graph :
          Set
            (CommonAugmentedHilbert period hPeriod configuration data analysis ×
              CommonAugmentedHilbert period hPeriod configuration data analysis)) =
        {pair | pair.2 =
          globalCandidateACommonAugmentedRieszOperator period hPeriod
            configuration data analysis chart sameAction physical pair.1} by
      ext pair
      rfl]
  exact isClosed_eq continuous_snd
    ((globalCandidateACommonAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical).continuous.comp continuous_fst)

/-! ## Genuine quadratic action and dense-core agreement -/

/-- Quadratic action whose Hessian is the complete augmented form. -/
def globalCandidateACommonAugmentedAction
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    Real :=
  (1 / 2 : Real) *
    globalCandidateACommonAugmentedHessian period hPeriod configuration data
      analysis chart sameAction physical state state

private theorem symmetricQuadratic_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (bilinear : E →L[Real] E →L[Real] Real)
    (hSymmetric : ∀ first second,
      bilinear first second = bilinear second first)
    (point : E) :
    HasFDerivAt (fun state => (1 / 2 : Real) * bilinear state state)
      (bilinear point) point := by
  have hDiagonal :=
    (bilinear.hasFDerivAt (x := point)).clm_apply
      (hasFDerivAt_id (𝕜 := Real) point)
  have hHalf := hDiagonal.const_mul (1 / 2 : Real)
  apply hHalf.congr_fderiv
  ext direction
  change (1 / 2 : Real) *
      (bilinear point direction + bilinear direction point) =
    bilinear point direction
  rw [hSymmetric direction point]
  ring

private theorem symmetricQuadratic_contDiff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (bilinear : E →L[Real] E →L[Real] Real) :
    ContDiff Real ⊤ (fun state => (1 / 2 : Real) * bilinear state state) :=
  contDiff_const.mul (bilinear.contDiff.clm_apply contDiff_id)

theorem globalCandidateACommonAugmentedAction_hasFDerivAt
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    HasFDerivAt
      (globalCandidateACommonAugmentedAction period hPeriod configuration data
        analysis chart sameAction physical)
      (globalCandidateACommonAugmentedHessian period hPeriod configuration data
        analysis chart sameAction physical state) state := by
  exact symmetricQuadratic_hasFDerivAt
    (globalCandidateACommonAugmentedHessian period hPeriod configuration data
      analysis chart sameAction physical)
    (globalCandidateACommonAugmentedHessian_comm period hPeriod configuration
      data analysis chart sameAction physical) state

theorem globalCandidateACommonAugmentedAction_fderiv
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (state : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    fderiv Real
        (globalCandidateACommonAugmentedAction period hPeriod configuration data
          analysis chart sameAction physical) state =
      globalCandidateACommonAugmentedHessian period hPeriod configuration data
        analysis chart sameAction physical state :=
  (globalCandidateACommonAugmentedAction_hasFDerivAt period hPeriod
    configuration data analysis chart sameAction physical state).fderiv

theorem globalCandidateACommonAugmentedAction_second_fderiv
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (base : CommonAugmentedHilbert period hPeriod configuration data analysis) :
    fderiv Real
        (fun state => fderiv Real
          (globalCandidateACommonAugmentedAction period hPeriod configuration
            data analysis chart sameAction physical) state)
        base =
      globalCandidateACommonAugmentedHessian period hPeriod configuration data
        analysis chart sameAction physical := by
  rw [show
      (fun state => fderiv Real
        (globalCandidateACommonAugmentedAction period hPeriod configuration data
          analysis chart sameAction physical) state) =
      fun state => globalCandidateACommonAugmentedHessian period hPeriod
        configuration data analysis chart sameAction physical state from by
    funext state
    exact globalCandidateACommonAugmentedAction_fderiv period hPeriod
      configuration data analysis chart sameAction physical state]
  exact ContinuousLinearMap.fderiv
    (globalCandidateACommonAugmentedHessian period hPeriod configuration data
      analysis chart sameAction physical)

theorem globalCandidateACommonAugmentedAction_contDiff_two
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction) :
    ContDiff Real 2
      (globalCandidateACommonAugmentedAction period hPeriod configuration data
        analysis chart sameAction physical) :=
  (symmetricQuadratic_contDiff
    (globalCandidateACommonAugmentedHessian period hPeriod configuration data
      analysis chart sameAction physical)).of_le (by simp)

/-- The old graph Hessian transported to the L2 chart agrees with its original
smooth-core expression. -/
theorem diagonalExtendedBulkL2Hessian_smooth_eq_graphOnCore
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    diagonalExtendedBulkL2Hessian period hPeriod
        (globalCandidateAMetricBySector period hPeriod data)
        couplings.matterMassSquared data analysis
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis first)
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis second) =
      diagonalExtendedBulkGraphHessianOnCore period hPeriod configuration data
        analysis first second := by
  unfold diagonalExtendedBulkGraphHessianOnCore
  rw [diagonalExtendedBulkL2Hessian_apply]
  simp [diagonalExtendedBulkL2SmoothEmbedding]

/-- On the dense smooth core, the augmented Hilbert-space Hessian is exactly
the true H13 gauge-fixed covariant Hessian. -/
theorem globalCandidateACommonAugmentedHessian_smooth_eq_gaugeFixed
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    globalCandidateACommonAugmentedHessian period hPeriod configuration data
        analysis chart sameAction physical
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis first)
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis second) =
      diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore period
        hPeriod configuration data analysis chart sameAction.chartBridge first
          second := by
  have hDiagonal :
      diagonalHessianCommon period hPeriod configuration data analysis
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis first)
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis second) =
        diagonalExtendedBulkGraphHessianOnCore period hPeriod configuration data
          analysis first second := by
    unfold diagonalHessianCommon CommonAugmentedHilbert
    exact diagonalExtendedBulkL2Hessian_smooth_eq_graphOnCore period hPeriod
      configuration data analysis first second
  unfold globalCandidateACommonAugmentedHessian
  simp only [ContinuousLinearMap.add_apply]
  rw [hDiagonal, physical.smooth_agreement first second]
  exact
    (diagonalExtendedBulkH13GaugeFixed_eq_graph_add_sevenPhysical period hPeriod
      configuration data analysis chart sameAction first second).symm

/-- The genuine second derivative of the common quadratic action agrees with
the local gauge-fixed Candidate-A Hessian on the dense smooth core. -/
theorem globalCandidateACommonAugmentedAction_second_fderiv_smooth
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction)
    (base : CommonAugmentedHilbert period hPeriod configuration data analysis)
    (first second : GlobalCandidateADiagonalExtendedBulkSmoothCore
      period hPeriod analysis) :
    (fderiv Real
        (fun state => fderiv Real
          (globalCandidateACommonAugmentedAction period hPeriod configuration
            data analysis chart sameAction physical) state)
        base)
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis first)
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis second) =
      diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore period
        hPeriod configuration data analysis chart sameAction.chartBridge first
          second := by
  rw [globalCandidateACommonAugmentedAction_second_fderiv period hPeriod
    configuration data analysis chart sameAction physical base]
  exact globalCandidateACommonAugmentedHessian_smooth_eq_gaugeFixed period
    hPeriod configuration data analysis chart sameAction physical first second

/-! ## H11 certificate -/

/-- Auditable H11 certificate on the unique pre-existing graph completion. -/
structure GlobalCandidateACommonAugmentedAnalyticDomainCertificate4D
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction) : Prop where
  physical_domain : GlobalPhysicalAnalysisCertificate period hPeriod analysis
  smooth_core_dense : DenseRange
    (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis)
  smooth_core_injective : Function.Injective
    (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
      (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis)
  action_contDiff_two : ContDiff Real 2
    (globalCandidateACommonAugmentedAction period hPeriod configuration data
      analysis chart sameAction physical)
  riesz_graph_closed : IsClosed
    ((globalCandidateACommonAugmentedRieszOperator period hPeriod configuration
        data analysis chart sameAction physical).toLinearMap.graph :
      Set
        (CommonAugmentedHilbert period hPeriod configuration data analysis ×
          CommonAugmentedHilbert period hPeriod configuration data analysis))
  riesz_symmetric : ∀ first second,
    inner Real
        (globalCandidateACommonAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical first)
        second =
      inner Real first
        (globalCandidateACommonAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical second)
  sameAction_on_smooth_core : ∀ base first second,
    (fderiv Real
        (fun state => fderiv Real
          (globalCandidateACommonAugmentedAction period hPeriod configuration
            data analysis chart sameAction physical) state)
        base)
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis first)
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis second) =
      diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore period
        hPeriod configuration data analysis chart sameAction.chartBridge first
          second

/-- Canonical H11 gate from the bounded seven-block extension. -/
theorem global_candidateA_h11_common_augmented_domain_gate
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
    (physical : GlobalCandidateASevenPhysicalCommonDomainExtension4D period
      hPeriod configuration data analysis chart sameAction) :
    GlobalCandidateACommonAugmentedAnalyticDomainCertificate4D period hPeriod
      configuration data analysis chart sameAction physical := by
  refine
    { physical_domain :=
        globalCandidateACommonAnalyticDomain_physical_certificate period hPeriod
          analysis
      smooth_core_dense :=
        diagonalExtendedBulkL2SmoothEmbedding_denseRange period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis
      smooth_core_injective :=
        diagonalExtendedBulkL2SmoothEmbedding_injective period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis
      action_contDiff_two :=
        globalCandidateACommonAugmentedAction_contDiff_two period hPeriod
          configuration data analysis chart sameAction physical
      riesz_graph_closed :=
        globalCandidateACommonAugmentedRieszOperator_graph_isClosed period
          hPeriod configuration data analysis chart sameAction physical
      riesz_symmetric :=
        globalCandidateACommonAugmentedRieszOperator_isSymmetric period hPeriod
          configuration data analysis chart sameAction physical
      sameAction_on_smooth_core := ?_ }
  intro base first second
  exact globalCandidateACommonAugmentedAction_second_fderiv_smooth period
    hPeriod configuration data analysis chart sameAction physical base first
      second

end
end P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
end JanusFormal
