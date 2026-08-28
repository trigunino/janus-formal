import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D

/-!
# H12 faithful augmented Fredholm sum

H11 constructs the complete gauge-fixed Candidate-A Hessian on the faithful
D10-free diagonal Hilbert space: the old BRST--SpinC--LL graph operator plus
the seven retained physical action blocks.  The operator is bounded,
self-adjoint and closed, and its pairing on the dense smooth core is exactly
the H13 local covariant Hessian.

For a bounded self-adjoint operator, Fredholmness reduces to the two genuine
analytic estimates: closed range and finite-dimensional kernel.  This file
keeps exactly those estimates visible.  It derives finite cokernel and index
zero rather than storing a Fredholm hypothesis, while retaining the typed
nine-species nonminimal core and the stationary LL identification.

No `Fin 9` replacement, new completion, physical block, field, action or
Fredholm axiom is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1200000
set_option maxHeartbeats 2400000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalFullLLOnShellFredholmReduction4D
open P0EFTJanusBoundedSelfAdjointFredholmReduction4D
open P0EFTJanusMappingTorusGlobalLLVariation4D

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

local instance (priority := 30000) augmentedFredholmNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) augmentedFredholmInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) augmentedFredholmNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) augmentedFredholmModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) augmentedFredholmCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
        data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

/-! ## The actual faithful augmented operator -/

/-- Public H12 name for the H11 augmented Riesz representative on the faithful
typed Hilbert completion. -/
def globalCandidateAFaithfulAugmentedRieszOperator
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
    GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
        analysis →L[Real]
      GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
        analysis :=
  globalCandidateACommonAugmentedRieszOperator period hPeriod configuration data
    analysis chart sameAction physical

/-- On the dense typed smooth core, the faithful augmented pairing is exactly
the true local gauge-fixed Candidate-A Hessian. -/
theorem globalCandidateAFaithfulAugmentedRieszOperator_smooth_pairing
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
    inner Real
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis first))
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis second) =
      diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore period
        hPeriod configuration data analysis chart sameAction.chartBridge first
          second := by
  calc
    _ = globalCandidateACommonAugmentedHessian period hPeriod configuration data
          analysis chart sameAction physical
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis first)
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis second) :=
      globalCandidateACommonAugmentedRieszOperator_pairing period hPeriod
        configuration data analysis chart sameAction physical _ _
    _ = _ :=
      globalCandidateACommonAugmentedHessian_smooth_eq_gaugeFixed period hPeriod
        configuration data analysis chart sameAction physical first second

/-- The faithful augmented operator is self-adjoint before any Fredholm
estimate is imposed. -/
def globalCandidateAFaithfulAugmentedRieszOperator_isSelfAdjoint
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
      hPeriod configuration data analysis chart sameAction) :=
  globalCandidateACommonAugmentedRieszOperator_isSelfAdjoint period hPeriod
    configuration data analysis chart sameAction physical

/-! ## The two genuine Fredholm estimates -/

/-- Exact analytic input still needed for the total augmented operator.
`range_closed` and `kernel_finite` are the two estimates from which Fredholmness
and index zero follow.  LL stationarity records the terminal elliptic stratum;
it is not used as a substitute for either estimate. -/
structure GlobalCandidateAFaithfulAugmentedFredholmEstimates4D
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
  ll_stationary : ∀ point,
    LLStationaryAt period hPeriod
      (data.boundary.llFields period hPeriod) point
  range_closed : IsClosed
    ((globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
        configuration data analysis chart sameAction physical).range :
      Set
        (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
          data analysis))
  kernel_finite : FiniteDimensional Real
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
      configuration data analysis chart sameAction physical).ker

/-- The terminal stationary LL quotient is the identity factor already used by
the historical SpinC--LL Fredholm product. -/
def globalCandidateAFaithfulAugmented_actualLL_eq_identity_of_stationary
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
    (estimates : GlobalCandidateAFaithfulAugmentedFredholmEstimates4D period
      hPeriod configuration data analysis chart sameAction physical) :=
  globalCandidateAMatterLL_actualLL_eq_identity_of_stationary period hPeriod
    data analysis estimates.ll_stationary

/-- Closed range and finite kernel imply the complete Fredholm package for the
actual augmented Candidate-A operator. -/
theorem globalCandidateAFaithfulAugmentedRieszOperator_fredholm
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
    (estimates : GlobalCandidateAFaithfulAugmentedFredholmEstimates4D period
      hPeriod configuration data analysis chart sameAction physical) :
    IsClosed
        ((globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical).range :
          Set
            (GlobalCandidateAFaithfulSameActionHilbert period hPeriod
              configuration data analysis)) ∧
      FiniteDimensional Real
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical).ker ∧
      FiniteDimensional Real
        ((GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
            data analysis) ⧸
          (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
            configuration data analysis chart sameAction physical).range) :=
by
  exact @boundedSelfAdjoint_fredholm_of_closedRange_finiteKernel
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedAddCommGroup period hPeriod configuration data analysis)
    (augmentedFredholmInnerProductSpace period hPeriod configuration data analysis)
    (augmentedFredholmCompleteSpace period hPeriod configuration data analysis)
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical)
    (globalCandidateAFaithfulAugmentedRieszOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
    estimates.range_closed estimates.kernel_finite

/-- Self-adjointness forces equality of kernel and cokernel dimensions, hence
the full faithful augmented index is zero. -/
theorem globalCandidateAFaithfulAugmentedRieszOperator_index_zero
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
    (estimates : GlobalCandidateAFaithfulAugmentedFredholmEstimates4D period
      hPeriod configuration data analysis chart sameAction physical) :
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical).toLinearMap.index = 0 :=
by
  exact @boundedSelfAdjoint_index_zero
    (GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
      analysis)
    (augmentedFredholmNormedAddCommGroup period hPeriod configuration data analysis)
    (augmentedFredholmInnerProductSpace period hPeriod configuration data analysis)
    (augmentedFredholmCompleteSpace period hPeriod configuration data analysis)
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical)
    (globalCandidateAFaithfulAugmentedRieszOperator_isSelfAdjoint period hPeriod
      configuration data analysis chart sameAction physical)
    estimates.range_closed estimates.kernel_finite

/-! ## H12 certificate -/

/-- Auditable faithful total Fredholm certificate. -/
structure GlobalCandidateAFaithfulAugmentedFredholmCertificate4D
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
    (estimates : GlobalCandidateAFaithfulAugmentedFredholmEstimates4D period
      hPeriod configuration data analysis chart sameAction physical) : Prop where
  typed_core_injective : Function.Injective
    (diagonalExtendedBulkGraphTypedCoreLinearMap period hPeriod configuration
      data analysis)
  common_domain : GlobalCandidateACommonAugmentedAnalyticDomainCertificate4D
    period hPeriod configuration data analysis chart sameAction physical
  ll_stationary : ∀ point,
    LLStationaryAt period hPeriod
      (data.boundary.llFields period hPeriod) point
  fredholm :
    IsClosed
        ((globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical).range :
          Set
            (GlobalCandidateAFaithfulSameActionHilbert period hPeriod
              configuration data analysis)) ∧
      FiniteDimensional Real
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical).ker ∧
      FiniteDimensional Real
        ((GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration
            data analysis) ⧸
          (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
            configuration data analysis chart sameAction physical).range)
  index_zero :
    (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod configuration
      data analysis chart sameAction physical).toLinearMap.index = 0
  sameAction_on_typed_core : ∀ first second,
    inner Real
        (globalCandidateAFaithfulAugmentedRieszOperator period hPeriod
          configuration data analysis chart sameAction physical
          (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
            (globalCandidateAMetricBySector period hPeriod data)
            couplings.matterMassSquared data analysis first))
        (diagonalExtendedBulkL2SmoothEmbedding period hPeriod
          (globalCandidateAMetricBySector period hPeriod data)
          couplings.matterMassSquared data analysis second) =
      diagonalExtendedBulkMinimalPhysicalLocalGaugeFixedHessianOnCore period
        hPeriod configuration data analysis chart sameAction.chartBridge first
          second

/-- Canonical H12 gate from the two explicit analytic estimates. -/
theorem global_candidateA_h12_faithful_augmented_fredholm_gate
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
    (estimates : GlobalCandidateAFaithfulAugmentedFredholmEstimates4D period
      hPeriod configuration data analysis chart sameAction physical) :
    GlobalCandidateAFaithfulAugmentedFredholmCertificate4D period hPeriod
      configuration data analysis chart sameAction physical estimates := by
  refine
    { typed_core_injective :=
        globalCandidateAFaithfulFredholmSum_typedCore_injective period hPeriod
          configuration data analysis
      common_domain :=
        global_candidateA_h11_common_augmented_domain_gate period hPeriod
          configuration data analysis chart sameAction physical
      ll_stationary := estimates.ll_stationary
      fredholm :=
        globalCandidateAFaithfulAugmentedRieszOperator_fredholm period hPeriod
          configuration data analysis chart sameAction physical estimates
      index_zero :=
        globalCandidateAFaithfulAugmentedRieszOperator_index_zero period hPeriod
          configuration data analysis chart sameAction physical estimates
      sameAction_on_typed_core := ?_ }
  intro first second
  exact globalCandidateAFaithfulAugmentedRieszOperator_smooth_pairing period
    hPeriod configuration data analysis chart sameAction physical first second

end
end P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
end JanusFormal
