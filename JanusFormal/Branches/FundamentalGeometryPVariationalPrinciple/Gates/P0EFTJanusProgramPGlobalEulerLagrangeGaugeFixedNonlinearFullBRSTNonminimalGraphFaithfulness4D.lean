import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTLLThreeSlotAugmentedGraphFaithfulness4D

/-!
# Faithfulness of the remaining full-BRST nonminimal graphs

The smooth pure ghost graph of the paired Abelian sector and the three smooth
pure nonminimal graphs of the diffeomorphism sector are injective.  Together
with their existing dense-range results, these are faithful graph coordinates.
No local PDE or Fredholm property is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNonminimalGraphFaithfulness4D

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
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalEulerLagrangePhysicalSectorSplit4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalComponentEuler4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTAbelianGhostGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismGhostGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismAntighostGraphRieszResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTDiffeomorphismNakanishiLautrupGraphRieszResidual4D

@[implicit_reducible]
local instance (priority := 11000) alignedRealNontriviallyNormedFieldNonminimalFaithfulness :
    NontriviallyNormedField Real :=
  @NontriviallyNormedField.ofNormNeOne Real Real.normedField
    ⟨2, by norm_num, by norm_num⟩

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

theorem globalPairedAbelianPureGhostStateLinearMap_injective :
    Function.Injective
      (globalPairedAbelianPureGhostStateLinearMap period hPeriod) := by
  intro first second hEqual
  funext sector
  simpa [globalPairedAbelianPureGhostStateLinearMap] using
    congrArg
      (fun state : GlobalPairedAbelianBRSTState period hPeriod =>
        (state.nonminimal sector).ghost) hEqual

theorem globalPairedAbelianPureGhostGraphLinearMap_injective
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (globalPairedAbelianPureGhostGraphLinearMap period hPeriod metric) := by
  intro first second hEqual
  apply globalPairedAbelianPureGhostStateLinearMap_injective period hPeriod
  apply globalPairedAbelianOffShellSmoothEmbedding_injective period hPeriod
    metric
  simpa [globalPairedAbelianPureGhostGraphLinearMap] using hEqual

theorem globalPairedAbelianPureGhostGraphEmbedding_injective
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (globalPairedAbelianPureGhostGraphEmbedding period hPeriod metric) := by
  intro first second hEqual
  apply globalPairedAbelianPureGhostGraphLinearMap_injective period hPeriod
    metric
  simpa [globalPairedAbelianPureGhostGraphEmbedding] using
    congrArg Subtype.val hEqual

theorem globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalOnlyStateLinearMap_injective :
    Function.Injective
      (globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalOnlyStateLinearMap
        period hPeriod) := by
  intro first second hEqual
  simpa [globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalOnlyStateLinearMap]
    using congrArg
      (fun state : GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod =>
        state.nonminimal) hEqual

theorem globalDiffeomorphismPureGhostNonminimalLinearMap_injective :
    Function.Injective
      (globalDiffeomorphismPureGhostNonminimalLinearMap period hPeriod) := by
  intro first second hEqual
  simpa [globalDiffeomorphismPureGhostNonminimalLinearMap,
    globalDiffeomorphismNonminimalFieldsLinearEquiv,
    productFirstInclusion] using congrArg
      (fun fields : GlobalDiffeomorphismNonminimalFields period hPeriod =>
        fields.ghost) hEqual

theorem globalDiffeomorphismPureAntighostNonminimalLinearMap_injective :
    Function.Injective
      (globalDiffeomorphismPureAntighostNonminimalLinearMap period hPeriod) := by
  intro first second hEqual
  simpa [globalDiffeomorphismPureAntighostNonminimalLinearMap,
    globalDiffeomorphismNonminimalFieldsLinearEquiv,
    productFirstInclusion, productSecondInclusion] using congrArg
      (fun fields : GlobalDiffeomorphismNonminimalFields period hPeriod =>
        fields.antighost) hEqual

theorem globalDiffeomorphismPureNakanishiLautrupNonminimalLinearMap_injective :
    Function.Injective
      (globalDiffeomorphismPureNakanishiLautrupNonminimalLinearMap period
        hPeriod) := by
  intro first second hEqual
  simpa [globalDiffeomorphismPureNakanishiLautrupNonminimalLinearMap,
    globalDiffeomorphismNonminimalFieldsLinearEquiv,
    productSecondInclusion] using congrArg
      (fun fields : GlobalDiffeomorphismNonminimalFields period hPeriod =>
        fields.nakanishiLautrup) hEqual

theorem globalDiffeomorphismPureGhostGraphLinearMap_injective
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (globalDiffeomorphismPureGhostGraphLinearMap period hPeriod metric) := by
  intro first second hEqual
  apply globalDiffeomorphismPureGhostNonminimalLinearMap_injective period
    hPeriod
  apply
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalOnlyStateLinearMap_injective
      period hPeriod
  apply
    globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding_injective
      period hPeriod metric
  simpa [globalDiffeomorphismPureGhostGraphLinearMap] using hEqual

theorem globalDiffeomorphismPureAntighostGraphLinearMap_injective
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (globalDiffeomorphismPureAntighostGraphLinearMap period hPeriod
        metric) := by
  intro first second hEqual
  apply globalDiffeomorphismPureAntighostNonminimalLinearMap_injective period
    hPeriod
  apply
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalOnlyStateLinearMap_injective
      period hPeriod
  apply
    globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding_injective
      period hPeriod metric
  simpa [globalDiffeomorphismPureAntighostGraphLinearMap] using hEqual

theorem globalDiffeomorphismPureNakanishiLautrupGraphLinearMap_injective
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (globalDiffeomorphismPureNakanishiLautrupGraphLinearMap period hPeriod
        metric) := by
  intro first second hEqual
  apply
    globalDiffeomorphismPureNakanishiLautrupNonminimalLinearMap_injective
      period hPeriod
  apply
    globalCandidateAGaugeFixedNonlinearFullBRSTDiffeomorphismNonminimalOnlyStateLinearMap_injective
      period hPeriod
  apply
    globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding_injective
      period hPeriod metric
  simpa [globalDiffeomorphismPureNakanishiLautrupGraphLinearMap] using hEqual

theorem globalDiffeomorphismPureGhostGraphEmbedding_injective
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (globalDiffeomorphismPureGhostGraphEmbedding period hPeriod metric) := by
  intro first second hEqual
  apply globalDiffeomorphismPureGhostGraphLinearMap_injective period hPeriod
    metric
  simpa [globalDiffeomorphismPureGhostGraphEmbedding] using
    congrArg Subtype.val hEqual

theorem globalDiffeomorphismPureAntighostGraphEmbedding_injective
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (globalDiffeomorphismPureAntighostGraphEmbedding period hPeriod
        metric) := by
  intro first second hEqual
  apply globalDiffeomorphismPureAntighostGraphLinearMap_injective period
    hPeriod metric
  simpa [globalDiffeomorphismPureAntighostGraphEmbedding] using
    congrArg Subtype.val hEqual

theorem globalDiffeomorphismPureNakanishiLautrupGraphEmbedding_injective
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
      (globalDiffeomorphismPureNakanishiLautrupGraphEmbedding period hPeriod
        metric) := by
  intro first second hEqual
  apply
    globalDiffeomorphismPureNakanishiLautrupGraphLinearMap_injective period
      hPeriod metric
  simpa [globalDiffeomorphismPureNakanishiLautrupGraphEmbedding] using
    congrArg Subtype.val hEqual

/-- Gate 265: all four remaining pure nonminimal graph coordinates are
faithful. -/
theorem global_candidateA_gaugeFixed_nonlinear_full_BRST_nonminimal_graph_faithfulness_gate
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod) :
    Function.Injective
        (globalPairedAbelianPureGhostGraphEmbedding period hPeriod metric) ∧
      Function.Injective
          (globalDiffeomorphismPureGhostGraphEmbedding period hPeriod metric) ∧
        Function.Injective
            (globalDiffeomorphismPureAntighostGraphEmbedding period hPeriod
              metric) ∧
          Function.Injective
            (globalDiffeomorphismPureNakanishiLautrupGraphEmbedding period
              hPeriod metric) :=
  ⟨globalPairedAbelianPureGhostGraphEmbedding_injective period hPeriod metric,
    globalDiffeomorphismPureGhostGraphEmbedding_injective period hPeriod
      metric,
    globalDiffeomorphismPureAntighostGraphEmbedding_injective period hPeriod
      metric,
    globalDiffeomorphismPureNakanishiLautrupGraphEmbedding_injective period
      hPeriod metric⟩

end
end P0EFTJanusProgramPGlobalEulerLagrangeGaugeFixedNonlinearFullBRSTNonminimalGraphFaithfulness4D
end JanusFormal
