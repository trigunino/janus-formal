import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASixPhysicalChartPullback4D

/-!
# The six canonical non-Robin Hessians of the Candidate-A chart

The H11 chart-pullback route already avoids selecting an arbitrary continuous
physical form: it pulls the total local physical Hessian back through one
bounded realization of the common graph Hilbert space.  This file makes the
remaining six-block content explicit.

For each non-Robin physical block we take, by definition, the genuine second
Frechet derivative of the corresponding action in the same local Candidate-A
chart and at the same H13 base point.  The only compatibility statement left is
therefore the finite decomposition

`B_six = sum_j D^2 S_j`.

Once this equality is supplied, the existing chart pullback constructs the H11
continuous extension.  No bilinear form, product constant, replacement action,
second completion or D10 direction is added.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASixCanonicalChartHessians4D

set_option autoImplicit false
set_option maxHeartbeats 7200000
set_option synthInstance.maxHeartbeats 3600000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousExtension4D
open P0EFTJanusProgramPGlobalCandidateASixPhysicalAggregateExtension4D
open P0EFTJanusProgramPGlobalCandidateASixPhysicalChartPullback4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

/-- The actual nine action blocks of the local chart, evaluated at the H13 base
point. -/
def globalCandidateALocalActionBlocksAtBase
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (basePoint : chart.Model)
    (hBasePoint : basePoint ∈ chart.family.domain) :=
  globalCandidateAActionBlocks period hPeriod
    (chart.family.toActionFamily period hPeriod basePoint hBasePoint) measure

/-- The action attached to one of the six retained non-Robin physical blocks. -/
def globalCandidateALocalNonRobinBlockAction
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (basePoint : chart.Model)
    (hBasePoint : basePoint ∈ chart.family.domain)
    (block : GlobalCandidateANonRobinPhysicalBlock) : chart.Model -> Real :=
  let blocks := globalCandidateALocalActionBlocksAtBase period hPeriod chart
    basePoint hBasePoint
  match block with
  | .candidateA => blocks.candidateA
  | .einsteinHilbertPlus => blocks.einsteinHilbertPlus
  | .einsteinHilbertMinus => blocks.einsteinHilbertMinus
  | .maxwellPlus => blocks.maxwellPlus
  | .maxwellMinus => blocks.maxwellMinus
  | .finiteBV => blocks.finiteBV

/-- Genuine second Frechet derivative of one named non-Robin action block. -/
def globalCandidateALocalNonRobinBlockHessian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (basePoint : chart.Model)
    (hBasePoint : basePoint ∈ chart.family.domain)
    (block : GlobalCandidateANonRobinPhysicalBlock) :
    chart.Model →L[Real] chart.Model →L[Real] Real :=
  fderiv Real
    (fun point => fderiv Real
      (globalCandidateALocalNonRobinBlockAction period hPeriod chart basePoint
        hBasePoint block) point)
    basePoint

/-- Finite sum of the six genuine chart Hessians. -/
def globalCandidateALocalSixCanonicalHessian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (basePoint : chart.Model)
    (hBasePoint : basePoint ∈ chart.family.domain) :
    chart.Model →L[Real] chart.Model →L[Real] Real :=
  ∑ block : GlobalCandidateANonRobinPhysicalBlock,
    globalCandidateALocalNonRobinBlockHessian period hPeriod chart basePoint
      hBasePoint block

/-- The sole compatibility identity: after pullback to the common Hilbert
space, the six genuine chart Hessians equal the total physical Hessian with
the H10-compatible Robin form removed. -/
structure GlobalCandidateASixCanonicalChartHessianAgreement4D
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
    (einsteinScale : Real)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure) period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (realization : GlobalCandidateACommonHilbertToLocalChart4D period hPeriod
      configuration data analysis chart sameAction einsteinScale family) : Prop where
  common_domain_sum_eq :
    (globalCandidateALocalSixCanonicalHessian period hPeriod chart
      sameAction.chartBridge.basePoint
        sameAction.chartBridge.basePoint_mem).bilinearComp
          realization.realization realization.realization =
      globalCandidateASixPhysicalCommonDomainForm_of_chartPullback period hPeriod
        configuration data analysis chart sameAction einsteinScale family
          realization

/-- Pull one genuine block Hessian to the common graph Hilbert space. -/
def globalCandidateASixCanonicalCommonDomainBlock
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
    (einsteinScale : Real)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure) period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (realization : GlobalCandidateACommonHilbertToLocalChart4D period hPeriod
      configuration data analysis chart sameAction einsteinScale family)
    (block : GlobalCandidateANonRobinPhysicalBlock) :=
  (globalCandidateALocalNonRobinBlockHessian period hPeriod chart
    sameAction.chartBridge.basePoint sameAction.chartBridge.basePoint_mem block).bilinearComp
      realization.realization realization.realization

/-- Pull the canonical six-block sum to the common graph Hilbert space. -/
def globalCandidateASixCanonicalCommonDomainHessian
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
    (einsteinScale : Real)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure) period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (realization : GlobalCandidateACommonHilbertToLocalChart4D period hPeriod
      configuration data analysis chart sameAction einsteinScale family) :=
  (globalCandidateALocalSixCanonicalHessian period hPeriod chart
    sameAction.chartBridge.basePoint
      sameAction.chartBridge.basePoint_mem).bilinearComp
        realization.realization realization.realization

/-- The one local decomposition identity identifies the canonical pullback with
the aggregate H11 pullback already used by the terminal construction. -/
theorem globalCandidateASixCanonicalCommonDomainHessian_eq_chartPullback
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
    (einsteinScale : Real)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure) period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (realization : GlobalCandidateACommonHilbertToLocalChart4D period hPeriod
      configuration data analysis chart sameAction einsteinScale family)
    (agreement : GlobalCandidateASixCanonicalChartHessianAgreement4D period
      hPeriod configuration data analysis chart sameAction einsteinScale family
        realization) :
    globalCandidateASixCanonicalCommonDomainHessian period hPeriod configuration
        data analysis chart sameAction einsteinScale family realization =
      globalCandidateASixPhysicalCommonDomainForm_of_chartPullback period hPeriod
        configuration data analysis chart sameAction einsteinScale family
          realization := by
  unfold globalCandidateASixCanonicalCommonDomainHessian
  exact agreement.common_domain_sum_eq

/-- H11 gate with the six actual chart Hessians exposed explicitly.  The
continuous extension itself is still the canonical chart pullback already
constructed in the preceding layer. -/
def global_candidateA_h11_canonical_six_chart_gate
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
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure) period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (realization : GlobalCandidateACommonHilbertToLocalChart4D period hPeriod
      configuration data analysis chart sameAction einsteinScale family)
    (agreement : GlobalCandidateASixCanonicalChartHessianAgreement4D period
      hPeriod configuration data analysis chart sameAction einsteinScale family
        realization) :=
  let extension :=
    globalCandidateASixPhysicalAggregateExtension_of_chartPullback period hPeriod
      configuration data analysis chart sameAction einsteinScale hTransverse
        family realization
  (extension,
    PLift.up
      (globalCandidateASixCanonicalCommonDomainHessian_eq_chartPullback period
        hPeriod configuration data analysis chart sameAction einsteinScale family
          realization agreement))

end
end P0EFTJanusProgramPGlobalCandidateASixCanonicalChartHessians4D
end JanusFormal
