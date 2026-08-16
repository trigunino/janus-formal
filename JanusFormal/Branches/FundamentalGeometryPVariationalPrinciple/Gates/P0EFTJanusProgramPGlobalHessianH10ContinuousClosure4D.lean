import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousExtension4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedGeneralizedInverse4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D

/-!
# H14 from H10, six continuous physical blocks and one generalized inverse

This is the strongest constructive H14 interface currently exposed.  It
consumes the already closed mobile boundary sector twice, in the two places
where it belongs:

* Robin regularity in the local Candidate-A family is derived from the H10
  completed action;
* the Robin common-domain Hessian is the H10 second Fréchet derivative pulled
  back by one bounded projection.

Matter and LL are supplied by their genuine closed graph actions.  The only
new physical regularity input is therefore six local `C²` blocks, the only H11
input is six continuous bilinear extensions with exact dense-core agreement,
and the only H12 operator input is one generalized inverse satisfying `HQH=H`
with finite canonical defects.  The theorem below composes these data directly
into the existing terminal H14 certificate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianH10ContinuousClosure4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 1800000
set_option maxHeartbeats 3600000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedFredholmSum4D
open P0EFTJanusProgramPGlobalHessianClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamily4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyPhysicalC2Reduction4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousExtension4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedParametrix4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedGeneralizedInverse4D
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

/-- Reduced family consumed by the existing Dirac-Green chart constructor. -/
def globalCandidateAH10ContinuousReducedFamily
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale) :
    ProgramPGlobalMinimalPhysicalLocalActionFamilyReducedData4D period hPeriod
      configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) :=
  (family.toPhysicalC2 period hPeriod hTransverse).toReduced period hPeriod

/-- Actual D10-free local chart generated from the H10-reduced family. -/
def globalCandidateAH10ContinuousChart
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale) :=
  diracGreenClosureChart period hPeriod configuration data analysis
    (globalCandidateAH10ContinuousReducedFamily period hPeriod configuration
      data analysis einsteinScale hTransverse family)

/-- H13 matter--LL bridge generated from the same H10-reduced family. -/
def globalCandidateAH10ContinuousSameAction
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale) :=
  diracGreenClosureMatterLLSameAction period hPeriod configuration data analysis
    (globalCandidateAH10ContinuousReducedFamily period hPeriod configuration
      data analysis einsteinScale hTransverse family)

/-- H11 extension generated from the H10 Robin Hessian and six continuous
physical block extensions. -/
def globalCandidateAH10ContinuousPhysicalExtension
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (extensions : GlobalCandidateASixPhysicalContinuousExtensions4D period
      hPeriod configuration data analysis
        (globalCandidateAH10ContinuousChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAH10ContinuousSameAction period hPeriod configuration
          data analysis einsteinScale hTransverse family)
        einsteinScale) :=
  globalCandidateASevenPhysicalCommonDomainExtension_of_sixContinuous period
    hPeriod configuration data analysis
      (globalCandidateAH10ContinuousChart period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      (globalCandidateAH10ContinuousSameAction period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      einsteinScale hTransverse extensions

/-- Canonical finite-defect parametrix generated from one generalized inverse. -/
def globalCandidateAH10ContinuousParametrix
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (extensions : GlobalCandidateASixPhysicalContinuousExtensions4D period
      hPeriod configuration data analysis
        (globalCandidateAH10ContinuousChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAH10ContinuousSameAction period hPeriod configuration
          data analysis einsteinScale hTransverse family)
        einsteinScale)
    (inverse : GlobalCandidateAFaithfulAugmentedGeneralizedInverse4D period
      hPeriod configuration data analysis
        (globalCandidateAH10ContinuousChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAH10ContinuousSameAction period hPeriod configuration
          data analysis einsteinScale hTransverse family)
        (globalCandidateAH10ContinuousPhysicalExtension period hPeriod
          configuration data analysis einsteinScale hTransverse family
            extensions)) :=
  globalCandidateAFaithfulAugmentedFiniteDefectParametrix_of_generalizedInverse
    period hPeriod configuration data analysis
      (globalCandidateAH10ContinuousChart period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      (globalCandidateAH10ContinuousSameAction period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      (globalCandidateAH10ContinuousPhysicalExtension period hPeriod
        configuration data analysis einsteinScale hTransverse family extensions)
      inverse

/-- H12 estimate packet generated by the canonical finite-defect parametrix. -/
def globalCandidateAH10ContinuousFredholmEstimates
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (extensions : GlobalCandidateASixPhysicalContinuousExtensions4D period
      hPeriod configuration data analysis
        (globalCandidateAH10ContinuousChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAH10ContinuousSameAction period hPeriod configuration
          data analysis einsteinScale hTransverse family)
        einsteinScale)
    (inverse : GlobalCandidateAFaithfulAugmentedGeneralizedInverse4D period
      hPeriod configuration data analysis
        (globalCandidateAH10ContinuousChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAH10ContinuousSameAction period hPeriod configuration
          data analysis einsteinScale hTransverse family)
        (globalCandidateAH10ContinuousPhysicalExtension period hPeriod
          configuration data analysis einsteinScale hTransverse family
            extensions)) :=
  globalCandidateAFaithfulAugmentedFredholmEstimates_of_parametrix period hPeriod
    configuration data analysis
      (globalCandidateAH10ContinuousChart period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      (globalCandidateAH10ContinuousSameAction period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      (globalCandidateAH10ContinuousPhysicalExtension period hPeriod
        configuration data analysis einsteinScale hTransverse family extensions)
      (globalCandidateAH10ContinuousParametrix period hPeriod configuration data
        analysis einsteinScale hTransverse family extensions inverse)

/-- Terminal H14 gate with H10 consumed in both the local and common-domain
Robin sectors. -/
theorem global_candidateA_hessian_h10_continuous_closure_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (extensions : GlobalCandidateASixPhysicalContinuousExtensions4D period
      hPeriod configuration data analysis
        (globalCandidateAH10ContinuousChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAH10ContinuousSameAction period hPeriod configuration
          data analysis einsteinScale hTransverse family)
        einsteinScale)
    (inverse : GlobalCandidateAFaithfulAugmentedGeneralizedInverse4D period
      hPeriod configuration data analysis
        (globalCandidateAH10ContinuousChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAH10ContinuousSameAction period hPeriod configuration
          data analysis einsteinScale hTransverse family)
        (globalCandidateAH10ContinuousPhysicalExtension period hPeriod
          configuration data analysis einsteinScale hTransverse family
            extensions)) :=
  global_candidateA_hessian_closure_gate period hPeriod configuration data
    analysis
      (globalCandidateAH10ContinuousChart period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      einsteinScale hTransverse
      (globalCandidateAH10ContinuousSameAction period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      (globalCandidateAH10ContinuousPhysicalExtension period hPeriod
        configuration data analysis einsteinScale hTransverse family extensions)
      (globalCandidateAH10ContinuousFredholmEstimates period hPeriod
        configuration data analysis einsteinScale hTransverse family extensions
          inverse)

end
end P0EFTJanusProgramPGlobalHessianH10ContinuousClosure4D
end JanusFormal
