import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedComplementInverse4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianH10RobinContinuousClosure4D

/-!
# Preferred H14 route from H10, continuous physical blocks and complements

This module exposes the most decomposed constructive terminal route currently
available:

* H10 supplies the Robin action and its `C²` Hessian;
* six non-Robin physical blocks supply local `C²` regularity;
* seven continuous bilinear extensions supply all H11 bounds;
* an inverse on finite kernel/cokernel complements supplies H12.

Every intermediate aggregate packet is reconstructed by the imported gates.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianH10RobinComplementClosure4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000

noncomputable section

open Set Topology MeasureTheory
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
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10RobinReduction4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousExtensions4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedGeneralizedInverse4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedComplementInverse4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalHessianH10RobinAnalyticClosure4D
open P0EFTJanusProgramPGlobalHessianH10RobinContinuousClosure4D

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

/-- Preferred H14 gate from the fully decomposed analytic inputs. -/
def global_candidateA_hessian_h10Robin_complement_closure_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hBoundaryTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10RobinData4D
      period hPeriod (measure := measure) configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared))
    (extensions : GlobalCandidateASevenPhysicalContinuousBlockExtensions4D
      period hPeriod (measure := measure) configuration data analysis
        (globalCandidateAH10RobinChart period hPeriod (measure := measure) configuration data
          analysis family)
        (globalCandidateAH10RobinSameAction period hPeriod (measure := measure) configuration data
          analysis family))
    (inverse : GlobalCandidateAFaithfulAugmentedComplementInverse4D period
      hPeriod (measure := measure) configuration data analysis
        (globalCandidateAH10RobinChart period hPeriod (measure := measure) configuration data
          analysis family)
        (globalCandidateAH10RobinSameAction period hPeriod (measure := measure) configuration data
          analysis family)
        (globalCandidateAH10RobinContinuousPhysicalExtension period hPeriod
          (measure := measure) configuration data analysis family extensions)) :=
  global_candidateA_hessian_h10Robin_continuous_closure_gate period hPeriod
    (measure := measure) configuration data analysis einsteinScale hBoundaryTransverse family
    extensions
      (globalCandidateAFaithfulAugmentedGeneralizedInverse_of_complement period
        hPeriod (measure := measure) configuration data analysis
        (globalCandidateAH10RobinChart period hPeriod (measure := measure) configuration data
          analysis family)
        (globalCandidateAH10RobinSameAction period hPeriod (measure := measure) configuration data
          analysis family)
        (globalCandidateAH10RobinContinuousPhysicalExtension period hPeriod
          (measure := measure) configuration data analysis family extensions)
        inverse)

end
end P0EFTJanusProgramPGlobalHessianH10RobinComplementClosure4D
end JanusFormal
