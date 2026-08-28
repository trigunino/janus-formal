import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedSelfAdjointLowerBoundShift4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensions4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianH10RobinContinuousClosure4D

/-!
# Terminal H14 closure from a shifted global lower bound

This is the PDE-facing terminal route.  The local family retains only six
independent `C²` physical blocks; H10 supplies Robin and the graph actions
supply matter and LL.  H11 receives the canonical continuous extensions of the
seven true physical second derivatives.

For H12 the sole range estimate is

`‖x‖ ≤ C ‖(H + P) x‖`,

together with self-adjointness of the shifted operator and the finite-defect
coercive packet.  The anti-Lipschitz certificate, dense range, surjectivity,
bounded inverse, generalized inverse and Fredholm conclusions are all derived.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianH10RobinLowerBoundClosure4D

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 2500000

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
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensions4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedSelfAdjointLowerBoundShift4D
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

/-- Preferred terminal H14 gate in direct norm-estimate form. -/
def global_candidateA_hessian_h10Robin_lowerBound_closure_gate
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
    (extensions : GlobalCandidateASevenPhysicalCanonicalContinuousExtensions4D
      period hPeriod (measure := measure) configuration data analysis
        (globalCandidateAH10RobinChart period hPeriod (measure := measure)
          configuration data analysis family)
        (globalCandidateAH10RobinSameAction period hPeriod (measure := measure)
          configuration data analysis family))
    (shift : GlobalCandidateAAugmentedSelfAdjointLowerBoundShift4D period
      hPeriod (measure := measure) configuration data analysis
        (globalCandidateAH10RobinChart period hPeriod (measure := measure)
          configuration data analysis family)
        (globalCandidateAH10RobinSameAction period hPeriod (measure := measure)
          configuration data analysis family)
        (globalCandidateAH10RobinContinuousPhysicalExtension period hPeriod
          (measure := measure) configuration data analysis family
            (extensions.toContinuous period hPeriod))) :=
  global_candidateA_hessian_h10Robin_continuous_closure_gate period hPeriod
    (measure := measure) configuration data analysis einsteinScale
      hBoundaryTransverse family
      (extensions.toContinuous period hPeriod)
      (globalCandidateAFaithfulAugmentedGeneralizedInverse_of_selfAdjointLowerBoundShift
        period hPeriod (measure := measure) configuration data analysis
          (globalCandidateAH10RobinChart period hPeriod (measure := measure)
            configuration data analysis family)
          (globalCandidateAH10RobinSameAction period hPeriod (measure := measure)
            configuration data analysis family)
          (globalCandidateAH10RobinContinuousPhysicalExtension period hPeriod
            (measure := measure) configuration data analysis family
              (extensions.toContinuous period hPeriod))
          shift)

end
end P0EFTJanusProgramPGlobalHessianH10RobinLowerBoundClosure4D
end JanusFormal
