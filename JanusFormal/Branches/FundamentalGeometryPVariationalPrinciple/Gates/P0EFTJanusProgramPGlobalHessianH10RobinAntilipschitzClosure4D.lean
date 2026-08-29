import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedSelfAdjointAntilipschitzShift4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianH10RobinCanonicalClosure4D

/-!
# Terminal H14 closure from a self-adjoint anti-Lipschitz shift

This terminal route combines the narrowest H10/H11 inputs with an H12 range
argument that no longer stores surjectivity.  The family retains only the six
non-Robin local `C²` blocks, H10 supplies Robin, and H11 uses canonical
continuous extensions of the seven true physical second Fréchet blocks.

For H12 one supplies a finite-defect coercive shift together with
self-adjointness and an anti-Lipschitz estimate for `H + P`.  Dense range and
surjectivity are derived, after which the canonical shifted inverse and the
existing H14 certificate are constructed.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianH10RobinAntilipschitzClosure4D

set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option synthInstance.maxHeartbeats 2400000

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
open P0EFTJanusProgramPGlobalCandidateAAugmentedSelfAdjointAntilipschitzShift4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalHessianH10RobinAnalyticClosure4D
open P0EFTJanusProgramPGlobalHessianH10RobinContinuousClosure4D
open P0EFTJanusProgramPGlobalHessianH10RobinCanonicalClosure4D

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

/-- Preferred H14 gate after deriving shifted surjectivity from
self-adjointness and the anti-Lipschitz estimate. -/
def global_candidateA_hessian_h10Robin_antilipschitz_closure_gate
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
        (globalCandidateAH10RobinChart period hPeriod (measure := measure) configuration data
          analysis family)
        (globalCandidateAH10RobinSameAction period hPeriod (measure := measure) configuration data
          analysis family))
    (shift : GlobalCandidateAAugmentedSelfAdjointAntilipschitzShift4D period
      hPeriod (measure := measure) configuration data analysis
        (globalCandidateAH10RobinChart period hPeriod (measure := measure) configuration data
          analysis family)
        (globalCandidateAH10RobinSameAction period hPeriod (measure := measure) configuration data
          analysis family)
        (globalCandidateAH10RobinContinuousPhysicalExtension period hPeriod
          (measure := measure) configuration data analysis family
            (extensions.toContinuous period hPeriod (measure := measure)))) :=
  global_candidateA_hessian_h10Robin_continuous_closure_gate period hPeriod
    (measure := measure) configuration data analysis einsteinScale hBoundaryTransverse family
      (extensions.toContinuous period hPeriod (measure := measure))
      (globalCandidateAFaithfulAugmentedGeneralizedInverse_of_selfAdjointAntilipschitzShift
        period hPeriod configuration data analysis
          (measure := measure)
          (globalCandidateAH10RobinChart period hPeriod (measure := measure) configuration data
            analysis family)
          (globalCandidateAH10RobinSameAction period hPeriod (measure := measure) configuration data
            analysis family)
          (globalCandidateAH10RobinContinuousPhysicalExtension period hPeriod
            (measure := measure) configuration data analysis family
              (extensions.toContinuous period hPeriod (measure := measure)))
          shift)

end
end P0EFTJanusProgramPGlobalHessianH10RobinAntilipschitzClosure4D
end JanusFormal
