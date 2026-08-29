import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedOrthogonalCoerciveShift4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianH10RobinOrthogonalLowerBoundClosure4D

/-!
# Terminal H14 route from orthogonal finite-defect coercivity

This façade removes the last independently supplied global shifted estimate.
The H12 input now consists only of the finite-defect coercivity packet, the
self-adjointness of its defect projection, and LL stationarity.  The global
bound for `H + P`, shifted self-adjointness, surjectivity and inverse are all
constructed by the imported gates before the canonical H14 assembler is
invoked.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianH10RobinOrthogonalCoerciveClosure4D

set_option autoImplicit false
set_option maxHeartbeats 5200000
set_option synthInstance.maxHeartbeats 2600000

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
open P0EFTJanusProgramPGlobalCandidateAAugmentedOrthogonalCoerciveShift4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalHessianH10RobinAnalyticClosure4D
open P0EFTJanusProgramPGlobalHessianH10RobinContinuousClosure4D
open P0EFTJanusProgramPGlobalHessianH10RobinOrthogonalLowerBoundClosure4D

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

/-- Narrowest terminal H14 gate currently exposed. -/
def global_candidateA_hessian_h10Robin_orthogonalCoercive_closure_gate
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
    (shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      (measure := measure) configuration data analysis
        (globalCandidateAH10RobinChart period hPeriod (measure := measure)
          configuration data analysis family)
        (globalCandidateAH10RobinSameAction period hPeriod (measure := measure)
          configuration data analysis family)
        (globalCandidateAH10RobinContinuousPhysicalExtension period hPeriod
          (measure := measure) configuration data analysis family
            (extensions.toContinuous period hPeriod))) :=
  global_candidateA_hessian_h10Robin_orthogonalLowerBound_closure_gate period
    hPeriod (measure := measure) configuration data analysis einsteinScale
      hBoundaryTransverse family extensions
      (shift.toLowerBound period hPeriod (measure := measure))

end
end P0EFTJanusProgramPGlobalHessianH10RobinOrthogonalCoerciveClosure4D
end JanusFormal
