import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedOrthogonalLowerBoundShift4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianH10RobinLowerBoundClosure4D

/-!
# Terminal H14 route from an orthogonal finite defect and one lower bound

The augmented Hessian itself is already self-adjoint.  Consequently the H12
input no longer needs to repeat self-adjointness of the shifted operator.  A
self-adjoint finite-dimensional defect projection makes `H + P` self-adjoint,
and the direct estimate

`‖x‖ ≤ C ‖(H + P) x‖`

forces its surjectivity and bounded invertibility.  This file attaches that
narrow H12 packet to the H10-supplied family and canonical H11 physical
extensions, producing the existing H14 certificate.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianH10RobinOrthogonalLowerBoundClosure4D

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 2500000

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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10RobinReduction4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensions4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedOrthogonalLowerBoundShift4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalHessianH10RobinAnalyticClosure4D
open P0EFTJanusProgramPGlobalHessianH10RobinCanonicalClosure4D
open P0EFTJanusProgramPGlobalHessianH10RobinLowerBoundClosure4D

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

/-- Narrow terminal gate in which self-adjointness of the full shift is derived
from the already proved self-adjoint augmented Hessian and the orthogonal finite
defect. -/
theorem global_candidateA_hessian_h10Robin_orthogonalLowerBound_closure_gate
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
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared))
    (extensions : GlobalCandidateASevenPhysicalCanonicalContinuousExtensions4D
      period hPeriod configuration data analysis
        (globalCandidateAH10RobinChart period hPeriod configuration data
          analysis family)
        (globalCandidateAH10RobinSameAction period hPeriod configuration data
          analysis family))
    (shift : GlobalCandidateAAugmentedOrthogonalLowerBoundShift4D period hPeriod
      configuration data analysis
        (globalCandidateAH10RobinChart period hPeriod configuration data
          analysis family)
        (globalCandidateAH10RobinSameAction period hPeriod configuration data
          analysis family)
        (globalCandidateAH10RobinCanonicalPhysicalExtension period hPeriod
          configuration data analysis family extensions)) :=
  global_candidateA_hessian_h10Robin_lowerBound_closure_gate period hPeriod
    configuration data analysis einsteinScale hBoundaryTransverse family
      extensions (shift.toLowerBound period hPeriod)

end
end P0EFTJanusProgramPGlobalHessianH10RobinOrthogonalLowerBoundClosure4D
end JanusFormal
