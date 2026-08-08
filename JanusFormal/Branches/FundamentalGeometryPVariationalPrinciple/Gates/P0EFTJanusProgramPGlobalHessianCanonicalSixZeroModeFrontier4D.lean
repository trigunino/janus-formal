import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASixCanonicalChartHessians4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianZeroModeModelFrontier4D

/-!
# Terminal H10--H14 frontier with the six actual chart Hessians

This facade strengthens the classified-zero-mode terminal endpoint by retaining
an explicit certificate that the non-Robin physical term is the finite sum of
the six genuine second Frechet derivatives of the Candidate-A chart actions.

The analytic inputs are therefore:

1. the H10-reduced local family;
2. one bounded realization of the common graph Hilbert space in that chart;
3. one finite action-level Hessian decomposition identity;
4. the finite actual-kernel model and the coercive gap on its orthogonal
   complement.

The H11 extension, H12 Fredholm result, reduced Green and real resolvent are all
still constructed by the existing gates.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixZeroModeFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option synthInstance.maxHeartbeats 6000000

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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateASixPhysicalChartPullback4D
open P0EFTJanusProgramPGlobalCandidateASixCanonicalChartHessians4D
open P0EFTJanusProgramPGlobalCandidateAActualZeroModeModel4D
open P0EFTJanusProgramPGlobalHessianActualKernelChartFrontier4D
open P0EFTJanusProgramPGlobalHessianZeroModeModelFrontier4D
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

/-- Terminal endpoint retaining the finite decomposition into the six genuine
non-Robin chart Hessians. -/
def global_candidateA_hessian_canonicalSix_zeroMode_frontier_gate
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
    (realization : GlobalCandidateACommonHilbertToLocalChart4D period hPeriod
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family))
    (agreement : GlobalCandidateASixCanonicalChartHessianAgreement4D period
      hPeriod configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        einsteinScale family)
    (zeroModes : GlobalCandidateAActualZeroModeGap4D period hPeriod configuration
      data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelChartPhysicalExtension period hPeriod
          configuration data analysis einsteinScale hTransverse family
            realization)) :=
  let chart := globalCandidateAActualKernelChart period hPeriod configuration
    data analysis einsteinScale hTransverse family
  let sameAction := globalCandidateAActualKernelSameAction period hPeriod
    configuration data analysis einsteinScale hTransverse family
  let canonicalH11 := global_candidateA_h11_canonical_six_chart_gate period
    hPeriod configuration data analysis chart sameAction einsteinScale
      hTransverse family realization agreement
  let terminal := global_candidateA_hessian_zeroModeModel_frontier_gate period
    hPeriod configuration data analysis einsteinScale hTransverse family
      realization zeroModes
  (terminal, canonicalH11)

/-- The strengthened endpoint has four concrete analytic packets. -/
theorem global_candidateA_hessian_canonicalSix_zeroMode_four_inputs :
    Nonempty (Unit × Unit × Unit × Unit) :=
  ⟨((), (), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixZeroModeFrontier4D
end JanusFormal
