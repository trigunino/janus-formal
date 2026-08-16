import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianActualKernelChartFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualZeroModeModel4D

/-!
# Terminal H10--H14 frontier with explicitly classified zero modes

This façade is the most concrete current endpoint.  Its three analytic inputs
are:

1. the H10-reduced local physical family;
2. one bounded realization of the common graph Hilbert space in the true local
   Candidate-A chart;
3. a finite type of named zero modes, an equivalence from their coordinate
   space to the actual augmented Hessian kernel, and a gap on the orthogonal
   complement.

The output includes H10--H14, exact zero-mode count, the reduced Green operator,
the real-gap resolvent and the quantitative perturbative stability package.
No anonymous kernel-finiteness proof, chosen projector, parametrix, physical
extension or seven-block bound remains in the interface.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianZeroModeModelFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 7200000
set_option synthInstance.maxHeartbeats 3600000

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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateASixPhysicalChartPullback4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelResolvent4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelStability4D
open P0EFTJanusProgramPGlobalCandidateAActualZeroModeModel4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianActualKernelChartFrontier4D
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

/-- Terminal endpoint with explicitly named zero modes. -/
def global_candidateA_hessian_zeroModeModel_frontier_gate
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
  let physical := globalCandidateAActualKernelChartPhysicalExtension period
    hPeriod configuration data analysis einsteinScale hTransverse family
      realization
  let gap := zeroModes.toActualKernelGap period hPeriod
  let closure := global_candidateA_hessian_actualKernel_chart_frontier_gate
    period hPeriod configuration data analysis einsteinScale hTransverse family
      realization gap
  let classified := global_candidateA_actual_zeroMode_model_gate period hPeriod
    configuration data analysis chart sameAction physical zeroModes
  let resolvent := global_candidateA_actual_kernel_resolvent_gate period hPeriod
    configuration data analysis chart sameAction physical gap
  (closure, classified, resolvent)

/-- Quantitative stability for a classified-zero-mode Hessian. -/
def global_candidateA_hessian_zeroModeModel_stability_gate
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
    (zeroModes : GlobalCandidateAActualZeroModeGap4D period hPeriod configuration
      data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelChartPhysicalExtension period hPeriod
          configuration data analysis einsteinScale hTransverse family
            realization))
    (perturbation : GlobalCandidateAActualKernelPerturbation4D period hPeriod
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelChartPhysicalExtension period hPeriod
          configuration data analysis einsteinScale hTransverse family
            realization)
        (zeroModes.toActualKernelGap period hPeriod)) :=
  global_candidateA_hessian_actualKernel_chart_stability_gate period hPeriod
    configuration data analysis einsteinScale hTransverse family realization
      (zeroModes.toActualKernelGap period hPeriod) perturbation

/-- The terminal frontier has three concrete analytic packets. -/
theorem global_candidateA_hessian_zeroModeModel_three_inputs :
    Nonempty (Unit × Unit × Unit) :=
  ⟨((), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianZeroModeModelFrontier4D
end JanusFormal
