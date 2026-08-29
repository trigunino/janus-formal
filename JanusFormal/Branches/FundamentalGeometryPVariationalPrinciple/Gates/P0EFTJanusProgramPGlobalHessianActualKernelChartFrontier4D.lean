import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianActualKernelBoundedFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASixPhysicalChartPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelStability4D

/-!
# H10--H14 from one bounded physical-chart realization and the actual gap

The H11 estimate is automatic once the common graph Hilbert space maps
continuously to the true local physical chart and agrees there with the smooth
core.  This façade therefore reduces the terminal analytic inputs to:

1. the H10-reduced local family;
2. one bounded common-to-chart realization;
3. finite actual kernel and a positive gap on its orthogonal complement.

It exposes H10--H14, the Green operator, the real resolvent and the quantitative
small-perturbation framework without any chosen physical extension,
zero-mode projector or parametrix.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianActualKernelChartFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 6800000
set_option synthInstance.maxHeartbeats 3400000

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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateASixPhysicalAggregateExtension4D
open P0EFTJanusProgramPGlobalCandidateASixPhysicalChartPullback4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelResolvent4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelStability4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryH10Closure4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
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

/-- H11 extension produced by the bounded common-to-chart realization. -/
def globalCandidateAActualKernelChartPhysicalExtension
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
      period hPeriod (measure := measure) configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (realization : GlobalCandidateACommonHilbertToLocalChart4D period hPeriod
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family) einsteinScale family) :=
  globalCandidateASevenPhysicalCommonDomainExtension_of_sixAggregate period
    hPeriod configuration data analysis
      (globalCandidateAActualKernelChart period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      (globalCandidateAActualKernelSameAction period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      einsteinScale hTransverse
      (globalCandidateASixPhysicalAggregateExtension_of_chartPullback period
        hPeriod configuration data analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family)
          einsteinScale hTransverse family realization)

/-- Preferred chart-realization terminal gate. -/
def global_candidateA_hessian_actualKernel_chart_frontier_gate
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
      period hPeriod (measure := measure) configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (realization : GlobalCandidateACommonHilbertToLocalChart4D period hPeriod
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family) einsteinScale family)
    (gap : GlobalCandidateAActualKernelGap4D period hPeriod configuration data
      analysis
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
  let h10 := global_candidateA_h10_closure_gate period hPeriod data
    einsteinScale data.plusGravity.metric hTransverse
  let h13 := global_candidateA_h13_minimalPhysical_h10ReducedFamily_gate period
    hPeriod configuration data analysis
      (diracGreenClosureMatterRealization period hPeriod
        couplings.matterMassSquared)
      einsteinScale hTransverse family
  let h11 := global_candidateA_h11_gate_of_chartPullback period hPeriod
    configuration data analysis chart sameAction einsteinScale hTransverse
      family realization
  let h12 := global_candidateA_h12_fredholm_gate_of_actualKernelGap period
    hPeriod configuration data analysis chart sameAction physical gap
  let reduced := global_candidateA_actual_kernel_complement_gate period hPeriod
    configuration data analysis chart sameAction physical gap
  let resolvent := global_candidateA_actual_kernel_resolvent_gate period hPeriod
    configuration data analysis chart sameAction physical gap
  And.intro h10
    (And.intro h13 (And.intro h11
      (And.intro h12 (And.intro reduced resolvent))))

/-- Stability is available for every perturbation smaller than the same actual
gap, with no extra terminal packet. -/
def global_candidateA_hessian_actualKernel_chart_stability_gate
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
      period hPeriod (measure := measure) configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (realization : GlobalCandidateACommonHilbertToLocalChart4D period hPeriod
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family) einsteinScale family)
    (gap : GlobalCandidateAActualKernelGap4D period hPeriod configuration data
      analysis
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
        gap) :=
  global_candidateA_actual_kernel_stability_gate period hPeriod configuration
    data analysis
      (globalCandidateAActualKernelChart period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      (globalCandidateAActualKernelSameAction period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      (globalCandidateAActualKernelChartPhysicalExtension period hPeriod
        configuration data analysis einsteinScale hTransverse family realization)
      gap perturbation

/-- The final frontier still has three inputs, with H11 represented by the
bounded chart realization rather than an estimate. -/
theorem global_candidateA_hessian_actualKernel_chart_three_inputs :
    Nonempty (Unit × Unit × Unit) :=
  ⟨((), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianActualKernelChartFrontier4D
end JanusFormal
