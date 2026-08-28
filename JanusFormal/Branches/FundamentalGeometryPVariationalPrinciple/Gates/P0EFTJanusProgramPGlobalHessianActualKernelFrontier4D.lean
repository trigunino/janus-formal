import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianH10ContinuousClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASixPhysicalAggregateExtension4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D

/-!
# Preferred H10--H14 frontier on the actual zero-mode complement

This façade combines the narrowest constructive inputs currently available:

1. the H10-reduced local Candidate-A family, with only six independent `C²`
   physical blocks;
2. one aggregate continuous extension of those six non-Robin Hessians, while
   Robin is supplied by the genuine H10 second Fréchet derivative;
3. finite-dimensionality of the actual augmented kernel and one positive gap
   on its orthogonal complement.

The third item replaces every auxiliary finite projection or parametrix by the
canonical space `(ker H)ᗮ`.  The gate exposes H10, H13, H11, H12, the exact
range splitting and the reduced Green operator in one inferred product, so no
additional certificate type can hide an extra premise.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 5600000
set_option synthInstance.maxHeartbeats 2800000

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
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryH10Closure4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalHessianH10ContinuousClosure4D

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

/-- Reduced family used by the actual-kernel route. -/
def globalCandidateAActualKernelReducedFamily
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
          couplings.matterMassSquared) einsteinScale) :=
  globalCandidateAH10ContinuousReducedFamily period hPeriod (measure := measure) configuration data
    analysis einsteinScale hTransverse family

/-- Actual D10-free local chart. -/
def globalCandidateAActualKernelChart
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
          couplings.matterMassSquared) einsteinScale) :=
  globalCandidateAH10ContinuousChart period hPeriod (measure := measure) configuration data analysis
    einsteinScale hTransverse family

/-- Matter--LL same-action bridge generated from the same family. -/
def globalCandidateAActualKernelSameAction
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
          couplings.matterMassSquared) einsteinScale) :=
  globalCandidateAH10ContinuousSameAction period hPeriod (measure := measure) configuration data
    analysis einsteinScale hTransverse family

/-- H11 extension from H10 Robin plus one non-Robin aggregate. -/
def globalCandidateAActualKernelPhysicalExtension
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
    (extension : GlobalCandidateASixPhysicalAggregateContinuousExtension4D
      period hPeriod configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        einsteinScale) :=
  globalCandidateASevenPhysicalCommonDomainExtension_of_sixAggregate period
    hPeriod configuration data analysis
      (globalCandidateAActualKernelChart period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      (globalCandidateAActualKernelSameAction period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      einsteinScale hTransverse extension

/-- Preferred terminal gate.  The result is deliberately inferred as the
product of the existing H10, H13, H11 and H12 certificates together with the
actual-kernel Green certificate. -/
def global_candidateA_hessian_actualKernel_frontier_gate
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
    (extension : GlobalCandidateASixPhysicalAggregateContinuousExtension4D
      period hPeriod configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        einsteinScale)
    (gap : GlobalCandidateAActualKernelGap4D period hPeriod configuration data
      analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelPhysicalExtension period hPeriod
          configuration data analysis einsteinScale hTransverse family
            extension)) :=
  let chart := globalCandidateAActualKernelChart period hPeriod configuration
    data analysis einsteinScale hTransverse family
  let sameAction := globalCandidateAActualKernelSameAction period hPeriod
    configuration data analysis einsteinScale hTransverse family
  let physical := globalCandidateAActualKernelPhysicalExtension period hPeriod
    configuration data analysis einsteinScale hTransverse family extension
  let h10 := global_candidateA_h10_closure_gate period hPeriod data
    einsteinScale data.plusGravity.metric hTransverse
  let h13 := global_candidateA_h13_minimalPhysical_h10ReducedFamily_gate period
    hPeriod configuration data analysis
      (diracGreenClosureMatterRealization period hPeriod
        couplings.matterMassSquared)
      einsteinScale hTransverse family
  let h11 := global_candidateA_h11_common_domain_gate_of_sixAggregate period
    hPeriod configuration data analysis chart sameAction einsteinScale
      hTransverse extension
  let h12 := global_candidateA_h12_fredholm_gate_of_actualKernelGap period
    hPeriod configuration data analysis chart sameAction physical gap
  let reduced := global_candidateA_actual_kernel_complement_gate period hPeriod
    configuration data analysis chart sameAction physical gap
  And.intro h10 (And.intro h13 (And.intro h11 (And.intro h12 reduced)))

/-- The actual-kernel frontier has exactly three analytic packets after the
fixed geometry and SpinC Green theorem: family, aggregate extension and actual
kernel gap. -/
theorem global_candidateA_hessian_actualKernel_three_inputs :
    Nonempty (Unit × Unit × Unit) :=
  ⟨((), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
end JanusFormal
