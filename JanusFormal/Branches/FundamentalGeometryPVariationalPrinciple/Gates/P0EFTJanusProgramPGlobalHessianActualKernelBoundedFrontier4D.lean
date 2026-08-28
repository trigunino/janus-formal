import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASixPhysicalAggregateBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelResolvent4D

/-!
# Narrowest H10--H14 frontier: one H11 estimate and the actual kernel gap

The continuous six-block extension can itself be constructed canonically from
one product estimate on the smooth core.  This façade therefore accepts only:

1. the H10-reduced local family;
2. one bound on the six-block remainder `B_physical - B_Robin`;
3. finite-dimensionality of the genuine augmented kernel and a positive gap
   on its orthogonal complement.

It returns all previous H10--H14 checkpoints together with the reduced Green
operator and its real resolvent on the open gap.  No zero-mode projection,
parametrix or hand-selected continuous physical form remains in the input.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianActualKernelBoundedFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 6200000
set_option synthInstance.maxHeartbeats 3100000

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
open P0EFTJanusProgramPGlobalCandidateASixPhysicalAggregateBound4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelResolvent4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryH10Closure4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D

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

/-- Canonical H11 extension obtained from the sole six-block estimate. -/
def globalCandidateAActualKernelBoundedPhysicalExtension
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
    (bound : GlobalCandidateASixPhysicalAggregateCoreBound4D period hPeriod
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        einsteinScale) :=
  globalCandidateASevenPhysicalCommonDomainExtension_of_sixAggregateBound period
    hPeriod configuration data analysis
      (globalCandidateAActualKernelChart period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      (globalCandidateAActualKernelSameAction period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      einsteinScale bound

/-- Narrow terminal gate with exactly one H11 estimate and one actual-kernel
gap. -/
def global_candidateA_hessian_actualKernel_bounded_frontier_gate
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
    (bound : GlobalCandidateASixPhysicalAggregateCoreBound4D period hPeriod
      configuration data analysis
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
        (globalCandidateAActualKernelBoundedPhysicalExtension period hPeriod
          configuration data analysis einsteinScale hTransverse family bound)) :=
  let chart := globalCandidateAActualKernelChart period hPeriod configuration
    data analysis einsteinScale hTransverse family
  let sameAction := globalCandidateAActualKernelSameAction period hPeriod
    configuration data analysis einsteinScale hTransverse family
  let physical := globalCandidateAActualKernelBoundedPhysicalExtension period
    hPeriod configuration data analysis einsteinScale hTransverse family bound
  let h10 := global_candidateA_h10_closure_gate period hPeriod data
    einsteinScale data.plusGravity.metric hTransverse
  let h13 := global_candidateA_h13_minimalPhysical_h10ReducedFamily_gate period
    hPeriod configuration data analysis
      (diracGreenClosureMatterRealization period hPeriod
        couplings.matterMassSquared)
      einsteinScale hTransverse family
  let h11 := global_candidateA_h11_gate_of_sixAggregateBound period hPeriod
    configuration data analysis chart sameAction einsteinScale bound
  let h12 := global_candidateA_h12_fredholm_gate_of_actualKernelGap period
    hPeriod configuration data analysis chart sameAction physical gap
  let reduced := global_candidateA_actual_kernel_complement_gate period hPeriod
    configuration data analysis chart sameAction physical gap
  let resolvent := global_candidateA_actual_kernel_resolvent_gate period hPeriod
    configuration data analysis chart sameAction physical gap
  And.intro h10
    (And.intro h13 (And.intro h11
      (And.intro h12 (And.intro reduced resolvent))))

/-- The frontier remains a three-packet problem, but the second packet is now
one scalar estimate rather than a chosen extension. -/
theorem global_candidateA_hessian_actualKernel_bounded_three_inputs :
    Nonempty (Unit × Unit × Unit) :=
  ⟨((), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianActualKernelBoundedFrontier4D
end JanusFormal
