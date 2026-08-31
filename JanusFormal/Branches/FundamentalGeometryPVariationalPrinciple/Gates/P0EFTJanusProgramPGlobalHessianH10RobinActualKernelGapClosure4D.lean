import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelResolvent4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryH10Closure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianH10RobinContinuousClosure4D

/-!
# H14 from H10 Robin data, continuous blocks and the actual-kernel gap

The T12 input is reduced to finite-dimensionality of the genuine Hessian
kernel and a positive spectral gap on its orthogonal complement.  The Fredholm
certificate is constructed directly; no parametrix or chosen defect
projection remains in the terminal interface.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianH10RobinActualKernelGapClosure4D

set_option autoImplicit false
set_option maxHeartbeats 4400000
set_option synthInstance.maxHeartbeats 2200000

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
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelResolvent4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryH10Closure4D
open P0EFTJanusProgramPGlobalHessianClosure4D
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

/-- Preferred H14 gate with T12 reduced to the true-kernel spectral gap. -/
def global_candidateA_hessian_h10Robin_actualKernelGap_closure_gate
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
        (globalCandidateAH10RobinChart period hPeriod (measure := measure)
          configuration data analysis family)
        (globalCandidateAH10RobinSameAction period hPeriod (measure := measure)
          configuration data analysis family))
    (gap : GlobalCandidateAActualKernelGap4D period hPeriod configuration data
      analysis
        (globalCandidateAH10RobinChart period hPeriod (measure := measure)
          configuration data analysis family)
        (globalCandidateAH10RobinSameAction period hPeriod (measure := measure)
          configuration data analysis family)
        (globalCandidateAH10RobinContinuousPhysicalExtension period hPeriod
          (measure := measure) configuration data analysis family extensions)) :
    GlobalCandidateAHessianClosureCertificate4D period hPeriod configuration
      data analysis
        (globalCandidateAH10RobinChart period hPeriod (measure := measure)
          configuration data analysis family)
        einsteinScale
        (globalCandidateAH10RobinSameAction period hPeriod (measure := measure)
          configuration data analysis family)
        (globalCandidateAH10RobinContinuousPhysicalExtension period hPeriod
          (measure := measure) configuration data analysis family extensions)
        (globalCandidateAActualKernelFredholmEstimates period hPeriod
          configuration data analysis
          (globalCandidateAH10RobinChart period hPeriod (measure := measure)
            configuration data analysis family)
          (globalCandidateAH10RobinSameAction period hPeriod (measure := measure)
            configuration data analysis family)
          (globalCandidateAH10RobinContinuousPhysicalExtension period hPeriod
            (measure := measure) configuration data analysis family extensions)
          gap) where
  boundary_h10 :=
    (global_candidateA_h10_closure_gate period hPeriod data einsteinScale
      data.plusGravity.metric hBoundaryTransverse).boundaryHessian
  matterLL_h13 :=
    global_candidateA_h13_minimalPhysical_h10RobinFamily_gate period hPeriod
      configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared)
      family
  common_domain_h11 :=
    global_candidateA_h11_common_augmented_domain_gate_of_continuousExtensions
      period hPeriod configuration data analysis
        (globalCandidateAH10RobinChart period hPeriod (measure := measure)
          configuration data analysis family)
        (globalCandidateAH10RobinSameAction period hPeriod (measure := measure)
          configuration data analysis family)
      extensions
  faithful_fredholm_h12 :=
    global_candidateA_h12_fredholm_gate_of_actualKernelGap period hPeriod
      configuration data analysis
        (globalCandidateAH10RobinChart period hPeriod (measure := measure)
          configuration data analysis family)
        (globalCandidateAH10RobinSameAction period hPeriod (measure := measure)
          configuration data analysis family)
        (globalCandidateAH10RobinContinuousPhysicalExtension period hPeriod
          (measure := measure) configuration data analysis family extensions)
      gap

/-- Full preferred output: H14 together with the canonical reduced Green and
the real resolvent on the open spectral gap. -/
def global_candidateA_hessian_h10Robin_actualKernelGap_full_closure_gate
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
        (globalCandidateAH10RobinChart period hPeriod (measure := measure)
          configuration data analysis family)
        (globalCandidateAH10RobinSameAction period hPeriod (measure := measure)
          configuration data analysis family))
    (gap : GlobalCandidateAActualKernelGap4D period hPeriod configuration data
      analysis
        (globalCandidateAH10RobinChart period hPeriod (measure := measure)
          configuration data analysis family)
        (globalCandidateAH10RobinSameAction period hPeriod (measure := measure)
          configuration data analysis family)
        (globalCandidateAH10RobinContinuousPhysicalExtension period hPeriod
          (measure := measure) configuration data analysis family extensions)) :=
  let chart := globalCandidateAH10RobinChart period hPeriod (measure := measure)
    configuration data analysis family
  let sameAction := globalCandidateAH10RobinSameAction period hPeriod
    (measure := measure) configuration data analysis family
  let physical := globalCandidateAH10RobinContinuousPhysicalExtension period
    hPeriod (measure := measure) configuration data analysis family extensions
  let h14 :=
    global_candidateA_hessian_h10Robin_actualKernelGap_closure_gate period
      hPeriod configuration data analysis einsteinScale hBoundaryTransverse
      family extensions gap
  let complement := global_candidateA_actual_kernel_complement_gate period
    hPeriod configuration data analysis chart sameAction physical gap
  let resolvent := global_candidateA_actual_kernel_resolvent_gate period hPeriod
    configuration data analysis chart sameAction physical gap
  And.intro h14 (And.intro complement resolvent)

end
end P0EFTJanusProgramPGlobalHessianH10RobinActualKernelGapClosure4D
end JanusFormal
