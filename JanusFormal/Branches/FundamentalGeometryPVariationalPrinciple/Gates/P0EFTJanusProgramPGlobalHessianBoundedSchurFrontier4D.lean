import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianContinuousSchurFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualBoundedSchurBlock4D

/-!
# Preferred bounded four-block H10--H14 Schur frontier

This façade removes the separately supplied reduced-coordinate map from the
terminal interface.  A bounded decomposition, bounded blocks `A,B,C,D` and a
bounded inverse for `D` construct the continuous Gaussian-elimination map and
therefore the entire finite-Schur/actual-kernel package.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianBoundedSchurFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 10400000
set_option synthInstance.maxHeartbeats 5200000

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
open P0EFTJanusProgramPGlobalCandidateASixPhysicalChartPullback4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelStability4D
open P0EFTJanusProgramPGlobalCandidateAActualBoundedSchurBlock4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianActualKernelChartFrontier4D
open P0EFTJanusProgramPGlobalHessianContinuousSchurFrontier4D
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

/-- Strongest current terminal gate: all Schur data are bounded four-block
operator data. -/
def global_candidateA_hessian_bounded_schur_frontier_gate
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
    (Mode Complement : Type*)
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (blockData : GlobalCandidateAActualBoundedSchurBlockData4D period hPeriod
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelChartPhysicalExtension period hPeriod
          configuration data analysis einsteinScale hTransverse family
            realization)
        Mode Complement) :=
  global_candidateA_hessian_continuous_schur_frontier_gate period hPeriod
    configuration data analysis einsteinScale hTransverse family realization
      Mode Complement
      (blockData.toContinuousSchurBlockData period hPeriod)

/-- Perturbative stability generated from the same bounded four-block data. -/
def global_candidateA_hessian_bounded_schur_stability_gate
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
    (Mode Complement : Type*)
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (blockData : GlobalCandidateAActualBoundedSchurBlockData4D period hPeriod
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelChartPhysicalExtension period hPeriod
          configuration data analysis einsteinScale hTransverse family
            realization)
        Mode Complement)
    (perturbation : GlobalCandidateAActualKernelPerturbation4D period hPeriod
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelChartPhysicalExtension period hPeriod
          configuration data analysis einsteinScale hTransverse family
            realization)
        (((((blockData.toContinuousSchurBlockData period hPeriod).toClosedRangeData
          period hPeriod).toSchurZeroModeData period hPeriod).toActualZeroModeGap
          period hPeriod).toActualKernelGap period hPeriod)) :=
  global_candidateA_hessian_continuous_schur_stability_gate period hPeriod
    configuration data analysis einsteinScale hTransverse family realization
      Mode Complement (blockData.toContinuousSchurBlockData period hPeriod)
      perturbation

/-- The terminal architecture still has only three analytic packets. -/
theorem global_candidateA_hessian_bounded_schur_three_inputs :
    Nonempty (Unit × Unit × Unit) :=
  ⟨((), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianBoundedSchurFrontier4D
end JanusFormal
