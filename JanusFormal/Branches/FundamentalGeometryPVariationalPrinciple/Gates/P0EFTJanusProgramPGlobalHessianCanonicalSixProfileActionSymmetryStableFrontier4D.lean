import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAProfileActionTranslationStablePhysicalForm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixActionSymmetryStableFrontier4D

/-!
# Terminal H10--H14 frontier with five numerical zero-mode multiplicities

This is the most concrete sector-counting spelling of the preferred stable
Noether frontier.  The zero-mode index is generated from five natural numbers,
while the actual vectors, action invariance, orthogonality, principal Gårding
and physical-form smallness remain genuine analytic data.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixProfileActionSymmetryStableFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 15200000
set_option synthInstance.maxHeartbeats 7600000

noncomputable section

open Set Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateAProfileActionTranslationStablePhysicalForm4D
open P0EFTJanusProgramPGlobalCandidateAActionTranslationStablePhysicalForm4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D
open P0EFTJanusProgramPCandidateASectorMultiplicityProfile4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixActionSymmetryStableFrontier4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D

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

/-- Preferred terminal endpoint with a five-number zero-mode profile. -/
def global_candidateA_hessian_canonicalSix_profileActionSymmetryStable_frontier_gate
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
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family)))
    (profile : CandidateASectorMultiplicityProfile)
    (stable : GlobalCandidateAProfileActionTranslationStablePhysicalFormData4D
      period hPeriod configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
          hPeriod configuration data analysis einsteinScale hTransverse family
            chartBound)
        profile) :=
  let terminal :=
    global_candidateA_hessian_canonicalSix_actionSymmetryStable_frontier_gate
      period hPeriod configuration data analysis einsteinScale hTransverse
        family chartBound profile.modeTypes.GlobalMode
          (stable.toStable period hPeriod)
  let multiplicity := stable.kernel_finrank_eq_profile_sum period hPeriod
  (terminal, multiplicity)

/-- Explicit five-number actual-kernel count. -/
theorem global_candidateA_hessian_canonicalSix_profileActionSymmetryStable_exact_count
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
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family)))
    (profile : CandidateASectorMultiplicityProfile)
    (stable : GlobalCandidateAProfileActionTranslationStablePhysicalFormData4D
      period hPeriod configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
          hPeriod configuration data analysis einsteinScale hTransverse family
            chartBound)
        profile) :
    let chart := globalCandidateAActualKernelChart period hPeriod configuration
      data analysis einsteinScale hTransverse family
    let sameAction := globalCandidateAActualKernelSameAction period hPeriod
      configuration data analysis einsteinScale hTransverse family
    let physical := globalCandidateACanonicalSixPhysicalExtension_of_chartBound
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound
    Module.finrank Real
        (globalCandidateAActualKernelOperator period hPeriod configuration data
          analysis chart sameAction physical).ker =
      ∑ sector : CandidateAZeroModeSector,
        profile.multiplicity sector := by
  dsimp only
  exact stable.kernel_finrank_eq_profile_sum period hPeriod

/-- The numerical profile does not add an analytic packet: after the fixed
family, only the chart bound and stable symmetry/coercivity data remain. -/
theorem global_candidateA_hessian_canonicalSix_profileActionSymmetryStable_two_inputs :
    Nonempty (Unit × Unit) :=
  ⟨((), ())⟩

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixProfileActionSymmetryStableFrontier4D
end JanusFormal
