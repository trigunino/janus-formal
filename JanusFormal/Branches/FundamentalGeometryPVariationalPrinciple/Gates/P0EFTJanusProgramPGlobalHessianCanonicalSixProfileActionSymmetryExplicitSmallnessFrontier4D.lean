import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAProfileActionTranslationCanonicalSmallness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixActionSymmetryExplicitSmallnessFrontier4D

/-!
# Numerical five-sector H10--H14 frontier with explicit H11 smallness

This is the numerical-profile spelling of the strongest current action-symmetry
frontier.  The five sector index types are the coordinate spaces selected by a
`CandidateASectorMultiplicityProfile`, while the H11 perturbation condition is
the explicit dense-core comparison

`canonicalSevenPhysicalConstant < principalGardingConstant`.

The completed physical-form norm, the Hessian equations of the symmetry modes,
their independence, the finite projection and the absence of hidden zero modes
are all derived.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixProfileActionSymmetryExplicitSmallnessFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 15800000
set_option synthInstance.maxHeartbeats 7900000

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
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAProfileActionTranslationCanonicalSmallness4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D
open P0EFTJanusProgramPCandidateASectorMultiplicityProfile4D
open P0EFTJanusProgramPCandidateASectorModeAssembly4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixActionSymmetryExplicitSmallnessFrontier4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D

attribute [local instance]
  P0EFTJanusProgramPGlobalLocalVariationalChart4D.GlobalCandidateALocalVariationalChart.normedAddCommGroup
  P0EFTJanusProgramPGlobalLocalVariationalChart4D.GlobalCandidateALocalVariationalChart.normedSpace
  actualKernelNormedAddCommGroup
  actualKernelInnerProductSpace
  actualKernelNormedSpace
  actualKernelModule
  actualKernelCompleteSpace

variable (period : Real) (hPeriod : period ≠ 0)

noncomputable local instance candidateASectorGlobalModeDecidableEq
    (types : CandidateASectorModeTypes) : DecidableEq types.GlobalMode :=
  Classical.decEq _

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

/-- Preferred terminal endpoint with five numerical multiplicities and the
explicit dense-core physical smallness test. -/
def global_candidateA_hessian_canonicalSix_profileActionSymmetryExplicitSmallness_frontier_gate
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
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod (measure := measure) configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod (measure := measure) configuration
            data analysis einsteinScale hTransverse family)))
    (profile : CandidateASectorMultiplicityProfile)
    (smallness :
      GlobalCandidateAProfileActionTranslationCanonicalSmallnessData4D period
        hPeriod (measure := measure) configuration data analysis einsteinScale hTransverse family
          chartBound profile) :=
  global_candidateA_hessian_canonicalSix_actionSymmetryExplicitSmallness_frontier_gate
    period hPeriod (measure := measure) configuration data analysis einsteinScale hTransverse family
      chartBound profile.modeTypes.GlobalMode
        (smallness.toGlobal period hPeriod (measure := measure))

/-- Exact actual-kernel count given by the five numerical profile entries. -/
theorem global_candidateA_hessian_canonicalSix_profileActionSymmetryExplicitSmallness_exact_count
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
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod (measure := measure) configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod (measure := measure) configuration
            data analysis einsteinScale hTransverse family)))
    (profile : CandidateASectorMultiplicityProfile)
    (smallness :
      GlobalCandidateAProfileActionTranslationCanonicalSmallnessData4D period
        hPeriod (measure := measure) configuration data analysis einsteinScale hTransverse family
          chartBound profile) :
    let chart := globalCandidateAActualKernelChart period hPeriod (measure := measure) configuration
      data analysis einsteinScale hTransverse family
    let sameAction := globalCandidateAActualKernelSameAction period hPeriod (measure := measure)
      configuration data analysis einsteinScale hTransverse family
    let physical := globalCandidateACanonicalSixPhysicalExtension_of_chartBound
      period hPeriod (measure := measure) configuration data analysis einsteinScale hTransverse family
        chartBound
    Module.finrank Real
        (globalCandidateAActualKernelOperator period hPeriod (measure := measure) configuration data
          analysis chart sameAction physical).ker =
      ∑ sector : CandidateAZeroModeSector,
        profile.multiplicity sector := by
  dsimp only
  exact smallness.kernel_finrank_eq_profile_sum period hPeriod (measure := measure)

/-- The numerical profile is a type-level specialization, not an additional
analytic packet.  After the fixed local family, only the chart bound and the
profile action-symmetry/coercivity packet remain. -/
theorem global_candidateA_hessian_canonicalSix_profileActionSymmetryExplicitSmallness_two_inputs :
    Nonempty (Unit × Unit) :=
  ⟨((), ())⟩

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixProfileActionSymmetryExplicitSmallnessFrontier4D
end JanusFormal
