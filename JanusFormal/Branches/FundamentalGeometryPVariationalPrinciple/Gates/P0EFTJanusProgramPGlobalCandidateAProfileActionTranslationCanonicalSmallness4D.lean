import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateASectorMultiplicityProfile4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASectorActionTranslationCanonicalSmallness4D

/-!
# Numerical five-sector profile with canonical H11 smallness

The sector-explicit action-symmetry packet already replaces the abstract norm
condition on the completed H11 form by the scalar dense-core comparison

`canonicalSevenPhysicalConstant < principalGardingConstant`.

This file specializes its five sector index types to the canonical coordinate
models `Fin n` selected by a numerical multiplicity profile.  The zero-mode
count is consequently stated directly as the sum of five natural numbers,
without reintroducing a chosen basis of the full Hessian kernel.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAProfileActionTranslationCanonicalSmallness4D

set_option autoImplicit false
set_option maxHeartbeats 9200000
set_option synthInstance.maxHeartbeats 4600000

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
open P0EFTJanusProgramPGlobalCandidateASectorActionTranslationCanonicalSmallness4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D
open P0EFTJanusProgramPCandidateASectorMultiplicityProfile4D
open P0EFTJanusProgramPCandidateASectorModeAssembly4D
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

/-- Numerical-profile spelling of the sector packet with explicit dense-core
H11 smallness. -/
abbrev GlobalCandidateAProfileActionTranslationCanonicalSmallnessData4D
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
    (profile : CandidateASectorMultiplicityProfile) :=
  GlobalCandidateASectorActionTranslationCanonicalSmallnessData4D period hPeriod
    configuration data analysis einsteinScale hTransverse family chartBound
      profile.modeTypes

/-- Exact actual-kernel count expressed directly by the five numerical
multiplicities. -/
theorem GlobalCandidateAProfileActionTranslationCanonicalSmallnessData4D.kernel_finrank_eq_profile_sum
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family))}
    {profile : CandidateASectorMultiplicityProfile}
    (input : GlobalCandidateAProfileActionTranslationCanonicalSmallnessData4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound profile) :
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
  rw [input.kernel_finrank_eq_sector_sum period hPeriod]
  apply Finset.sum_congr rfl
  intro sector _
  exact profile.classification_multiplicity sector

/-- Public numerical-profile checkpoint for the explicit-smallness route. -/
theorem global_candidateA_profile_action_translation_canonical_smallness_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family))}
    {profile : CandidateASectorMultiplicityProfile}
    (input : GlobalCandidateAProfileActionTranslationCanonicalSmallnessData4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound profile) :
    GlobalCandidateAActualKernelGap4D period hPeriod configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
          hPeriod configuration data analysis einsteinScale hTransverse family
            chartBound) ∧
      Module.finrank Real
          (globalCandidateAActualKernelOperator period hPeriod configuration data
            analysis
              (globalCandidateAActualKernelChart period hPeriod configuration data
                analysis einsteinScale hTransverse family)
              (globalCandidateAActualKernelSameAction period hPeriod
                configuration data analysis einsteinScale hTransverse family)
              (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
                hPeriod configuration data analysis einsteinScale hTransverse
                  family chartBound)).ker =
        ∑ sector : CandidateAZeroModeSector,
          profile.multiplicity sector :=
  ⟨((input.toGlobal period hPeriod).toStable period hPeriod).toNamedGarding.toGap
      period hPeriod,
    input.kernel_finrank_eq_profile_sum period hPeriod⟩

end
end P0EFTJanusProgramPGlobalCandidateAProfileActionTranslationCanonicalSmallness4D
end JanusFormal
