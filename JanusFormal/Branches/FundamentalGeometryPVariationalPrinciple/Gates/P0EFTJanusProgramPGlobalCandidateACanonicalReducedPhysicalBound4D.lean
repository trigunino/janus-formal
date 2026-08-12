import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAReducedCanonicalEnergies4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateACanonicalPhysicalSmallness4D

/-!
# Canonical dense-core H11 bound on the actual kernel complement

The seven physical blocks are extended from one bounded smooth-core form.  The
same core constant controls the completed form norm and hence, after canonical
restriction, the physical quadratic energy on `(ker H_actual)ᗮ`.

This file records that final transport for the preferred H10/H11 chart-bound
construction.  The H12 smallness comparison can therefore use the explicit
constant already computed from the Robin block and the six genuine local
Candidate-A Hessians; no independent completed-space bound is requested.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateACanonicalReducedPhysicalBound4D

set_option autoImplicit false
set_option maxHeartbeats 7800000
set_option synthInstance.maxHeartbeats 3900000

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
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateACanonicalPhysicalSmallness4D
open P0EFTJanusProgramPGlobalCandidateAReducedCanonicalEnergies4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusMappingTorusGlobalLLVariation4D

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

/-- Any seven-block smooth-core bound produces the corresponding reduced H11
energy majorant. -/
def globalCandidateAReducedPhysicalFormBound_of_coreBound
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (sameAction : ProgramPGlobalMinimalPhysicalLocalMatterLLSameActionBridge4D
      period hPeriod configuration data analysis chart)
    (bound : GlobalCandidateASevenPhysicalCoreBound4D period hPeriod
      configuration data analysis chart sameAction) :
    GlobalCandidateAReducedPhysicalFormBound4D period hPeriod configuration data
      analysis chart sameAction
        (globalCandidateASevenPhysicalCommonDomainExtension_of_bound period hPeriod
          configuration data analysis chart sameAction bound) where
  constant := bound.constant
  constant_nonneg := bound.constant_nonneg
  form_norm_le :=
    globalCandidateASevenPhysicalExtension_form_opNorm_le period hPeriod
      configuration data analysis chart sameAction bound

/-- Preferred H10/H11 specialization: the chart-bound construction carries its
explicit seven-block constant all the way to the actual complement. -/
def globalCandidateACanonicalReducedPhysicalFormBound_of_chartBound
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
            data analysis einsteinScale hTransverse family))) :
    GlobalCandidateAReducedPhysicalFormBound4D period hPeriod configuration data
      analysis
      (globalCandidateAActualKernelChart period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      (globalCandidateAActualKernelSameAction period hPeriod configuration data
        analysis einsteinScale hTransverse family)
      (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period hPeriod
        configuration data analysis einsteinScale hTransverse family chartBound) where
  constant := globalCandidateACanonicalSevenPhysicalConstant period hPeriod
    configuration data analysis einsteinScale hTransverse family chartBound
  constant_nonneg :=
    (globalCandidateACanonicalSevenPhysicalCoreBound_of_chartBound period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
      ).constant_nonneg
  form_norm_le :=
    globalCandidateACanonicalSixPhysicalExtension_form_opNorm_le period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound

/-- Explicit reduced quadratic estimate generated by the typed core-to-chart
bound. -/
theorem globalCandidateACanonicalReducedPhysicalEnergy_bound
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
    (vector : SelfAdjointKernelComplement
      (globalCandidateAActualKernelOperator period hPeriod configuration data
        analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period hPeriod
          configuration data analysis einsteinScale hTransverse family
            chartBound))) :
    |globalCandidateAReducedPhysicalEnergy period hPeriod configuration data
        analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period hPeriod
          configuration data analysis einsteinScale hTransverse family chartBound)
        vector| ≤
      globalCandidateACanonicalSevenPhysicalConstant period hPeriod configuration
          data analysis einsteinScale hTransverse family chartBound *
        ‖vector‖ ^ 2 :=
  (globalCandidateACanonicalReducedPhysicalFormBound_of_chartBound period hPeriod
    configuration data analysis einsteinScale hTransverse family chartBound
    ).energy_bound vector

/-- Public canonical reduced-H11 checkpoint. -/
theorem global_candidateA_canonical_reduced_physical_bound_gate
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
            data analysis einsteinScale hTransverse family))) :
    let reducedBound :=
      globalCandidateACanonicalReducedPhysicalFormBound_of_chartBound period
        hPeriod configuration data analysis einsteinScale hTransverse family
          chartBound
    reducedBound.constant =
        globalCandidateACanonicalSevenPhysicalConstant period hPeriod
          configuration data analysis einsteinScale hTransverse family chartBound ∧
      (∀ vector,
        |globalCandidateAReducedPhysicalEnergy period hPeriod configuration data
            analysis
            (globalCandidateAActualKernelChart period hPeriod configuration data
              analysis einsteinScale hTransverse family)
            (globalCandidateAActualKernelSameAction period hPeriod configuration
              data analysis einsteinScale hTransverse family)
            (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
              hPeriod configuration data analysis einsteinScale hTransverse family
                chartBound) vector| ≤
          reducedBound.constant * ‖vector‖ ^ 2) := by
  dsimp only
  exact ⟨rfl,
    (globalCandidateACanonicalReducedPhysicalFormBound_of_chartBound period
      hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound).energy_bound⟩

end
end P0EFTJanusProgramPGlobalCandidateACanonicalReducedPhysicalBound4D
end JanusFormal
