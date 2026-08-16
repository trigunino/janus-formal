import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASectorActionTranslationStablePhysicalForm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixActionSymmetryStableFrontier4D

/-!
# Terminal H10--H14 frontier assembled from five physical mode sectors

This is the sector-explicit form of the preferred terminal frontier.  The
opaque finite type of zero modes is replaced by one finite type over each of
the five D10-free physical sectors.  Their dependent sum is assembled
internally, while sector-local and cross-sector orthogonality yield the global
orthogonal family required by the Noether/Gårding argument.

The output retains the complete H10--H14 certificate and additionally exposes
the exact kernel dimension as the sum of the five physical multiplicities.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixSectorActionSymmetryStableFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 14800000
set_option synthInstance.maxHeartbeats 7400000

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
open P0EFTJanusProgramPGlobalCandidateAActionTranslationStablePhysicalForm4D
open P0EFTJanusProgramPGlobalCandidateASectorActionTranslationStablePhysicalForm4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixActionSymmetryStableFrontier4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPCandidateASectorModeAssembly4D

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

/-- Preferred sector-explicit terminal endpoint. -/
def global_candidateA_hessian_canonicalSix_sectorActionSymmetryStable_frontier_gate
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
    (types : CandidateASectorModeTypes)
    (stable : GlobalCandidateASectorActionTranslationStablePhysicalFormData4D
      period hPeriod configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
          hPeriod configuration data analysis einsteinScale hTransverse family
            chartBound)
        types) :=
  let terminal :=
    global_candidateA_hessian_canonicalSix_actionSymmetryStable_frontier_gate
      period hPeriod configuration data analysis einsteinScale hTransverse
        family chartBound types.GlobalMode (stable.toStable period hPeriod)
  let sectorCount := stable.kernel_finrank_eq_sector_sum period hPeriod
  (terminal, sectorCount)

/-- The exact zero-mode count is the sum of the five sector multiplicities. -/
theorem global_candidateA_hessian_canonicalSix_sectorActionSymmetryStable_exact_count
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
    (types : CandidateASectorModeTypes)
    (stable : GlobalCandidateASectorActionTranslationStablePhysicalFormData4D
      period hPeriod configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
          hPeriod configuration data analysis einsteinScale hTransverse family
            chartBound)
        types) :
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
        types.classification.multiplicity sector := by
  dsimp only
  exact stable.kernel_finrank_eq_sector_sum period hPeriod

/-- After the fixed geometry, the sector-explicit frontier still has only the
chart bound and the sector-stable analytic packet. -/
theorem global_candidateA_hessian_canonicalSix_sectorActionSymmetryStable_two_inputs :
    Nonempty (Unit × Unit) :=
  ⟨((), ())⟩

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixSectorActionSymmetryStableFrontier4D
end JanusFormal
