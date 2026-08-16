import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixNamedModeFrontier4D

/-!
# Terminal H10--H14 frontier with sector-classified actual zero modes

The named-mode frontier already proves that a finite family of ambient vectors
synthesizes exactly the actual augmented Hessian kernel.  This façade attaches
to those same labels the five physical D10-free Candidate-A sectors and
returns the exact sector multiplicity formula together with the complete
H10--H14 output.

No block-diagonal decomposition is assumed: the sector map classifies the
physical origin of each coupled zero mode after the full kernel has been
identified.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixSectorModesFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 14200000
set_option synthInstance.maxHeartbeats 7100000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace BigOperators
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
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixNamedModeFrontier4D
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

/-- Terminal closure plus the exact decomposition of the actual kernel count
among the five physical sectors. -/
def global_candidateA_hessian_canonicalSix_sectorModes_frontier_gate
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
    (ZeroMode : Type*) [Fintype ZeroMode]
    (named : GlobalCandidateAActualNamedKernelCoercivity4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        ZeroMode)
    (classification : CandidateAZeroModeSectorClassification ZeroMode) :=
  let terminal := global_candidateA_hessian_canonicalSix_namedMode_frontier_gate
    period hPeriod configuration data analysis einsteinScale hTransverse family
      chartBound ZeroMode named
  let classified : CandidateASectorClassifiedNamedKernelCoercivity
      (globalCandidateAActualKernelOperator period hPeriod configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family)
          (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
            hPeriod configuration data analysis einsteinScale hTransverse family
              chartBound))
      (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
        configuration data analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family)
          (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
            hPeriod configuration data analysis einsteinScale hTransverse family
              chartBound))
      ZeroMode :=
    { named := named
      classification := classification }
  (terminal, classified.kernel_finrank_eq_sum)

/-- Public count formula for the five D10-free sectors. -/
theorem global_candidateA_hessian_sectorMode_count
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
    (ZeroMode : Type*) [Fintype ZeroMode]
    (named : GlobalCandidateAActualNamedKernelCoercivity4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        ZeroMode)
    (classification : CandidateAZeroModeSectorClassification ZeroMode) :
    Module.finrank Real
        (globalCandidateAActualKernelOperator period hPeriod configuration data
          analysis
            (globalCandidateAActualKernelChart period hPeriod configuration data
              analysis einsteinScale hTransverse family)
            (globalCandidateAActualKernelSameAction period hPeriod configuration
              data analysis einsteinScale hTransverse family)
            (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
              hPeriod configuration data analysis einsteinScale hTransverse
                family chartBound)).ker =
      ∑ sector : CandidateAZeroModeSector,
        classification.multiplicity sector := by
  let classified : CandidateASectorClassifiedNamedKernelCoercivity
      (globalCandidateAActualKernelOperator period hPeriod configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family)
          (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
            hPeriod configuration data analysis einsteinScale hTransverse family
              chartBound))
      (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
        configuration data analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family)
          (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
            hPeriod configuration data analysis einsteinScale hTransverse family
              chartBound))
      ZeroMode :=
    { named := named
      classification := classification }
  exact classified.kernel_finrank_eq_sum

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixSectorModesFrontier4D
end JanusFormal
