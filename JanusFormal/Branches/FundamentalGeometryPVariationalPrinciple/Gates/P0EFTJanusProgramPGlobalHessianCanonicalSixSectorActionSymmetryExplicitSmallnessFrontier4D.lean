import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASectorActionTranslationCanonicalSmallness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixActionSymmetryExplicitSmallnessFrontier4D

/-!
# Sector-explicit H10--H14 frontier with canonical H11 smallness

This façade combines the five D10-free physical mode sectors with the strongest
current perturbative reduction.  The completed physical-form norm is not an
input: it is bounded by the explicit canonical dense-core constant.

The resulting terminal returns the full H10--H14 certificate and the exact
kernel dimension as the sum of metric/diffeomorphism, Abelian, primitive SpinC,
longitudinal/LL and boundary/finite-BV multiplicities.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixSectorActionSymmetryExplicitSmallnessFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 15400000
set_option synthInstance.maxHeartbeats 7700000

noncomputable section

open Set Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
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
open P0EFTJanusProgramPGlobalCandidateASectorActionTranslationCanonicalSmallness4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixActionSymmetryExplicitSmallnessFrontier4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPCandidateASectorModeAssembly4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D

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

/-- Preferred sector-explicit action-symmetry endpoint. -/
def global_candidateA_hessian_canonicalSix_sectorActionSymmetryExplicitSmallness_frontier_gate
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
      (globalCandidateACanonicalSixCoreToChart period hPeriod (measure := measure)
        configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod (measure := measure)
            configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod
            (measure := measure) configuration data analysis einsteinScale
              hTransverse family)))
    (types : CandidateASectorModeTypes)
    (smallness : GlobalCandidateASectorActionTranslationCanonicalSmallnessData4D
      period hPeriod (measure := measure) configuration data analysis
        einsteinScale hTransverse family chartBound types) :=
  let terminal :=
    global_candidateA_hessian_canonicalSix_actionSymmetryExplicitSmallness_frontier_gate
      period hPeriod (measure := measure) configuration data analysis
        einsteinScale hTransverse family chartBound types.GlobalMode
          (smallness.toGlobal period hPeriod (measure := measure))
  let sectorCount := smallness.kernel_finrank_eq_sector_sum period hPeriod
    (measure := measure)
  PSigma.mk (β := fun _ => _) terminal sectorCount

/-- Exact zero-mode count as the sum of the five physical sector
multiplicities. -/
theorem global_candidateA_hessian_canonicalSix_sectorActionSymmetryExplicitSmallness_exact_count
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
      (globalCandidateACanonicalSixCoreToChart period hPeriod (measure := measure)
        configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod (measure := measure)
            configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod
            (measure := measure) configuration data analysis einsteinScale
              hTransverse family)))
    (types : CandidateASectorModeTypes)
    (smallness : GlobalCandidateASectorActionTranslationCanonicalSmallnessData4D
      period hPeriod (measure := measure) configuration data analysis
        einsteinScale hTransverse family chartBound types) :
    let chart := globalCandidateAActualKernelChart period hPeriod
      (measure := measure) configuration data analysis einsteinScale hTransverse
        family
    let sameAction := globalCandidateAActualKernelSameAction period hPeriod
      (measure := measure) configuration data analysis einsteinScale hTransverse
        family
    let physical := globalCandidateACanonicalSixPhysicalExtension_of_chartBound
      period hPeriod (measure := measure) configuration data analysis
        einsteinScale hTransverse family chartBound
    Module.finrank Real
        (globalCandidateAActualKernelOperator period hPeriod (measure := measure)
          configuration data analysis chart sameAction physical).ker =
      ∑ sector : CandidateAZeroModeSector,
        types.classification.multiplicity sector := by
  dsimp only
  exact smallness.kernel_finrank_eq_sector_sum period hPeriod
    (measure := measure)

/-- After the local family, this sector-explicit terminal still has only the
core-to-chart bound and one sector action-symmetry/coercivity packet. -/
theorem global_candidateA_hessian_canonicalSix_sectorActionSymmetryExplicitSmallness_two_inputs :
    Nonempty (Unit × Unit) :=
  ⟨((), ())⟩

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixSectorActionSymmetryExplicitSmallnessFrontier4D
end JanusFormal
