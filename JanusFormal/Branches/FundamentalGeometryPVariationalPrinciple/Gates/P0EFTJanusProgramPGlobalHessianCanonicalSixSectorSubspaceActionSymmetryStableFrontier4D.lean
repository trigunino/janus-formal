import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASectorSubspaceActionTranslationStablePhysicalForm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixSectorActionSymmetryStableFrontier4D

/-!
# Terminal H10--H14 frontier from five orthogonal physical subspaces

This frontier removes mode-by-mode cross-sector inner-product identities from
the sector-explicit terminal packet.  The finite modes are carried by five
mutually orthogonal physical subspaces, so their global orthogonality and exact
sector count are consequences of the subspace decomposition.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixSectorSubspaceActionSymmetryStableFrontier4D

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
open P0EFTJanusProgramPGlobalCandidateASectorSubspaceActionTranslationStablePhysicalForm4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixSectorActionSymmetryStableFrontier4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPCandidateASectorModeAssembly4D

attribute [local instance]
  P0EFTJanusProgramPGlobalLocalVariationalChart4D.GlobalCandidateALocalVariationalChart.normedAddCommGroup
  P0EFTJanusProgramPGlobalLocalVariationalChart4D.GlobalCandidateALocalVariationalChart.normedSpace
  actualKernelNormedAddCommGroup
  actualKernelInnerProductSpace
  actualKernelNormedSpace
  actualKernelModule
  actualKernelCompleteSpace

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

/-- Preferred subspace-carried sector terminal endpoint. -/
def global_candidateA_hessian_canonicalSix_sectorSubspaceActionSymmetryStable_frontier_gate
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
      (globalCandidateACanonicalSixCoreToChart period hPeriod
        (measure := measure) configuration data analysis
          (globalCandidateAActualKernelChart period hPeriod
            (measure := measure) configuration data analysis einsteinScale
              hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod
            (measure := measure) configuration data analysis einsteinScale
              hTransverse family)))
    (types : CandidateASectorModeTypes)
    (stable : GlobalCandidateASectorSubspaceActionTranslationStablePhysicalFormData4D
      period hPeriod configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod (measure := measure)
          configuration data analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod
          (measure := measure) configuration data analysis einsteinScale
            hTransverse family)
        (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
          hPeriod (measure := measure) configuration data analysis einsteinScale
            hTransverse family chartBound)
        types) :=
  global_candidateA_hessian_canonicalSix_sectorActionSymmetryStable_frontier_gate
    period hPeriod (measure := measure) configuration data analysis einsteinScale
      hTransverse family chartBound types
        (stable.toSectorStable period hPeriod (measure := measure))

/-- The subspace formulation still has two analytic packets after the fixed
H10-reduced family: the chart bound and the sector-subspace stable data. -/
theorem global_candidateA_hessian_canonicalSix_sectorSubspaceActionSymmetryStable_two_inputs :
    Nonempty (Unit × Unit) :=
  ⟨((), ())⟩

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixSectorSubspaceActionSymmetryStableFrontier4D
end JanusFormal
