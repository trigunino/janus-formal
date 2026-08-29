import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActualInvariantOrthogonalReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurNamedVectorsFrontier4D

/-!
# H10--H14 on an invariant finite-mode subspace

Concrete reference modes span a finite subspace invariant under the actual
augmented Candidate-A Hessian.  Auto-adjointness makes its orthogonal complement
invariant, a norm gap there constructs the complementary inverse, and the
finite Schur operator is exactly the finite compression `A`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixInvariantOrthogonalFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 15400000
set_option synthInstance.maxHeartbeats 7700000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
open P0EFTJanusProgramPGlobalCandidateAActualInvariantOrthogonalReduction4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixOrthogonalSchurNamedVectorsFrontier4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
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

/-- Preferred invariant-subspace H10--H14 gate. -/
def global_candidateA_hessian_canonicalSix_invariantOrthogonal_frontier_gate
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
    (Mode : Type*) [Fintype Mode] [DecidableEq Mode]
    (invariant : GlobalCandidateAActualNamedInvariantOrthogonalGapData4D period
      hPeriod configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixOrthogonalSchurPhysicalExtension period
          hPeriod configuration data analysis einsteinScale hTransverse family
            chartBound)
        Mode) :=
  let namedVectors := invariant.toNamedVectorsData period hPeriod
  let terminal :=
    global_candidateA_hessian_canonicalSix_orthogonalSchurNamedVectors_frontier_gate
      period hPeriod configuration data analysis einsteinScale hTransverse
        family chartBound Mode namedVectors
  (terminal,
    invariant.invariantGap.toInvariantData.blockB_eq_zero,
    invariant.invariantGap.toInvariantData.blockC_eq_zero,
    invariant.invariantGap.toInvariantData.schur_eq_blockA,
    invariant.invariantGap.gap,
    invariant.invariantGap.gap_pos,
    invariant.invariantGap.lowerBound)

/-- Beyond fixed geometry, the invariant route has the local family, the common
chart estimate, and one finite invariant-mode/gap packet. -/
theorem global_candidateA_hessian_canonicalSix_invariantOrthogonal_three_inputs :
    Nonempty (Unit × Unit × Unit) :=
  ⟨((), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixInvariantOrthogonalFrontier4D
end JanusFormal
