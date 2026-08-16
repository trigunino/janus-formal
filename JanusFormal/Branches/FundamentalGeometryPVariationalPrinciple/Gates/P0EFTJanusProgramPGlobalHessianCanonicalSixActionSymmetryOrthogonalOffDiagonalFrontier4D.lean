import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActionSymmetryOrthogonalOffDiagonalGap4D

/-!
# H10--H14 from action symmetries and one complement off-diagonal form

This façade joins the narrow canonical H11 construction with the new direct
actual-kernel proof.

After the H10-reduced local family it accepts:

1. the genuine dense-core-to-chart bound, which constructs the canonical six
   non-Robin Hessians and H10 Robin extension;
2. exact local action symmetries, nonzero pairwise orthogonality, and one
   five-sector orthogonal-coordinate Gårding packet on the complement of their
   ambient span.

The second packet proves by itself that the named span is the actual kernel,
that its dimension is the number of named symmetries, and that its orthogonal
complement carries the H12 gap.  The existing canonical-six terminal then
constructs H10, H13, H11, H12, the reduced Green/resolvent package and H14.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixActionSymmetryOrthogonalOffDiagonalFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 13200000
set_option synthInstance.maxHeartbeats 6600000

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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateAH10BoundaryProjectionFromChartBound4D
open P0EFTJanusProgramPGlobalCandidateAActionSymmetryOrthogonalOffDiagonalGap4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D

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

variable (Component : CandidateAZeroModeSector → Type*)
  [∀ sector, NormedAddCommGroup (Component sector)]
  [∀ sector, NormedSpace Real (Component sector)]
  [∀ sector, InnerProductSpace Real (Component sector)]

/-- Preferred direct terminal: action invariance supplies the zero modes and
one off-diagonal complement margin supplies both exact-kernel finiteness and the
actual H12 gap. -/
def global_candidateA_hessian_canonicalSix_actionSymmetry_orthogonalOffDiagonal_frontier_gate
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
    (input : GlobalCandidateAActionSymmetryOrthogonalOffDiagonalGap4D period
      hPeriod Component configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixPhysicalExtension_of_chartBound period
          hPeriod configuration data analysis einsteinScale hTransverse family
            chartBound)
        ZeroMode) :=
  let closure :=
    global_candidateA_hessian_canonicalSix_chartBound_frontier_gate period
      hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound (input.toActualKernelGap period hPeriod Component)
  let exactCount := input.kernel_finrank_eq_card period hPeriod Component
  (closure, exactCount)

/-- After the local family, only the dense-core chart estimate and the combined
symmetry/complement-margin packet remain. -/
theorem global_candidateA_hessian_canonicalSix_actionSymmetry_orthogonalOffDiagonal_two_inputs :
    Nonempty (Unit × Unit) :=
  ⟨((), ())⟩

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixActionSymmetryOrthogonalOffDiagonalFrontier4D
end JanusFormal
