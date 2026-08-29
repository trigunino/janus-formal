import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASixCanonicalChartHessians4D

/-!
# Symmetry of the six canonical Candidate-A chart Hessians

Each of the six non-Robin blocks is the genuine second Frechet derivative of a
`C²` scalar action in the same local Candidate-A chart.  Schwarz symmetry is
therefore derived block by block from the chart regularity certificate and is
then transported to the finite sum and to every dense-core pullback.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateASixCanonicalChartHessianSymmetry4D

set_option autoImplicit false
set_option maxHeartbeats 7200000
set_option synthInstance.maxHeartbeats 3600000

noncomputable section

open Filter Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousExtension4D
open P0EFTJanusProgramPGlobalCandidateASixCanonicalChartHessians4D

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

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

/-- `C²` regularity of each selected action block at the chart base point. -/
theorem globalCandidateALocalNonRobinBlock_contDiffAt_two
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (basePoint : chart.Model)
    (hBasePoint : basePoint ∈ chart.family.domain)
    (block : GlobalCandidateANonRobinPhysicalBlock) :
    ContDiffAt Real 2
      (globalCandidateALocalNonRobinBlockAction period hPeriod chart basePoint
        hBasePoint block)
      basePoint := by
  have hBlocks := chart.blocksC2Within basePoint hBasePoint
  have hWithin : ContDiffWithinAt Real 2
      (globalCandidateALocalNonRobinBlockAction period hPeriod chart basePoint
        hBasePoint block)
      chart.family.domain basePoint := by
    cases block with
    | candidateA =>
        simpa [globalCandidateALocalNonRobinBlockAction,
          globalCandidateALocalActionBlocksAtBase] using hBlocks.candidateA
    | einsteinHilbertPlus =>
        simpa [globalCandidateALocalNonRobinBlockAction,
          globalCandidateALocalActionBlocksAtBase] using
            hBlocks.einsteinHilbertPlus
    | einsteinHilbertMinus =>
        simpa [globalCandidateALocalNonRobinBlockAction,
          globalCandidateALocalActionBlocksAtBase] using
            hBlocks.einsteinHilbertMinus
    | maxwellPlus =>
        simpa [globalCandidateALocalNonRobinBlockAction,
          globalCandidateALocalActionBlocksAtBase] using hBlocks.maxwellPlus
    | maxwellMinus =>
        simpa [globalCandidateALocalNonRobinBlockAction,
          globalCandidateALocalActionBlocksAtBase] using hBlocks.maxwellMinus
    | finiteBV =>
        simpa [globalCandidateALocalNonRobinBlockAction,
          globalCandidateALocalActionBlocksAtBase] using hBlocks.finiteBV
  exact hWithin.contDiffAt chart.isOpen_domain

/-- Schwarz symmetry of one genuine non-Robin second Frechet derivative. -/
theorem globalCandidateALocalNonRobinBlockHessian_symmetric
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (basePoint : chart.Model)
    (hBasePoint : basePoint ∈ chart.family.domain)
    (block : GlobalCandidateANonRobinPhysicalBlock)
    (first second : chart.Model) :
    globalCandidateALocalNonRobinBlockHessian period hPeriod chart basePoint
        hBasePoint block first second =
      globalCandidateALocalNonRobinBlockHessian period hPeriod chart basePoint
        hBasePoint block second first := by
  exact
    (globalCandidateALocalNonRobinBlock_contDiffAt_two period hPeriod chart
      basePoint hBasePoint block).isSymmSndFDeriv first second

/-- Symmetry of the finite six-block chart Hessian. -/
theorem globalCandidateALocalSixCanonicalHessian_symmetric
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (basePoint : chart.Model)
    (hBasePoint : basePoint ∈ chart.family.domain)
    (first second : chart.Model) :
    globalCandidateALocalSixCanonicalHessian period hPeriod chart basePoint
        hBasePoint first second =
      globalCandidateALocalSixCanonicalHessian period hPeriod chart basePoint
        hBasePoint second first := by
  unfold globalCandidateALocalSixCanonicalHessian
  simp only [ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun block _ =>
    globalCandidateALocalNonRobinBlockHessian_symmetric period hPeriod chart
      basePoint hBasePoint block first second

end
end P0EFTJanusProgramPGlobalCandidateASixCanonicalChartHessianSymmetry4D
end JanusFormal
