import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MatterFiniteGraphSevenPhysicalConst4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalLocalVariationalChart4D

/-! The finite matter chart's seven physical blocks remain constant after local-chart conversion. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12MatterFiniteLocalPhysicalHessianZero4D

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D
open P0EFTJanusProgramPGlobalCandidateAMatterFiniteGraphVariationalChart4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance matterFiniteGraphNormedAddCommGroup (massSquared : Real) :
    NormedAddCommGroup
      (GlobalCandidateAMatterFiniteGraphCore period hPeriod massSquared) :=
  globalCandidateAMatterFiniteGraphCoreNormedAddCommGroup period hPeriod massSquared

local instance matterFiniteGraphNormedSpace (massSquared : Real) :
    NormedSpace Real
      (GlobalCandidateAMatterFiniteGraphCore period hPeriod massSquared) :=
  globalCandidateAMatterFiniteGraphCoreNormedSpace period hPeriod massSquared

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

theorem finiteMatterLocalPhysicalHessian_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (point : GlobalCandidateAMatterFiniteGraphCore period hPeriod
      couplings.matterMassSquared) :
    globalCandidateALocalPhysicalHessian period hPeriod
      (globalCandidateAVariationalChartToLocal period hPeriod
        (globalCandidateAMatterFiniteGraphVariationalChart
          period hPeriod data measure)) point = 0 := by
  let localChart := globalCandidateAVariationalChartToLocal period hPeriod
    (globalCandidateAMatterFiniteGraphVariationalChart period hPeriod data measure)
  letI := localChart.normedAddCommGroup
  letI := localChart.normedSpace
  have hConst :
      fullCoupledPhysicalAction
        (globalCandidateAActionBlocks period hPeriod
          (localChart.family.toActionFamily period hPeriod 0
            localChart.zero_mem_domain) measure) =
        fun _ => fullCoupledPhysicalAction
          (globalCandidateAActionBlocks period hPeriod
            (localChart.family.toActionFamily period hPeriod 0
              localChart.zero_mem_domain) measure) point := by
    simpa only [localChart, globalCandidateAVariationalChartToLocal,
      globalCandidateAMatterFiniteGraphVariationalChart,
      globalCandidateAActionFamilyToLocal_blocks_eq] using
      (P0EFTJanusProgramPT12MatterFiniteGraphSevenPhysicalConst4D.fullCoupledPhysicalAction_eq_const
        period hPeriod data measure point)
  change fderiv Real
    (actionGradient
      (fullCoupledPhysicalAction
        (globalCandidateAActionBlocks period hPeriod
          (localChart.family.toActionFamily period hPeriod 0
            localChart.zero_mem_domain) measure))) point = 0
  rw [hConst]
  change fderiv Real
    (fun state : localChart.Model =>
      fderiv Real (fun _ : localChart.Model =>
        fullCoupledPhysicalAction
          (globalCandidateAActionBlocks period hPeriod
            (localChart.family.toActionFamily period hPeriod 0
              localChart.zero_mem_domain) measure) point) state) point = 0
  simp only [fderiv_const_apply]

end
end P0EFTJanusProgramPT12MatterFiniteLocalPhysicalHessianZero4D
end JanusFormal
