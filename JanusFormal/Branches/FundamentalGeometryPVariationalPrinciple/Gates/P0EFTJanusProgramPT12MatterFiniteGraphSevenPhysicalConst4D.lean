import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMatterFiniteGraphVariationalChart4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D

/-! The seven physical spectator blocks on the finite matter graph chart. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12MatterFiniteGraphSevenPhysicalConst4D

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D
open P0EFTJanusProgramPGlobalCandidateAMatterFiniteGraphVariationalChart4D

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

/-- The seven physical blocks are spectators on the matter-only finite graph core. -/
theorem fullCoupledPhysicalAction_eq_const
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (point : GlobalCandidateAMatterFiniteGraphCore period hPeriod
      couplings.matterMassSquared) :
    fullCoupledPhysicalAction
        (globalCandidateAActionBlocks period hPeriod
          (globalCandidateAMatterFiniteGraphActionFamily period hPeriod
            couplings.matterMassSquared data) measure) =
      fun _ => fullCoupledPhysicalAction
        (globalCandidateAActionBlocks period hPeriod
          (globalCandidateAMatterFiniteGraphActionFamily period hPeriod
            couplings.matterMassSquared data) measure) point := by
  funext state
  rfl

/-- Consequently its Hessian vanishes on the finite matter graph chart. -/
theorem fullCoupledPhysicalAction_hessian_eq_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (point : GlobalCandidateAMatterFiniteGraphCore period hPeriod
      couplings.matterMassSquared) :
    fderiv Real
      (actionGradient
        (fullCoupledPhysicalAction
          (globalCandidateAActionBlocks period hPeriod
            (globalCandidateAMatterFiniteGraphActionFamily period hPeriod
              couplings.matterMassSquared data) measure))) point = 0 := by
  rw [fullCoupledPhysicalAction_eq_const period hPeriod data measure point]
  change fderiv Real
    (fun state : GlobalCandidateAMatterFiniteGraphCore period hPeriod
      couplings.matterMassSquared =>
      fderiv Real (fun _ : GlobalCandidateAMatterFiniteGraphCore period hPeriod
        couplings.matterMassSquared =>
        fullCoupledPhysicalAction
          (globalCandidateAActionBlocks period hPeriod
            (globalCandidateAMatterFiniteGraphActionFamily period hPeriod
              couplings.matterMassSquared data) measure) point) state) point = 0
  simp only [fderiv_const_apply]

end
end P0EFTJanusProgramPT12MatterFiniteGraphSevenPhysicalConst4D
end JanusFormal
