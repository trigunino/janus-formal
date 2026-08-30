import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalCanonicalAlgebraicResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalEulerLagrangeMatterFiniteConcreteAtlas4D

/-!
# Concrete continuous residual on the finite SpinC atlas

The exact finite SpinC chart has one nonconstant action block.  Its closed
graph Hessian at a point is therefore a genuine continuous-dual residual whose
evaluation pairing is the full nine-block Euler derivative.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalEulerLagrangeMatterFiniteContinuousResidual4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalEulerLagrangeBlockDecomposition4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeAtlasDescent4D
open P0EFTJanusProgramPGlobalCandidateAMatterFiniteGraphVariationalChart4D
open P0EFTJanusProgramPGlobalEulerLagrangeMatterFiniteConcreteAtlas4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance matterFiniteCoreNormedAddCommGroup (massSquared : Real) :
    NormedAddCommGroup
      (GlobalCandidateAMatterFiniteGraphCore period hPeriod massSquared) :=
  globalCandidateAMatterFiniteGraphCoreNormedAddCommGroup
    period hPeriod massSquared

local instance matterFiniteCoreNormedSpace (massSquared : Real) :
    NormedSpace Real
      (GlobalCandidateAMatterFiniteGraphCore period hPeriod massSquared) :=
  globalCandidateAMatterFiniteGraphCoreNormedSpace
    period hPeriod massSquared

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

attribute [local instance]
  GlobalCandidateAVariationalChart.normedAddCommGroup
  GlobalCandidateAVariationalChart.normedSpace
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

/-- The exact closed-graph Euler functional as a separating residual in the
continuous dual of the finite SpinC core. -/
def globalCandidateAMatterFiniteGraphContinuousResidualRepresentation
    (massSquared : Real)
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod massSquared) :
    SeparatingPDEResidualRepresentation
      (globalCandidateAMatterFiniteGraphHessian
        period hPeriod massSquared core).toLinearMap where
  Residual := GlobalCandidateAMatterFiniteGraphCore
      period hPeriod massSquared →L[Real] Real
  zeroResidual := 0
  residual := globalCandidateAMatterFiniteGraphHessian
    period hPeriod massSquared core
  pairing := fun residual direction ↦ residual direction
  represents := fun _ ↦ rfl
  separates := by
    constructor
    · intro hZero
      apply ContinuousLinearMap.ext
      intro direction
      change globalCandidateAMatterFiniteGraphHessian
        period hPeriod massSquared core direction = 0
      exact hZero direction
    · intro hZero direction
      rw [hZero]
      rfl

/-- The true chart Euler evaluation is exactly the continuous residual
pairing. -/
theorem globalCandidateAMatterFiniteGraphEuler_apply_eq_residualPairing
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (core direction : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod couplings.matterMassSquared) :
    globalEulerLagrangeOperator period hPeriod
        (globalCandidateAMatterFiniteGraphVariationalChart
          period hPeriod data measure) core direction =
      (globalCandidateAMatterFiniteGraphContinuousResidualRepresentation
        period hPeriod couplings.matterMassSquared core).pairing
          (globalCandidateAMatterFiniteGraphContinuousResidualRepresentation
            period hPeriod couplings.matterMassSquared core).residual
          direction := by
  rw [globalCandidateAMatterFiniteGraph_euler_eq period hPeriod data measure
    core]
  rfl

/-- The residual pairing is also the exact sum of all nine action-block
derivatives; the eight spectator blocks vanish because they are constant on
this chart. -/
theorem globalCandidateAMatterFiniteGraphBlockSum_eq_residualPairing
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (core direction : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod couplings.matterMassSquared) :
    fullCoupledEulerBlockSum
        (globalCandidateAActionBlocks period hPeriod
          (globalCandidateAMatterFiniteGraphVariationalChart
            period hPeriod data measure).family measure)
        core direction =
      (globalCandidateAMatterFiniteGraphContinuousResidualRepresentation
        period hPeriod couplings.matterMassSquared core).pairing
          (globalCandidateAMatterFiniteGraphContinuousResidualRepresentation
            period hPeriod couplings.matterMassSquared core).residual
          direction := by
  rw [← globalEulerLagrangeOperator_blockSum_apply period hPeriod
    (globalCandidateAMatterFiniteGraphVariationalChart
      period hPeriod data measure) core direction]
  exact globalCandidateAMatterFiniteGraphEuler_apply_eq_residualPairing
    period hPeriod data measure core direction

/-- Descended criticality on the concrete finite SpinC atlas is precisely
vanishing of this continuous residual. -/
theorem globalCandidateAMatterFiniteGraphAtlas_isEulerCritical_iff_continuousResidual
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod couplings.matterMassSquared) :
    (globalCandidateAMatterFiniteGraphVariationalAtlas period hPeriod data
        measure).IsEulerCritical period hPeriod
      (globalCandidateAMatterFiniteGraphConfiguration period hPeriod
        configuration couplings.matterMassSquared core) ↔
      (globalCandidateAMatterFiniteGraphContinuousResidualRepresentation
          period hPeriod couplings.matterMassSquared core).residual =
        (globalCandidateAMatterFiniteGraphContinuousResidualRepresentation
          period hPeriod couplings.matterMassSquared core).zeroResidual := by
  rw [globalCandidateAMatterFiniteGraphAtlas_isEulerCritical_iff period hPeriod
    data measure core]
  rfl

end
end P0EFTJanusProgramPGlobalEulerLagrangeMatterFiniteContinuousResidual4D
end JanusFormal
