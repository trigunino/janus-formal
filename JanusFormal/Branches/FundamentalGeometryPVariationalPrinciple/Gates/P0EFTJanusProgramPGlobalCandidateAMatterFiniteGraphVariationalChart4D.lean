import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianFrontier4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D

/-!
# Candidate-A finite matter graph variational chart

The finite primitive SpinC graph core is realized as a genuine nonconstant
variational chart of the already assembled covariant Candidate-A action.
Every non-matter field is fixed.  Consequently the exact chart Hessian is the
pullback of the closed matter graph Hessian, without an extra action or axiom.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMatterFiniteGraphVariationalChart4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D
open P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalHessianFrontier4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D

universe u

variable (period : Real) (hPeriod : period ≠ 0)

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

/-- The algebraic finite matter range equipped with the inherited graph norm. -/
def GlobalCandidateAMatterFiniteGraphCore (massSquared : Real) : Type :=
  LinearMap.range
    (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap
      period hPeriod massSquared)

@[implicit_reducible]
def globalCandidateAMatterFiniteGraphCoreNormedAddCommGroup
    (massSquared : Real) :
    NormedAddCommGroup
      (GlobalCandidateAMatterFiniteGraphCore
        period hPeriod massSquared) := by
  unfold GlobalCandidateAMatterFiniteGraphCore
  infer_instance

local instance (priority := 10000)
    globalCandidateAMatterFiniteGraphCoreNormedAddCommGroupInstance
    (massSquared : Real) :
    NormedAddCommGroup
      (GlobalCandidateAMatterFiniteGraphCore
        period hPeriod massSquared) :=
  globalCandidateAMatterFiniteGraphCoreNormedAddCommGroup
    period hPeriod massSquared

@[implicit_reducible]
def globalCandidateAMatterFiniteGraphCoreNormedSpace
    (massSquared : Real) :
    NormedSpace Real
      (GlobalCandidateAMatterFiniteGraphCore
        period hPeriod massSquared) := by
  unfold GlobalCandidateAMatterFiniteGraphCore
  exact Submodule.normedSpace _

local instance (priority := 10000)
    globalCandidateAMatterFiniteGraphCoreNormedSpaceInstance
    (massSquared : Real) :
    NormedSpace Real
      (GlobalCandidateAMatterFiniteGraphCore
        period hPeriod massSquared) :=
  globalCandidateAMatterFiniteGraphCoreNormedSpace
    period hPeriod massSquared

local instance (priority := 10000)
    globalCandidateAMatterFiniteGraphCoreModule
    (massSquared : Real) :
    Module Real
      (GlobalCandidateAMatterFiniteGraphCore
        period hPeriod massSquared) := by
  unfold GlobalCandidateAMatterFiniteGraphCore
  exact Submodule.module _

local instance (priority := 10004)
    globalCandidateAMatterFiniteGraphCoreIsBoundedSMul
    (massSquared : Real) :
    IsBoundedSMul Real
      (GlobalCandidateAMatterFiniteGraphCore
        period hPeriod massSquared) :=
  @NormedSpace.toIsBoundedSMul Real
    (GlobalCandidateAMatterFiniteGraphCore
      period hPeriod massSquared)
    inferInstance inferInstance
    (globalCandidateAMatterFiniteGraphCoreNormedSpace
      period hPeriod massSquared)

/-- Underlying closed-graph vector of a finite-range point. -/
def globalCandidateAMatterFiniteGraphCoreValue
    (massSquared : Real)
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod massSquared) :
    ProgramPPrimitiveSpinCMatterGraphDomain
      period hPeriod massSquared := by
  unfold GlobalCandidateAMatterFiniteGraphCore at core
  exact core.1

/-- Continuous inclusion of the finite range into the closed matter graph. -/
def globalCandidateAMatterFiniteGraphInclusion
    (massSquared : Real) :
    GlobalCandidateAMatterFiniteGraphCore period hPeriod massSquared
      →L[Real]
    ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared := by
  let linear :
      GlobalCandidateAMatterFiniteGraphCore period hPeriod massSquared
        →ₗ[Real]
      ProgramPPrimitiveSpinCMatterGraphDomain period hPeriod massSquared :=
    { toFun := globalCandidateAMatterFiniteGraphCoreValue
        period hPeriod massSquared
      map_add' := by
        intros
        unfold globalCandidateAMatterFiniteGraphCoreValue
          GlobalCandidateAMatterFiniteGraphCore
        rfl
      map_smul' := by
        intros
        unfold globalCandidateAMatterFiniteGraphCoreValue
          GlobalCandidateAMatterFiniteGraphCore
        rfl }
  exact linear.mkContinuous 1 (by
    intro core
    rw [one_mul]
    change ‖linear core‖ ≤ ‖linear core‖
    exact le_rfl)

@[simp]
theorem globalCandidateAMatterFiniteGraphInclusion_apply
    (massSquared : Real)
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod massSquared) :
    globalCandidateAMatterFiniteGraphInclusion
        period hPeriod massSquared core =
      globalCandidateAMatterFiniteGraphCoreValue
        period hPeriod massSquared core :=
  rfl

/-- Finite coefficients identify exactly with their graph-norm range. -/
def globalCandidateAMatterFiniteGraphCoreEquiv
    (massSquared : Real) :
    ProgramPPrimitiveSpinCMatterFiniteCoefficients ≃ₗ[Real]
      GlobalCandidateAMatterFiniteGraphCore period hPeriod massSquared :=
  by
    unfold GlobalCandidateAMatterFiniteGraphCore
    exact LinearEquiv.ofInjective
      (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap
        period hPeriod massSquared)
      (programPPrimitiveSpinCMatterGraphFiniteLinearMap_injective
        period hPeriod massSquared)

@[simp]
theorem globalCandidateAMatterFiniteGraphCoreEquiv_symm_graph
    (massSquared : Real)
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod massSquared) :
    programPPrimitiveSpinCMatterGraphFinite
        period hPeriod massSquared
        ((globalCandidateAMatterFiniteGraphCoreEquiv
          period hPeriod massSquared).symm core) =
      globalCandidateAMatterFiniteGraphCoreValue
        period hPeriod massSquared core := by
  unfold globalCandidateAMatterFiniteGraphCoreEquiv
    globalCandidateAMatterFiniteGraphCoreValue
    GlobalCandidateAMatterFiniteGraphCore
  exact LinearEquiv.ofInjective_symm_apply
    (programPPrimitiveSpinCMatterGraphFiniteRealLinearMap
      period hPeriod massSquared) core

/-- Change only the genuine primitive SpinC field. -/
def globalCandidateAMatterFiniteGraphConfiguration
    (configuration : GlobalFieldConfiguration period hPeriod)
    (massSquared : Real)
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod massSquared) :
    GlobalFieldConfiguration period hPeriod :=
  { configuration with
    spinCMatter :=
      programPPrimitiveSpinCMatterSmoothFiniteSynthesis
        period hPeriod
        ((globalCandidateAMatterFiniteGraphCoreEquiv
          period hPeriod massSquared).symm core) }

private def matterFiniteGraphBoundaryData
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod massSquared) :
    GlobalBoundaryVariationData period hPeriod
      (globalCandidateAMatterFiniteGraphConfiguration
        period hPeriod configuration massSquared core)
      NonNullFace NullFace where
  nonNullWeight := data.boundary.nonNullWeight
  nonNullEinsteinScale := data.boundary.nonNullEinsteinScale
  nonNullOrientation := data.boundary.nonNullOrientation
  nonNullDirichletJet := data.boundary.nonNullDirichletJet
  nullFaces := data.boundary.nullFaces
  scalarMassSquared := data.boundary.scalarMassSquared
  scalarField := data.boundary.scalarField
  scalarTest := data.boundary.scalarTest
  scalarControl := data.boundary.scalarControl

/-- The original global action data transported along the matter-only family. -/
def globalCandidateAMatterFiniteGraphDataAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod massSquared) :
    GlobalCandidateAActionData period hPeriod
      (globalCandidateAMatterFiniteGraphConfiguration
        period hPeriod configuration massSquared core)
      couplings NonNullFace NullFace where
  plusGravity := data.plusGravity
  minusGravity := data.minusGravity
  plusMetric_eq := data.plusMetric_eq
  minusMetric_eq := data.minusMetric_eq
  plusMaxwell := data.plusMaxwell
  minusMaxwell := data.minusMaxwell
  plusGauge_eq := data.plusGauge_eq
  minusGauge_eq := data.minusGauge_eq
  interactionDensity := data.interactionDensity
  interactionDensity_eq := data.interactionDensity_eq
  boundary := matterFiniteGraphBoundaryData
    period hPeriod massSquared data core
  nonNullBoundary := data.nonNullBoundary
  nullActionFaces := data.nullActionFaces
  nullActionGenerator_eq := data.nullActionGenerator_eq
  nullActionInterval_eq := data.nullActionInterval_eq

/-- A genuine family of the existing global covariant action. -/
def globalCandidateAMatterFiniteGraphActionFamily
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace) :
    GlobalCandidateAActionFamily period hPeriod
      (GlobalCandidateAMatterFiniteGraphCore
        period hPeriod massSquared)
      couplings NonNullFace NullFace where
  configurationAt :=
    globalCandidateAMatterFiniteGraphConfiguration
      period hPeriod configuration massSquared
  dataAt := globalCandidateAMatterFiniteGraphDataAt
    period hPeriod massSquared data

@[simp]
theorem globalCandidateAMatterFiniteGraphActionFamily_configurationAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod massSquared) :
    (globalCandidateAMatterFiniteGraphActionFamily
      period hPeriod massSquared data).configurationAt core =
      globalCandidateAMatterFiniteGraphConfiguration
        period hPeriod configuration massSquared core :=
  rfl

/-- On this family, the actual matter block is exactly the graph action. -/
theorem globalCandidateAMatterFiniteGraph_matterAction_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    (couplings : GlobalCandidateAActionCouplings)
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod couplings.matterMassSquared) :
    globalCandidateAMatterAction period hPeriod
        (globalCandidateAMatterFiniteGraphConfiguration
          period hPeriod configuration couplings.matterMassSquared core)
        couplings =
      programPPrimitiveSpinCMatterGraphAction
        period hPeriod couplings.matterMassSquared
        (globalCandidateAMatterFiniteGraphInclusion
          period hPeriod couplings.matterMassSquared core) := by
  unfold globalCandidateAMatterFiniteGraphConfiguration
  rw [globalCandidateAMatterAction_finite_eq_graphAction]
  rw [globalCandidateAMatterFiniteGraphCoreEquiv_symm_graph]
  rfl

/-- Exact covariant action restricted to the nonconstant matter family. -/
theorem globalCandidateAMatterFiniteGraph_covariantAction_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod couplings.matterMassSquared) :
    globalCandidateACovariantAction period hPeriod
        (globalCandidateAMatterFiniteGraphDataAt
          period hPeriod couplings.matterMassSquared data core)
        measure =
      (globalCandidateACovariantAction period hPeriod data measure -
          globalCandidateAMatterAction period hPeriod configuration couplings) +
        programPPrimitiveSpinCMatterGraphAction
          period hPeriod couplings.matterMassSquared
          (globalCandidateAMatterFiniteGraphInclusion
            period hPeriod couplings.matterMassSquared core) := by
  unfold globalCandidateACovariantAction
    globalCandidateAMatterFiniteGraphDataAt
    matterFiniteGraphBoundaryData
    globalCandidateAMatterFiniteGraphConfiguration
  rw [globalCandidateAMatterAction_finite_eq_graphAction]
  rw [globalCandidateAMatterFiniteGraphCoreEquiv_symm_graph]
  change
    globalCandidateAEinsteinHilbertAction period hPeriod data measure +
          globalCandidateAInteractionAction period hPeriod data measure +
        programPPrimitiveSpinCMatterGraphAction
          period hPeriod couplings.matterMassSquared
          (globalCandidateAMatterFiniteGraphInclusion
            period hPeriod couplings.matterMassSquared core) +
      globalCandidateAMaxwellAction period hPeriod data measure +
      globalCandidateALLAction period hPeriod data +
      globalCandidateAGHYAction period hPeriod data +
      globalCandidateANullBoundaryAction period hPeriod data =
    (globalCandidateAEinsteinHilbertAction period hPeriod data measure +
            globalCandidateAInteractionAction period hPeriod data measure +
          globalCandidateAMatterAction period hPeriod configuration couplings +
        globalCandidateAMaxwellAction period hPeriod data measure +
        globalCandidateALLAction period hPeriod data +
        globalCandidateAGHYAction period hPeriod data +
        globalCandidateANullBoundaryAction period hPeriod data -
        globalCandidateAMatterAction period hPeriod configuration couplings) +
      programPPrimitiveSpinCMatterGraphAction
        period hPeriod couplings.matterMassSquared
        (globalCandidateAMatterFiniteGraphInclusion
          period hPeriod couplings.matterMassSquared core)
  ring

private theorem matterFiniteGraph_candidateABlock_eq_const
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateAMatterFiniteGraphActionFamily period hPeriod
        couplings.matterMassSquared data) measure).candidateA =
      fun _ => globalCandidateAInteractionAction period hPeriod data measure :=
  rfl

private theorem matterFiniteGraph_matterBlock_eq_graphAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    (couplings : GlobalCandidateAActionCouplings)
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateAMatterFiniteGraphActionFamily period hPeriod
        couplings.matterMassSquared data) measure).matter =
      fun state : GlobalCandidateAMatterFiniteGraphCore period hPeriod
          couplings.matterMassSquared =>
        programPPrimitiveSpinCMatterGraphAction
          period hPeriod couplings.matterMassSquared
          (globalCandidateAMatterFiniteGraphInclusion
            period hPeriod couplings.matterMassSquared state) := by
  funext state
  change globalCandidateAMatterAction period hPeriod
      ((globalCandidateAMatterFiniteGraphActionFamily period hPeriod
        couplings.matterMassSquared data).configurationAt state) couplings = _
  rw [globalCandidateAMatterFiniteGraphActionFamily_configurationAt]
  simpa using globalCandidateAMatterFiniteGraph_matterAction_eq
    period hPeriod couplings state

private theorem matterFiniteGraph_robinBlock_eq_const
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateAMatterFiniteGraphActionFamily period hPeriod
        couplings.matterMassSquared data) measure).robin =
      fun _ => globalCandidateAGHYAction period hPeriod data :=
  rfl

private theorem matterFiniteGraph_llBlock_eq_const
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateAMatterFiniteGraphActionFamily period hPeriod
        couplings.matterMassSquared data) measure).ll =
      fun _ => globalCandidateALLAction period hPeriod data :=
  rfl

private theorem matterFiniteGraph_einsteinHilbertPlusBlock_eq_const
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateAMatterFiniteGraphActionFamily period hPeriod
        couplings.matterMassSquared data) measure).einsteinHilbertPlus =
      fun _ => intrinsicEinsteinHilbertAction period hPeriod
        couplings.plusEinstein data.plusGravity measure :=
  rfl

private theorem matterFiniteGraph_einsteinHilbertMinusBlock_eq_const
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateAMatterFiniteGraphActionFamily period hPeriod
        couplings.matterMassSquared data) measure).einsteinHilbertMinus =
      fun _ => intrinsicEinsteinHilbertAction period hPeriod
        couplings.minusEinstein data.minusGravity measure :=
  rfl

private theorem matterFiniteGraph_maxwellPlusBlock_eq_const
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateAMatterFiniteGraphActionFamily period hPeriod
        couplings.matterMassSquared data) measure).maxwellPlus =
      fun _ => couplings.plusMaxwellScale *
        intrinsicMaxwellAction period hPeriod data.plusGravity.metric
          data.plusMaxwell.basePairing measure :=
  rfl

private theorem matterFiniteGraph_maxwellMinusBlock_eq_const
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateAMatterFiniteGraphActionFamily period hPeriod
        couplings.matterMassSquared data) measure).maxwellMinus =
      fun _ => couplings.minusMaxwellScale *
        intrinsicMaxwellAction period hPeriod data.minusGravity.metric
          data.minusMaxwell.basePairing measure :=
  rfl

private theorem matterFiniteGraph_finiteBVBlock_eq_const
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    (globalCandidateAActionBlocks period hPeriod
      (globalCandidateAMatterFiniteGraphActionFamily period hPeriod
        couplings.matterMassSquared data) measure).finiteBV =
      fun _ => globalCandidateANullBoundaryAction period hPeriod data :=
  rfl

private theorem matterFiniteGraph_graphAction_contDiff_two
    (massSquared : Real) :
    ContDiff Real 2
      (fun state : GlobalCandidateAMatterFiniteGraphCore period hPeriod
          massSquared =>
        programPPrimitiveSpinCMatterGraphAction
          period hPeriod massSquared
          (globalCandidateAMatterFiniteGraphInclusion
            period hPeriod massSquared state)) := by
  exact
    (programPPrimitiveSpinCMatterGraphAction_contDiff_two
      period hPeriod massSquared).comp
        (ContinuousLinearMap.contDiff (𝕜 := Real) (n := 2)
          (globalCandidateAMatterFiniteGraphInclusion
            period hPeriod massSquared))

/-- Closed matter graph Hessian pulled back to the finite graph-norm core. -/
def globalCandidateAMatterFiniteGraphHessian
    (massSquared : Real) :
    GlobalCandidateAMatterFiniteGraphCore period hPeriod massSquared
      →L[Real]
    GlobalCandidateAMatterFiniteGraphCore period hPeriod massSquared
      →L[Real] Real :=
  (programPPrimitiveSpinCMatterGraphForm
    period hPeriod massSquared).bilinearComp
      (globalCandidateAMatterFiniteGraphInclusion
        period hPeriod massSquared)
      (globalCandidateAMatterFiniteGraphInclusion
        period hPeriod massSquared)

@[simp]
theorem globalCandidateAMatterFiniteGraphHessian_apply
    (massSquared : Real)
    (first second : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod massSquared) :
    globalCandidateAMatterFiniteGraphHessian
        period hPeriod massSquared first second =
      programPPrimitiveSpinCMatterGraphForm
        period hPeriod massSquared
        (globalCandidateAMatterFiniteGraphInclusion
          period hPeriod massSquared first)
        (globalCandidateAMatterFiniteGraphInclusion
          period hPeriod massSquared second) :=
  rfl

theorem globalCandidateAMatterFiniteGraphHessian_comm
    (massSquared : Real)
    (first second : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod massSquared) :
    globalCandidateAMatterFiniteGraphHessian
        period hPeriod massSquared first second =
      globalCandidateAMatterFiniteGraphHessian
        period hPeriod massSquared second first := by
  apply programPPrimitiveSpinCMatterGraphForm_comm

private theorem contDiffAt_of_eq_const
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (f : E → Real) (point : E) (constant : Real)
    (h : f = fun _ => constant) :
    ContDiffAt Real 2 f point := by
  rw [h]
  exact contDiffAt_const

/-- The finite graph range is a valid chart of the exact global action. -/
def globalCandidateAMatterFiniteGraphVariationalChart
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure where
  Configuration := GlobalCandidateAMatterFiniteGraphCore
    period hPeriod couplings.matterMassSquared
  normedAddCommGroup :=
    globalCandidateAMatterFiniteGraphCoreNormedAddCommGroup
      period hPeriod couplings.matterMassSquared
  normedSpace := globalCandidateAMatterFiniteGraphCoreNormedSpace
    period hPeriod couplings.matterMassSquared
  family := globalCandidateAMatterFiniteGraphActionFamily
    period hPeriod couplings.matterMassSquared data
  blocksC2 := fun core => by
    constructor
    · exact contDiffAt_of_eq_const _ core _
        (matterFiniteGraph_candidateABlock_eq_const
          period hPeriod data measure)
    · exact Eq.mpr
        (congrArg (fun action => ContDiffAt Real 2 action core)
          (matterFiniteGraph_matterBlock_eq_graphAction
            period hPeriod couplings data measure))
        (matterFiniteGraph_graphAction_contDiff_two
          period hPeriod couplings.matterMassSquared).contDiffAt
    · exact contDiffAt_of_eq_const _ core _
        (matterFiniteGraph_robinBlock_eq_const
          period hPeriod data measure)
    · exact contDiffAt_of_eq_const _ core _
        (matterFiniteGraph_llBlock_eq_const period hPeriod data measure)
    · exact contDiffAt_of_eq_const _ core _
        (matterFiniteGraph_einsteinHilbertPlusBlock_eq_const
          period hPeriod data measure)
    · exact contDiffAt_of_eq_const _ core _
        (matterFiniteGraph_einsteinHilbertMinusBlock_eq_const
          period hPeriod data measure)
    · exact contDiffAt_of_eq_const _ core _
        (matterFiniteGraph_maxwellPlusBlock_eq_const
          period hPeriod data measure)
    · exact contDiffAt_of_eq_const _ core _
        (matterFiniteGraph_maxwellMinusBlock_eq_const
          period hPeriod data measure)
    · exact contDiffAt_of_eq_const _ core _
        (matterFiniteGraph_finiteBVBlock_eq_const
          period hPeriod data measure)

/-- The exact restricted action, written as spectator plus pulled quadratic. -/
def globalCandidateAMatterFiniteGraphPulledAction
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod couplings.matterMassSquared) : Real :=
  (globalCandidateACovariantAction period hPeriod data measure -
      globalCandidateAMatterAction period hPeriod configuration couplings) +
    (1 / 2 : Real) *
      globalCandidateAMatterFiniteGraphHessian
        period hPeriod couplings.matterMassSquared core core

/-- The actual chart pullback is the displayed pulled quadratic action. -/
theorem globalCandidateAMatterFiniteGraph_actionPullback_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod)) :
    globalCandidateAActionPullback period hPeriod
        (globalCandidateAMatterFiniteGraphVariationalChart
          period hPeriod data measure) =
      globalCandidateAMatterFiniteGraphPulledAction
        period hPeriod data measure := by
  funext core
  unfold globalCandidateAActionPullback
    globalCandidateAMatterFiniteGraphVariationalChart
    globalCandidateAMatterFiniteGraphActionFamily
  rw [globalCandidateAMatterFiniteGraph_covariantAction_eq]
  rfl

private theorem symmetricQuadratic_hasFDerivAt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (bilinear : E →L[Real] E →L[Real] Real)
    (hSymmetric :
      ∀ first second, bilinear first second = bilinear second first)
    (point : E) :
    HasFDerivAt (fun state => (1 / 2 : Real) * bilinear state state)
      (bilinear point) point := by
  have hDiagonal :=
    (bilinear.hasFDerivAt (x := point)).clm_apply
      (hasFDerivAt_id (𝕜 := Real) point)
  have hHalf := hDiagonal.const_mul (1 / 2 : Real)
  apply hHalf.congr_fderiv
  ext direction
  change (1 / 2 : Real) *
      (bilinear point direction + bilinear direction point) =
    bilinear point direction
  rw [hSymmetric direction point]
  ring

theorem globalCandidateAMatterFiniteGraphPulledAction_hasFDerivAt
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod couplings.matterMassSquared) :
    HasFDerivAt
      (globalCandidateAMatterFiniteGraphPulledAction
        period hPeriod data measure)
      (globalCandidateAMatterFiniteGraphHessian
        period hPeriod couplings.matterMassSquared core)
      core := by
  unfold globalCandidateAMatterFiniteGraphPulledAction
  have hQuadratic := symmetricQuadratic_hasFDerivAt
    (globalCandidateAMatterFiniteGraphHessian
      period hPeriod couplings.matterMassSquared)
    (globalCandidateAMatterFiniteGraphHessian_comm
      period hPeriod couplings.matterMassSquared)
    core
  exact hQuadratic.const_add
    (globalCandidateACovariantAction period hPeriod data measure -
      globalCandidateAMatterAction
        period hPeriod configuration couplings)

theorem globalCandidateAMatterFiniteGraphPulledAction_fderiv
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod couplings.matterMassSquared) :
    fderiv Real
        (globalCandidateAMatterFiniteGraphPulledAction
          period hPeriod data measure) core =
      globalCandidateAMatterFiniteGraphHessian
        period hPeriod couplings.matterMassSquared core :=
  (globalCandidateAMatterFiniteGraphPulledAction_hasFDerivAt
    period hPeriod data measure core).fderiv

theorem globalCandidateAMatterFiniteGraphPulledAction_second_fderiv
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod couplings.matterMassSquared) :
    fderiv Real
        (fun state => fderiv Real
          (globalCandidateAMatterFiniteGraphPulledAction
            period hPeriod data measure) state)
        core =
      globalCandidateAMatterFiniteGraphHessian
        period hPeriod couplings.matterMassSquared := by
  rw [show
      (fun state => fderiv Real
        (globalCandidateAMatterFiniteGraphPulledAction
          period hPeriod data measure) state) =
      globalCandidateAMatterFiniteGraphHessian
        period hPeriod couplings.matterMassSquared from by
    funext state
    exact globalCandidateAMatterFiniteGraphPulledAction_fderiv
      period hPeriod data measure state]
  exact ContinuousLinearMap.fderiv
    (𝕜 := Real)
    (E := GlobalCandidateAMatterFiniteGraphCore period hPeriod
      couplings.matterMassSquared)
    (F := GlobalCandidateAMatterFiniteGraphCore period hPeriod
      couplings.matterMassSquared →L[Real] Real)
    (globalCandidateAMatterFiniteGraphHessian
      period hPeriod couplings.matterMassSquared)

/-- The genuine global chart Hessian is exactly the closed matter graph form. -/
theorem globalCandidateAMatterFiniteGraph_hessian_eq
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (core : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod couplings.matterMassSquared) :
    globalCandidateAHessian period hPeriod
        (globalCandidateAMatterFiniteGraphVariationalChart
          period hPeriod data measure) core =
      globalCandidateAMatterFiniteGraphHessian
        period hPeriod couplings.matterMassSquared := by
  unfold globalCandidateAHessian globalEulerLagrangeOperator actionGradient
  rw [globalCandidateAMatterFiniteGraph_actionPullback_eq]
  exact globalCandidateAMatterFiniteGraphPulledAction_second_fderiv
    period hPeriod data measure core

/-- Pointwise same-action identity for the genuine covariant chart Hessian. -/
theorem globalCandidateAMatterFiniteGraph_sameActionHessian
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (core first second : GlobalCandidateAMatterFiniteGraphCore
      period hPeriod couplings.matterMassSquared) :
    globalCandidateAHessian period hPeriod
        (globalCandidateAMatterFiniteGraphVariationalChart
          period hPeriod data measure) core first second =
      programPPrimitiveSpinCMatterGraphForm
        period hPeriod couplings.matterMassSquared
        (globalCandidateAMatterFiniteGraphInclusion
          period hPeriod couplings.matterMassSquared first)
        (globalCandidateAMatterFiniteGraphInclusion
          period hPeriod couplings.matterMassSquared second) := by
  rw [globalCandidateAMatterFiniteGraph_hessian_eq]
  rfl

end
end P0EFTJanusProgramPGlobalCandidateAMatterFiniteGraphVariationalChart4D
end JanusFormal
