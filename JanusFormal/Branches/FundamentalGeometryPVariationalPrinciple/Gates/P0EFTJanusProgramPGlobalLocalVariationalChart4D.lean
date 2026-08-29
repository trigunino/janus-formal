import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianFrontier4D

/-!
# Open-domain variational charts for the global Candidate-A action

Admissible Lorentz metrics and root data form an open subset of a normed
model space, not the whole space.  This gate stores physical action data only
on that open set.  A harmless fallback totalizes the scalar action for
Frechet calculus; openness makes all derivatives at admissible points
independent of the fallback.  The Hessian therefore acts on the full ambient
tangent model without imposing global metric admissibility.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalLocalVariationalChart4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000

noncomputable section

open scoped Manifold ContDiff
open MeasureTheory Set
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalHelmholtzReconstruction4D
open P0EFTJanusProgramPGlobalHessianFrontier4D

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

/-- Termwise `C²` regularity restricted to a configuration-space domain. -/
structure FullCoupledC2WithinAt
    {Model : Type u}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (blocks : FullCoupledActionBlocks Model)
    (domain : Set Model) (point : Model) : Prop where
  candidateA : ContDiffWithinAt Real 2 blocks.candidateA domain point
  matter : ContDiffWithinAt Real 2 blocks.matter domain point
  robin : ContDiffWithinAt Real 2 blocks.robin domain point
  ll : ContDiffWithinAt Real 2 blocks.ll domain point
  einsteinHilbertPlus :
    ContDiffWithinAt Real 2 blocks.einsteinHilbertPlus domain point
  einsteinHilbertMinus :
    ContDiffWithinAt Real 2 blocks.einsteinHilbertMinus domain point
  maxwellPlus : ContDiffWithinAt Real 2 blocks.maxwellPlus domain point
  maxwellMinus : ContDiffWithinAt Real 2 blocks.maxwellMinus domain point
  finiteBV : ContDiffWithinAt Real 2 blocks.finiteBV domain point

/-- Global regularity restricts to any domain. -/
def fullCoupledC2At_toWithin
    {Model : Type u}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    {blocks : FullCoupledActionBlocks Model}
    {point : Model} (hC2 : FullCoupledC2At blocks point)
    (domain : Set Model) : FullCoupledC2WithinAt blocks domain point where
  candidateA := hC2.candidateA.contDiffWithinAt
  matter := hC2.matter.contDiffWithinAt
  robin := hC2.robin.contDiffWithinAt
  ll := hC2.ll.contDiffWithinAt
  einsteinHilbertPlus := hC2.einsteinHilbertPlus.contDiffWithinAt
  einsteinHilbertMinus := hC2.einsteinHilbertMinus.contDiffWithinAt
  maxwellPlus := hC2.maxwellPlus.contDiffWithinAt
  maxwellMinus := hC2.maxwellMinus.contDiffWithinAt
  finiteBV := hC2.finiteBV.contDiffWithinAt

/-- At an interior point, within-domain regularity is genuine ambient
regularity on the full model space. -/
def fullCoupledC2WithinAt_toAt
    {Model : Type u}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    {blocks : FullCoupledActionBlocks Model}
    {domain : Set Model} {point : Model}
    (hC2 : FullCoupledC2WithinAt blocks domain point)
    (hOpen : IsOpen domain) (hPoint : point ∈ domain) :
    FullCoupledC2At blocks point where
  candidateA := hC2.candidateA.contDiffAt (hOpen.mem_nhds hPoint)
  matter := hC2.matter.contDiffAt (hOpen.mem_nhds hPoint)
  robin := hC2.robin.contDiffAt (hOpen.mem_nhds hPoint)
  ll := hC2.ll.contDiffAt (hOpen.mem_nhds hPoint)
  einsteinHilbertPlus :=
    hC2.einsteinHilbertPlus.contDiffAt (hOpen.mem_nhds hPoint)
  einsteinHilbertMinus :=
    hC2.einsteinHilbertMinus.contDiffAt (hOpen.mem_nhds hPoint)
  maxwellPlus := hC2.maxwellPlus.contDiffAt (hOpen.mem_nhds hPoint)
  maxwellMinus := hC2.maxwellMinus.contDiffAt (hOpen.mem_nhds hPoint)
  finiteBV := hC2.finiteBV.contDiffAt (hOpen.mem_nhds hPoint)

/-- The exact nine-block sum is `C²` within the same domain. -/
theorem fullCoupledAction_contDiffWithinAt
    {Model : Type u}
    [NormedAddCommGroup Model] [NormedSpace Real Model]
    (blocks : FullCoupledActionBlocks Model)
    (domain : Set Model) (point : Model)
    (hC2 : FullCoupledC2WithinAt blocks domain point) :
    ContDiffWithinAt Real 2 (fullCoupledAction blocks) domain point := by
  exact ((((((((hC2.candidateA.add hC2.matter).add hC2.robin).add
    hC2.ll).add hC2.einsteinHilbertPlus).add
    hC2.einsteinHilbertMinus).add hC2.maxwellPlus).add
    hC2.maxwellMinus).add hC2.finiteBV)

/-- One physical configuration together with its exact Candidate-A data. -/
abbrev GlobalCandidateALocalActionDatum
    (couplings : GlobalCandidateAActionCouplings)
    (NonNullFace NullFace : Type*)
    [Fintype NonNullFace] [Fintype NullFace] :=
  Σ configuration : GlobalFieldConfiguration period hPeriod,
    GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace

/-- Physical Candidate-A data defined only on an admissible domain. -/
structure GlobalCandidateALocalActionFamily
    (Model : Type u)
    (couplings : GlobalCandidateAActionCouplings)
    (NonNullFace NullFace : Type*)
    [Fintype NonNullFace] [Fintype NullFace] where
  domain : Set Model
  datumAt : ∀ point : Model, point ∈ domain →
    GlobalCandidateALocalActionDatum period hPeriod couplings
      NonNullFace NullFace

/-- Totalize the packaged datum by one admissible fallback point. -/
noncomputable def GlobalCandidateALocalActionFamily.datumAtTotal
    {Model : Type u}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (family : GlobalCandidateALocalActionFamily period hPeriod Model couplings
      NonNullFace NullFace)
    (fallback : Model) (hFallback : fallback ∈ family.domain)
    (point : Model) : GlobalCandidateALocalActionDatum period hPeriod couplings
      NonNullFace NullFace := by
  classical
  exact if hPoint : point ∈ family.domain then
    family.datumAt point hPoint
  else
    family.datumAt fallback hFallback

@[simp]
theorem GlobalCandidateALocalActionFamily.datumAtTotal_of_mem
    {Model : Type u}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (family : GlobalCandidateALocalActionFamily period hPeriod Model couplings
      NonNullFace NullFace)
    (fallback : Model) (hFallback : fallback ∈ family.domain)
    (point : Model) (hPoint : point ∈ family.domain) :
    family.datumAtTotal period hPeriod fallback hFallback point =
      family.datumAt point hPoint := by
  classical
  simp [GlobalCandidateALocalActionFamily.datumAtTotal, hPoint]

/-- Canonical fallback totalization used only to invoke ambient Frechet
derivatives. -/
noncomputable def GlobalCandidateALocalActionFamily.toActionFamily
    {Model : Type u}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (family : GlobalCandidateALocalActionFamily period hPeriod Model couplings
      NonNullFace NullFace)
    (fallback : Model) (hFallback : fallback ∈ family.domain) :
    GlobalCandidateAActionFamily period hPeriod Model couplings
      NonNullFace NullFace where
  configurationAt := fun point =>
    (family.datumAtTotal period hPeriod fallback hFallback point).1
  dataAt := fun point =>
    (family.datumAtTotal period hPeriod fallback hFallback point).2

/-- A local chart centered at `0` in a normed model space.  Only points of
the open admissible domain carry physical configurations. -/
structure GlobalCandidateALocalVariationalChart
    (couplings : GlobalCandidateAActionCouplings)
    (NonNullFace NullFace : Type*)
    [Fintype NonNullFace] [Fintype NullFace]
    (measure : Measure (EffectiveQuotient period hPeriod)) where
  Model : Type u
  [normedAddCommGroup : NormedAddCommGroup Model]
  [normedSpace : NormedSpace Real Model]
  family : GlobalCandidateALocalActionFamily period hPeriod Model couplings
    NonNullFace NullFace
  isOpen_domain : IsOpen family.domain
  zero_mem_domain : (0 : Model) ∈ family.domain
  blocksC2Within : ∀ point (_hPoint : point ∈ family.domain),
    FullCoupledC2WithinAt
      (globalCandidateAActionBlocks period hPeriod
        (family.toActionFamily period hPeriod 0 zero_mem_domain) measure)
      family.domain point

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  GlobalCandidateAVariationalChart.normedAddCommGroup
  GlobalCandidateAVariationalChart.normedSpace

/-- The exact action pulled back to the ambient model. -/
def globalCandidateALocalActionPullback
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) : chart.Model → Real :=
  fullCoupledAction
    (globalCandidateAActionBlocks period hPeriod
      (chart.family.toActionFamily period hPeriod 0 chart.zero_mem_domain)
      measure)

theorem globalCandidateALocalActionPullback_eq_covariant_of_mem
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model) (hPoint : point ∈ chart.family.domain) :
    globalCandidateALocalActionPullback period hPeriod chart point =
      globalCandidateACovariantAction period hPeriod
        (chart.family.datumAt point hPoint).2 measure := by
  unfold globalCandidateALocalActionPullback
  rw [globalCandidateAActionBlocks_sum]
  change globalCandidateACovariantAction period hPeriod
      (chart.family.datumAtTotal period hPeriod 0 chart.zero_mem_domain
        point).2 measure =
    globalCandidateACovariantAction period hPeriod
      (chart.family.datumAt point hPoint).2 measure
  rw [GlobalCandidateALocalActionFamily.datumAtTotal_of_mem]

/-- The pullback is `C²` using only regularity inside the admissible set. -/
theorem globalCandidateALocalActionPullback_contDiffWithinAt_two
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model) (hPoint : point ∈ chart.family.domain) :
    ContDiffWithinAt Real 2
      (globalCandidateALocalActionPullback period hPeriod chart)
      chart.family.domain point :=
  fullCoupledAction_contDiffWithinAt _ _ _
    (chart.blocksC2Within point hPoint)

/-- Openness turns within-domain `C²` into ambient `C²` at every admissible
point. -/
theorem globalCandidateALocalActionPullback_contDiffAt_two
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model) (hPoint : point ∈ chart.family.domain) :
    ContDiffAt Real 2
      (globalCandidateALocalActionPullback period hPeriod chart) point :=
  (globalCandidateALocalActionPullback_contDiffWithinAt_two
    period hPeriod chart point hPoint).contDiffAt
      (chart.isOpen_domain.mem_nhds hPoint)

/-- Local Euler one-form on the full ambient tangent model. -/
noncomputable def globalCandidateALocalEulerLagrangeOperator
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) : EulerOneForm chart.Model :=
  actionGradient (globalCandidateALocalActionPullback period hPeriod chart)

theorem globalCandidateALocalAction_hasFDerivAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model) (hPoint : point ∈ chart.family.domain) :
    HasFDerivAt
      (globalCandidateALocalActionPullback period hPeriod chart)
      (globalCandidateALocalEulerLagrangeOperator period hPeriod chart point)
      point := by
  exact (globalCandidateALocalActionPullback_contDiffAt_two
    period hPeriod chart point hPoint).differentiableAt
      (by norm_num) |>.hasFDerivAt

/-- The Euler one-form is differentiable at every admissible point. -/
theorem globalCandidateALocalEulerLagrangeOperator_differentiableAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model) (hPoint : point ∈ chart.family.domain) :
    DifferentiableAt Real
      (globalCandidateALocalEulerLagrangeOperator period hPeriod chart)
      point := by
  have hDerivative : ContDiffAt Real 1
      (fderiv Real
        (globalCandidateALocalActionPullback period hPeriod chart)) point :=
    (globalCandidateALocalActionPullback_contDiffAt_two
      period hPeriod chart point hPoint).fderiv_right (by norm_num)
  exact hDerivative.differentiableAt (by norm_num)

/-- Actual ambient Hessian at an admissible point. -/
noncomputable def globalCandidateALocalHessian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model) :
    chart.Model →L[Real] chart.Model →L[Real] Real :=
  fderiv Real
    (globalCandidateALocalEulerLagrangeOperator period hPeriod chart) point

theorem globalCandidateALocalHessian_hasFDerivAt
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model) (hPoint : point ∈ chart.family.domain) :
    HasFDerivAt
      (globalCandidateALocalEulerLagrangeOperator period hPeriod chart)
      (globalCandidateALocalHessian period hPeriod chart point) point :=
  (globalCandidateALocalEulerLagrangeOperator_differentiableAt
    period hPeriod chart point hPoint).hasFDerivAt

theorem globalCandidateALocalHessian_symmetric
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Model) (hPoint : point ∈ chart.family.domain)
    (first second : chart.Model) :
    globalCandidateALocalHessian period hPeriod chart point first second =
      globalCandidateALocalHessian period hPeriod chart point second first := by
  exact action_gradient_helmholtz_at
    (globalCandidateALocalActionPullback period hPeriod chart) point
    (globalCandidateALocalActionPullback_contDiffAt_two
      period hPeriod chart point hPoint) first second

/-- A whole-space family is the special local family with domain `univ`. -/
def globalCandidateAActionFamilyToLocal
    {Model : Type u}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (family : GlobalCandidateAActionFamily period hPeriod Model couplings
      NonNullFace NullFace) :
    GlobalCandidateALocalActionFamily period hPeriod Model couplings
      NonNullFace NullFace where
  domain := Set.univ
  datumAt := fun point _ =>
    ⟨family.configurationAt point, family.dataAt point⟩

theorem globalCandidateAActionFamilyToLocal_blocks_eq
    {Model : Type u}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (family : GlobalCandidateAActionFamily period hPeriod Model couplings
      NonNullFace NullFace)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (fallback : Model)
    (hFallback : fallback ∈
      (globalCandidateAActionFamilyToLocal period hPeriod family).domain) :
    globalCandidateAActionBlocks period hPeriod
        ((globalCandidateAActionFamilyToLocal period hPeriod family).toActionFamily
          period hPeriod fallback hFallback) measure =
      globalCandidateAActionBlocks period hPeriod family measure := by
  rw [FullCoupledActionBlocks.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    funext point <;>
    simp [globalCandidateAActionBlocks,
      globalCandidateAActionFamilyToLocal,
      GlobalCandidateALocalActionFamily.toActionFamily,
      GlobalCandidateALocalActionFamily.datumAtTotal] <;>
    try rw [if_pos (Set.mem_univ point)] <;>
    try rw [dif_pos (Set.mem_univ point)]
  all_goals simp

/-- Existing global charts embed in the local API without changing their
action. -/
noncomputable def globalCandidateAVariationalChartToLocal
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure where
  Model := chart.Configuration
  normedAddCommGroup := chart.normedAddCommGroup
  normedSpace := chart.normedSpace
  family := globalCandidateAActionFamilyToLocal period hPeriod chart.family
  isOpen_domain := isOpen_univ
  zero_mem_domain := Set.mem_univ 0
  blocksC2Within := by
    intro point _
    rw [globalCandidateAActionFamilyToLocal_blocks_eq]
    exact fullCoupledC2At_toWithin (chart.blocksC2 point) Set.univ

theorem globalCandidateAVariationalChart_toLocal_actionPullback_eq
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    globalCandidateALocalActionPullback period hPeriod
        (globalCandidateAVariationalChartToLocal period hPeriod chart) =
      globalCandidateAActionPullback period hPeriod chart := by
  funext point
  rw [globalCandidateALocalActionPullback_eq_covariant_of_mem
    period hPeriod
      (globalCandidateAVariationalChartToLocal period hPeriod chart)
      point (Set.mem_univ point)]
  rfl

theorem globalCandidateAVariationalChart_toLocal_euler_eq
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    globalCandidateALocalEulerLagrangeOperator period hPeriod
        (globalCandidateAVariationalChartToLocal period hPeriod chart) =
      globalEulerLagrangeOperator period hPeriod chart := by
  unfold globalCandidateALocalEulerLagrangeOperator
    globalEulerLagrangeOperator
  rw [globalCandidateAVariationalChart_toLocal_actionPullback_eq]
  rfl

theorem globalCandidateAVariationalChart_toLocal_hessian_eq
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateAVariationalChart period hPeriod couplings
      NonNullFace NullFace measure)
    (point : chart.Configuration) :
    globalCandidateALocalHessian period hPeriod
        (globalCandidateAVariationalChartToLocal period hPeriod chart) point =
      globalCandidateAHessian period hPeriod chart point := by
  unfold globalCandidateALocalHessian globalCandidateAHessian
  rw [globalCandidateAVariationalChart_toLocal_euler_eq]
  rfl

/-- Local Hessian closure at the chart origin, with no admissibility
assumption on arbitrary tangent vectors. -/
theorem global_candidateA_local_hessian_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (chart : GlobalCandidateALocalVariationalChart period hPeriod couplings
      NonNullFace NullFace measure) :
    (0 : chart.Model) ∈ chart.family.domain ∧
      ContDiffAt Real 2
        (globalCandidateALocalActionPullback period hPeriod chart) 0 ∧
      HasFDerivAt
        (globalCandidateALocalEulerLagrangeOperator period hPeriod chart)
        (globalCandidateALocalHessian period hPeriod chart 0) 0 ∧
      ∀ first second : chart.Model,
        globalCandidateALocalHessian period hPeriod chart 0 first second =
          globalCandidateALocalHessian period hPeriod chart 0 second first := by
  exact ⟨chart.zero_mem_domain,
    globalCandidateALocalActionPullback_contDiffAt_two
      period hPeriod chart 0 chart.zero_mem_domain,
    globalCandidateALocalHessian_hasFDerivAt
      period hPeriod chart 0 chart.zero_mem_domain,
    globalCandidateALocalHessian_symmetric
      period hPeriod chart 0 chart.zero_mem_domain⟩

end
end P0EFTJanusProgramPGlobalLocalVariationalChart4D
end JanusFormal
