import Mathlib.Geometry.Manifold.VectorBundle.Basic
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusNormalLine
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothThroatEmbedding

/-!
# Smooth normal vector bundle of the effective fixed throat

This gate upgrades the sign-clutched normal-line presentation to an actual
rank-one `VectorBundleCore` on the effective throat quotient.  Its local
trivializations are the local sections of the mapping-torus covering and its
transition maps are the exact deck-sign representation.  The transition maps
are locally constant, hence analytic.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSmoothNormalVectorBundle

set_option autoImplicit false

noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusNormalBundleOrientationCover

variable (period : ℝ) (hPeriod : period ≠ 0)

private abbrev ThroatCover :=
  MappingTorusCover (fixedEquatorData period hPeriod)

private abbrev ThroatBase :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev throatProjectionLocalHomeomorph :
    IsLocalHomeomorph
      (mappingTorusMk (fixedEquatorData period hPeriod)) :=
  (mappingTorusMk_isCoveringMap
    (fixedEquatorData period hPeriod)).isLocalHomeomorph

/-- The bundle chart based at a cover point is defined on the source of its
chosen covering local inverse. -/
def normalBundleBaseSet (anchor : ThroatCover period hPeriod) :
    Set (ThroatBase period hPeriod) :=
  ((throatProjectionLocalHomeomorph period hPeriod).localInverseAt anchor).source

theorem normalBundleBaseSet_isOpen (anchor : ThroatCover period hPeriod) :
    IsOpen (normalBundleBaseSet period hPeriod anchor) :=
  ((throatProjectionLocalHomeomorph period hPeriod).localInverseAt anchor).open_source

/-- A preferred lift supplies a bundle chart at every quotient point. -/
def normalBundleIndexAt (base : ThroatBase period hPeriod) :
    ThroatCover period hPeriod :=
  Classical.choose
    (mappingTorusMk_surjective (fixedEquatorData period hPeriod) base)

theorem normalBundleIndexAt_projects (base : ThroatBase period hPeriod) :
    mappingTorusMk (fixedEquatorData period hPeriod)
        (normalBundleIndexAt period hPeriod base) = base :=
  Classical.choose_spec
    (mappingTorusMk_surjective (fixedEquatorData period hPeriod) base)

theorem mem_normalBundleBaseSet_indexAt (base : ThroatBase period hPeriod) :
    base ∈ normalBundleBaseSet period hPeriod
      (normalBundleIndexAt period hPeriod base) := by
  have hMem := (throatProjectionLocalHomeomorph period hPeriod)
    |>.apply_self_mem_localInverseAt_source
      (x := normalBundleIndexAt period hPeriod base)
  simpa only [normalBundleBaseSet,
    normalBundleIndexAt_projects period hPeriod base] using hMem

private theorem exists_transition_winding
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ normalBundleBaseSet period hPeriod first ∩
      normalBundleBaseSet period hPeriod second) :
    ∃ winding : ℤ,
      winding +ᵥ
          (throatProjectionLocalHomeomorph period hPeriod).localInverseAt first base =
        (throatProjectionLocalHomeomorph period hPeriod).localInverseAt second base := by
  let hf := throatProjectionLocalHomeomorph period hPeriod
  let firstSection := hf.localInverseAt first
  let secondSection := hf.localInverseAt second
  have hFirstProjection :
      mappingTorusMk (fixedEquatorData period hPeriod) (firstSection base) = base :=
    hf.apply_localInverseAt_of_mem hBase.1
  have hSecondProjection :
      mappingTorusMk (fixedEquatorData period hPeriod) (secondSection base) = base :=
    hf.apply_localInverseAt_of_mem hBase.2
  exact (mappingTorusMk_eq_iff_exists_vadd
    (fixedEquatorData period hPeriod) (secondSection base) (firstSection base)).1
      (hSecondProjection.trans hFirstProjection.symm)

/-- Unique integer relating two covering local sections on their overlap. -/
def localTransitionWinding
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod) : ℤ := by
  classical
  exact if hBase : base ∈ normalBundleBaseSet period hPeriod first ∩
        normalBundleBaseSet period hPeriod second then
      Classical.choose
        (exists_transition_winding period hPeriod first second base hBase)
    else 0

theorem localTransitionWinding_vadd
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ normalBundleBaseSet period hPeriod first ∩
      normalBundleBaseSet period hPeriod second) :
    localTransitionWinding period hPeriod first second base +ᵥ
        (throatProjectionLocalHomeomorph period hPeriod).localInverseAt first base =
      (throatProjectionLocalHomeomorph period hPeriod).localInverseAt second base := by
  rw [localTransitionWinding, dif_pos hBase]
  exact Classical.choose_spec
    (exists_transition_winding period hPeriod first second base hBase)

theorem localTransitionWinding_self
    (anchor : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ normalBundleBaseSet period hPeriod anchor) :
    localTransitionWinding period hPeriod anchor anchor base = 0 := by
  apply IsCancelVAdd.right_cancel _ _
    ((throatProjectionLocalHomeomorph period hPeriod).localInverseAt anchor base)
  rw [zero_vadd]
  exact localTransitionWinding_vadd period hPeriod anchor anchor base ⟨hBase, hBase⟩

private theorem localTransitionWinding_add
    (first second third : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ normalBundleBaseSet period hPeriod first ∩
        normalBundleBaseSet period hPeriod second ∩
        normalBundleBaseSet period hPeriod third) :
    localTransitionWinding period hPeriod second third base +
        localTransitionWinding period hPeriod first second base =
      localTransitionWinding period hPeriod first third base := by
  let firstLift :=
    (throatProjectionLocalHomeomorph period hPeriod).localInverseAt first base
  let secondLift :=
    (throatProjectionLocalHomeomorph period hPeriod).localInverseAt second base
  let thirdLift :=
    (throatProjectionLocalHomeomorph period hPeriod).localInverseAt third base
  have hFirstSecond := localTransitionWinding_vadd period hPeriod first second base
    ⟨hBase.1.1, hBase.1.2⟩
  have hSecondThird := localTransitionWinding_vadd period hPeriod second third base
    ⟨hBase.1.2, hBase.2⟩
  have hFirstThird := localTransitionWinding_vadd period hPeriod first third base
    ⟨hBase.1.1, hBase.2⟩
  apply IsCancelVAdd.right_cancel _ _ firstLift
  rw [add_vadd, hFirstSecond, hSecondThird, hFirstThird]

private theorem localTransitionWinding_eventuallyEq
    (first second : ThroatCover period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ normalBundleBaseSet period hPeriod first ∩
      normalBundleBaseSet period hPeriod second) :
    Filter.EventuallyEq (nhds base)
      (localTransitionWinding period hPeriod first second)
      (fun _ ↦ localTransitionWinding period hPeriod first second base) := by
  let hf := throatProjectionLocalHomeomorph period hPeriod
  let winding := localTransitionWinding period hPeriod first second base
  have hSections := localInverseAt_eventuallyEq_vadd_of_mem
    (fixedEquatorData period hPeriod) first second base hBase.1 hBase.2 winding
      (localTransitionWinding_vadd period hPeriod first second base hBase)
  have hOverlap : normalBundleBaseSet period hPeriod first ∩
      normalBundleBaseSet period hPeriod second ∈ nhds base :=
    ((normalBundleBaseSet_isOpen period hPeriod first).inter
      (normalBundleBaseSet_isOpen period hPeriod second)).mem_nhds hBase
  filter_upwards [hSections, hOverlap] with nearby hSectionsNearby hNearby
  apply IsCancelVAdd.right_cancel _ _
    ((throatProjectionLocalHomeomorph period hPeriod).localInverseAt first nearby)
  exact (localTransitionWinding_vadd period hPeriod first second nearby hNearby).trans
    hSectionsNearby

/-- Continuous linear action of a deck winding on the normal coordinate. -/
def normalSignCLM (winding : ℤ) : ℝ →L[ℝ] ℝ :=
  (normalSignRepresentation winding : ℝ) • ContinuousLinearMap.id ℝ ℝ

@[simp] theorem normalSignCLM_apply (winding : ℤ) (normal : ℝ) :
    normalSignCLM winding normal =
      (normalSignRepresentation winding : ℝ) * normal := by
  simp [normalSignCLM]

private theorem continuousOn_normalTransition
    (first second : ThroatCover period hPeriod) :
    ContinuousOn
      (fun base ↦ normalSignCLM
        (localTransitionWinding period hPeriod first second base))
      (normalBundleBaseSet period hPeriod first ∩
        normalBundleBaseSet period hPeriod second) := by
  intro base hBase
  let overlap := normalBundleBaseSet period hPeriod first ∩
    normalBundleBaseSet period hPeriod second
  have hWindingEq : Filter.EventuallyEq (nhdsWithin base overlap)
      (localTransitionWinding period hPeriod first second)
      (fun _ ↦ localTransitionWinding period hPeriod first second base) :=
    (localTransitionWinding_eventuallyEq period hPeriod first second base hBase).filter_mono
      inf_le_left
  have hNormalEq := hWindingEq.fun_comp normalSignCLM
  exact (continuousWithinAt_const : ContinuousWithinAt
      (fun _ : ThroatBase period hPeriod ↦
        normalSignCLM (localTransitionWinding period hPeriod first second base))
      overlap base).congr_of_eventuallyEq_of_mem hNormalEq hBase

/-- The actual rank-one normal vector-bundle core on the effective throat. -/
def fixedThroatNormalVectorBundleCore :
    VectorBundleCore ℝ (ThroatBase period hPeriod) ℝ
      (ThroatCover period hPeriod) where
  baseSet := normalBundleBaseSet period hPeriod
  isOpen_baseSet := normalBundleBaseSet_isOpen period hPeriod
  indexAt := normalBundleIndexAt period hPeriod
  mem_baseSet_at := mem_normalBundleBaseSet_indexAt period hPeriod
  coordChange first second base :=
    normalSignCLM (localTransitionWinding period hPeriod first second base)
  coordChange_self anchor base hBase normal := by
    simp [localTransitionWinding_self period hPeriod anchor base hBase,
      normalSignCLM, normalSignRepresentation]
  continuousOn_coordChange :=
    continuousOn_normalTransition period hPeriod
  coordChange_comp first second third base hBase normal := by
    simp only [normalSignCLM_apply]
    rw [← mul_assoc, ← Units.val_mul, ← normal_sign_add,
      localTransitionWinding_add period hPeriod first second third base hBase]

/-- The associated fiber family produced by the core. -/
abbrev FixedThroatNormalFiber :=
  (fixedThroatNormalVectorBundleCore period hPeriod).Fiber

/-- The construction is an actual topological real line bundle. -/
theorem fixedThroatNormalFiber_isVectorBundle :
    VectorBundle ℝ ℝ (FixedThroatNormalFiber period hPeriod) :=
  inferInstance

private theorem contMDiffOn_normalTransition
    (first second : ThroatCover period hPeriod) :
    letI : ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
      fixedThroatQuotientChartedSpace period hPeriod
    ContMDiffOn throatCoverModelWithCorners
      (modelWithCornersSelf ℝ (ℝ →L[ℝ] ℝ)) ω
      (fun base ↦ normalSignCLM
        (localTransitionWinding period hPeriod first second base))
      (normalBundleBaseSet period hPeriod first ∩
        normalBundleBaseSet period hPeriod second) := by
  letI : ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
    fixedThroatQuotientChartedSpace period hPeriod
  intro base hBase
  let overlap := normalBundleBaseSet period hPeriod first ∩
    normalBundleBaseSet period hPeriod second
  have hWindingEq : Filter.EventuallyEq (nhdsWithin base overlap)
      (localTransitionWinding period hPeriod first second)
      (fun _ ↦ localTransitionWinding period hPeriod first second base) :=
    (localTransitionWinding_eventuallyEq period hPeriod first second base hBase).filter_mono
      inf_le_left
  have hNormalEq := hWindingEq.fun_comp normalSignCLM
  exact (contMDiffWithinAt_const : ContMDiffWithinAt throatCoverModelWithCorners
      (modelWithCornersSelf ℝ (ℝ →L[ℝ] ℝ)) ω
      (fun _ : ThroatBase period hPeriod ↦
        normalSignCLM (localTransitionWinding period hPeriod first second base))
      overlap base).congr_of_eventuallyEq_of_mem hNormalEq hBase

/-- The transition functions are locally constant, so the normal line is an
analytic vector bundle over the descended analytic throat. -/
theorem fixedThroatNormalVectorBundleCore_isContMDiff :
    letI : ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
      fixedThroatQuotientChartedSpace period hPeriod
    (fixedThroatNormalVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ω := by
  letI : ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
    fixedThroatQuotientChartedSpace period hPeriod
  constructor
  exact contMDiffOn_normalTransition period hPeriod

/-- The core therefore installs a genuine analytic vector-bundle structure,
not merely a family of abstract one-dimensional spaces. -/
theorem fixedThroatNormalFiber_isContMDiffVectorBundle :
    letI : ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
      fixedThroatQuotientChartedSpace period hPeriod
    letI : (fixedThroatNormalVectorBundleCore period hPeriod).IsContMDiff
        throatCoverModelWithCorners ω :=
      fixedThroatNormalVectorBundleCore_isContMDiff period hPeriod
    ContMDiffVectorBundle ω ℝ (FixedThroatNormalFiber period hPeriod)
      throatCoverModelWithCorners := by
  letI : ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
    fixedThroatQuotientChartedSpace period hPeriod
  letI : (fixedThroatNormalVectorBundleCore period hPeriod).IsContMDiff
      throatCoverModelWithCorners ω :=
    fixedThroatNormalVectorBundleCore_isContMDiff period hPeriod
  infer_instance

/-- Each constructed bundle fiber is noncanonically linearly equivalent to
the differential normal quotient.  This identifies the two pointwise while
making no false claim that the chosen equivalences vary smoothly. -/
theorem fixedThroatNormalFiber_equiv_differentialNormal
    (point : ThroatBase period hPeriod) :
    letI : ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
      fixedThroatQuotientChartedSpace period hPeriod
    letI : ChartedSpace CoverModel
        (MappingTorus (reflectedSphereData period hPeriod)) :=
      reflectedSphereQuotientChartedSpace period hPeriod
    Nonempty
      (FixedThroatNormalFiber period hPeriod point ≃ₗ[ℝ]
        HasQuotient.Quotient
          (TangentSpace coverModelWithCorners
            (fixedThroatQuotientInclusion period hPeriod point))
          (LinearMap.range
            (mfderiv throatCoverModelWithCorners coverModelWithCorners
              (fixedThroatQuotientInclusion period hPeriod) point).toLinearMap)) := by
  letI : ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
    fixedThroatQuotientChartedSpace period hPeriod
  letI : ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
    reflectedSphereQuotientChartedSpace period hPeriod
  let targetTangent := TangentSpace coverModelWithCorners
    (fixedThroatQuotientInclusion period hPeriod point)
  let targetEquiv : targetTangent ≃L[ℝ] CoverCoordinates :=
    ContinuousLinearEquiv.refl ℝ CoverCoordinates
  letI : FiniteDimensional ℝ targetTangent :=
    targetEquiv.toLinearEquiv.symm.finiteDimensional
  letI : FiniteDimensional ℝ
      (FixedThroatNormalFiber period hPeriod point) := by
    change FiniteDimensional ℝ ℝ
    infer_instance
  have hFiber : Module.finrank ℝ
      (FixedThroatNormalFiber period hPeriod point) = 1 := by
    change Module.finrank ℝ ℝ = 1
    simp
  have hDifferentialNormal : Module.finrank ℝ
      (HasQuotient.Quotient targetTangent (LinearMap.range
        (mfderiv throatCoverModelWithCorners coverModelWithCorners
          (fixedThroatQuotientInclusion period hPeriod) point).toLinearMap)) = 1 :=
    mfderiv_fixedThroatQuotientInclusion_normal_finrank period hPeriod point
  exact ⟨LinearEquiv.ofFinrankEq _ _
    (hFiber.trans hDifferentialNormal.symm)⟩

/-- One deck circuit is recorded by the nontrivial transition `-id`. -/
theorem localTransitionWinding_one_loop
    (anchor : ThroatCover period hPeriod) :
    localTransitionWinding period hPeriod anchor ((1 : ℤ) +ᵥ anchor)
      (mappingTorusMk (fixedEquatorData period hPeriod) anchor) = 1 := by
  let hf := throatProjectionLocalHomeomorph period hPeriod
  let base := mappingTorusMk (fixedEquatorData period hPeriod) anchor
  have hProjection :
      mappingTorusMk (fixedEquatorData period hPeriod) ((1 : ℤ) +ᵥ anchor) = base := by
    exact (mappingTorusMk_isAddQuotientCoveringMap
      (fixedEquatorData period hPeriod)).map_vadd 1
  have hFirst : base ∈ normalBundleBaseSet period hPeriod anchor :=
    hf.apply_self_mem_localInverseAt_source
  have hSecond : base ∈ normalBundleBaseSet period hPeriod ((1 : ℤ) +ᵥ anchor) := by
    rw [← hProjection]
    exact hf.apply_self_mem_localInverseAt_source
  have hTransition := localTransitionWinding_vadd period hPeriod anchor
    ((1 : ℤ) +ᵥ anchor) base ⟨hFirst, hSecond⟩
  have hFirstValue : hf.localInverseAt anchor base = anchor :=
    hf.localInverseAt_apply_self
  have hSecondValue : hf.localInverseAt ((1 : ℤ) +ᵥ anchor) base =
      (1 : ℤ) +ᵥ anchor := by
    rw [← hProjection]
    exact hf.localInverseAt_apply_self
  rw [hFirstValue, hSecondValue] at hTransition
  exact IsCancelVAdd.right_cancel _ _ anchor hTransition

theorem one_loop_coordChange_eq_neg_id
    (anchor : ThroatCover period hPeriod) (normal : ℝ) :
    (fixedThroatNormalVectorBundleCore period hPeriod).coordChange anchor
        ((1 : ℤ) +ᵥ anchor)
        (mappingTorusMk (fixedEquatorData period hPeriod) anchor) normal =
      -normal := by
  simp [fixedThroatNormalVectorBundleCore,
    localTransitionWinding_one_loop period hPeriod anchor,
    normalSignCLM, normalSignRepresentation]

end

end P0EFTJanusMappingTorusSmoothNormalVectorBundle
end JanusFormal
