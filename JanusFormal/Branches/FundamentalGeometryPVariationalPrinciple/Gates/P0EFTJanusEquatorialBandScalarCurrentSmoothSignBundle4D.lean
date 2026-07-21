import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEquatorialBandScalarCurrentDeckTwist4D

/-!
# Smooth ambient sign line for the latitude scalar current

The global latitude-current coefficient is anti-invariant on the reflected-sphere
cover.  This gate realizes its sign cocycle as a genuine analytic real line bundle
over the effective four-dimensional mapping torus.  It then identifies the
equivariant coefficient with a smooth section of that bundle.

No scalar descent, Stokes theorem, or global Noether statement is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusEquatorialBandScalarCurrentSmoothSignBundle4D

set_option autoImplicit false
set_option maxHeartbeats 800000

noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusNormalBundleOrientationCover
open P0EFTJanusEquatorialBandScalarCurrentZeroExtension4D
open P0EFTJanusEquatorialBandScalarCurrentDeckTwist4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveCover :=
  MappingTorusCover (reflectedSphereData period hPeriod)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev ambientProjectionLocalHomeomorph :
    IsLocalHomeomorph
      (mappingTorusMk (reflectedSphereData period hPeriod)) :=
  (mappingTorusMk_isCoveringMap
    (reflectedSphereData period hPeriod)).isLocalHomeomorph

/-- Domain of the covering local inverse based at an ambient cover point. -/
def ambientSignBundleBaseSet (anchor : EffectiveCover period hPeriod) :
    Set (EffectiveQuotient period hPeriod) :=
  ((ambientProjectionLocalHomeomorph period hPeriod).localInverseAt anchor).source

theorem ambientSignBundleBaseSet_isOpen
    (anchor : EffectiveCover period hPeriod) :
    IsOpen (ambientSignBundleBaseSet period hPeriod anchor) :=
  ((ambientProjectionLocalHomeomorph period hPeriod).localInverseAt anchor).open_source

/-- A preferred cover lift supplies a chart index at each quotient point. -/
def ambientSignBundleIndexAt (base : EffectiveQuotient period hPeriod) :
    EffectiveCover period hPeriod :=
  Classical.choose
    (mappingTorusMk_surjective (reflectedSphereData period hPeriod) base)

theorem ambientSignBundleIndexAt_projects
    (base : EffectiveQuotient period hPeriod) :
    mappingTorusMk (reflectedSphereData period hPeriod)
        (ambientSignBundleIndexAt period hPeriod base) = base :=
  Classical.choose_spec
    (mappingTorusMk_surjective (reflectedSphereData period hPeriod) base)

theorem mem_ambientSignBundleBaseSet_indexAt
    (base : EffectiveQuotient period hPeriod) :
    base ∈ ambientSignBundleBaseSet period hPeriod
      (ambientSignBundleIndexAt period hPeriod base) := by
  have hMem := (ambientProjectionLocalHomeomorph period hPeriod)
    |>.apply_self_mem_localInverseAt_source
      (x := ambientSignBundleIndexAt period hPeriod base)
  simpa only [ambientSignBundleBaseSet,
    ambientSignBundleIndexAt_projects period hPeriod base] using hMem

private theorem exists_ambientSignTransitionWinding
    (first second : EffectiveCover period hPeriod)
    (base : EffectiveQuotient period hPeriod)
    (hBase : base ∈ ambientSignBundleBaseSet period hPeriod first ∩
      ambientSignBundleBaseSet period hPeriod second) :
    ∃ winding : Int,
      winding +ᵥ
          (ambientProjectionLocalHomeomorph period hPeriod).localInverseAt first base =
        (ambientProjectionLocalHomeomorph period hPeriod).localInverseAt second base := by
  let hf := ambientProjectionLocalHomeomorph period hPeriod
  let firstSection := hf.localInverseAt first
  let secondSection := hf.localInverseAt second
  have hFirstProjection :
      mappingTorusMk (reflectedSphereData period hPeriod) (firstSection base) = base :=
    hf.apply_localInverseAt_of_mem hBase.1
  have hSecondProjection :
      mappingTorusMk (reflectedSphereData period hPeriod) (secondSection base) = base :=
    hf.apply_localInverseAt_of_mem hBase.2
  exact (mappingTorusMk_eq_iff_exists_vadd
    (reflectedSphereData period hPeriod) (secondSection base) (firstSection base)).1
      (hSecondProjection.trans hFirstProjection.symm)

/-- Unique deck winding relating two covering local inverses on an overlap. -/
def ambientSignTransitionWinding
    (first second : EffectiveCover period hPeriod)
    (base : EffectiveQuotient period hPeriod) : Int := by
  classical
  exact if hBase : base ∈ ambientSignBundleBaseSet period hPeriod first ∩
        ambientSignBundleBaseSet period hPeriod second then
      Classical.choose
        (exists_ambientSignTransitionWinding period hPeriod first second base hBase)
    else 0

theorem ambientSignTransitionWinding_vadd
    (first second : EffectiveCover period hPeriod)
    (base : EffectiveQuotient period hPeriod)
    (hBase : base ∈ ambientSignBundleBaseSet period hPeriod first ∩
      ambientSignBundleBaseSet period hPeriod second) :
    ambientSignTransitionWinding period hPeriod first second base +ᵥ
        (ambientProjectionLocalHomeomorph period hPeriod).localInverseAt first base =
      (ambientProjectionLocalHomeomorph period hPeriod).localInverseAt second base := by
  rw [ambientSignTransitionWinding, dif_pos hBase]
  exact Classical.choose_spec
    (exists_ambientSignTransitionWinding period hPeriod first second base hBase)

theorem ambientSignTransitionWinding_self
    (anchor : EffectiveCover period hPeriod)
    (base : EffectiveQuotient period hPeriod)
    (hBase : base ∈ ambientSignBundleBaseSet period hPeriod anchor) :
    ambientSignTransitionWinding period hPeriod anchor anchor base = 0 := by
  apply IsCancelVAdd.right_cancel _ _
    ((ambientProjectionLocalHomeomorph period hPeriod).localInverseAt anchor base)
  rw [zero_vadd]
  exact ambientSignTransitionWinding_vadd period hPeriod anchor anchor base
    ⟨hBase, hBase⟩

theorem ambientSignTransitionWinding_add
    (first second third : EffectiveCover period hPeriod)
    (base : EffectiveQuotient period hPeriod)
    (hBase : base ∈ ambientSignBundleBaseSet period hPeriod first ∩
        ambientSignBundleBaseSet period hPeriod second ∩
        ambientSignBundleBaseSet period hPeriod third) :
    ambientSignTransitionWinding period hPeriod second third base +
        ambientSignTransitionWinding period hPeriod first second base =
      ambientSignTransitionWinding period hPeriod first third base := by
  let firstLift :=
    (ambientProjectionLocalHomeomorph period hPeriod).localInverseAt first base
  have hFirstSecond := ambientSignTransitionWinding_vadd period hPeriod first second base
    ⟨hBase.1.1, hBase.1.2⟩
  have hSecondThird := ambientSignTransitionWinding_vadd period hPeriod second third base
    ⟨hBase.1.2, hBase.2⟩
  have hFirstThird := ambientSignTransitionWinding_vadd period hPeriod first third base
    ⟨hBase.1.1, hBase.2⟩
  apply IsCancelVAdd.right_cancel _ _ firstLift
  rw [add_vadd, hFirstSecond, hSecondThird, hFirstThird]

theorem ambientSignTransitionWinding_eventuallyEq
    (first second : EffectiveCover period hPeriod)
    (base : EffectiveQuotient period hPeriod)
    (hBase : base ∈ ambientSignBundleBaseSet period hPeriod first ∩
      ambientSignBundleBaseSet period hPeriod second) :
    Filter.EventuallyEq (nhds base)
      (ambientSignTransitionWinding period hPeriod first second)
      (fun _ ↦ ambientSignTransitionWinding period hPeriod first second base) := by
  let winding := ambientSignTransitionWinding period hPeriod first second base
  have hSections := localInverseAt_eventuallyEq_vadd_of_mem
    (reflectedSphereData period hPeriod) first second base hBase.1 hBase.2 winding
      (ambientSignTransitionWinding_vadd period hPeriod first second base hBase)
  have hOverlap : ambientSignBundleBaseSet period hPeriod first ∩
      ambientSignBundleBaseSet period hPeriod second ∈ nhds base :=
    ((ambientSignBundleBaseSet_isOpen period hPeriod first).inter
      (ambientSignBundleBaseSet_isOpen period hPeriod second)).mem_nhds hBase
  filter_upwards [hSections, hOverlap] with nearby hSectionsNearby hNearby
  apply IsCancelVAdd.right_cancel _ _
    ((ambientProjectionLocalHomeomorph period hPeriod).localInverseAt first nearby)
  exact (ambientSignTransitionWinding_vadd period hPeriod first second nearby hNearby).trans
    hSectionsNearby

/-- Continuous linear sign action on the real model fiber. -/
def ambientNormalSignCLM (winding : Int) : Real →L[Real] Real :=
  (normalSignRepresentation winding : Real) • ContinuousLinearMap.id Real Real

@[simp]
theorem ambientNormalSignCLM_apply (winding : Int) (coefficient : Real) :
    ambientNormalSignCLM winding coefficient =
      (normalSignRepresentation winding : Real) * coefficient := by
  simp [ambientNormalSignCLM]

private theorem continuousOn_ambientSignTransition
    (first second : EffectiveCover period hPeriod) :
    ContinuousOn
      (fun base ↦ ambientNormalSignCLM
        (ambientSignTransitionWinding period hPeriod first second base))
      (ambientSignBundleBaseSet period hPeriod first ∩
        ambientSignBundleBaseSet period hPeriod second) := by
  intro base hBase
  let overlap := ambientSignBundleBaseSet period hPeriod first ∩
    ambientSignBundleBaseSet period hPeriod second
  have hWindingEq : Filter.EventuallyEq (nhdsWithin base overlap)
      (ambientSignTransitionWinding period hPeriod first second)
      (fun _ ↦ ambientSignTransitionWinding period hPeriod first second base) :=
    (ambientSignTransitionWinding_eventuallyEq period hPeriod first second base hBase).filter_mono
      inf_le_left
  have hNormalEq := hWindingEq.fun_comp ambientNormalSignCLM
  exact (continuousWithinAt_const : ContinuousWithinAt
      (fun _ : EffectiveQuotient period hPeriod ↦
        ambientNormalSignCLM
          (ambientSignTransitionWinding period hPeriod first second base))
      overlap base).congr_of_eventuallyEq_of_mem hNormalEq hBase

/-- Genuine rank-one sign bundle on the effective four-dimensional quotient. -/
def ambientNormalSignVectorBundleCore :
    VectorBundleCore Real (EffectiveQuotient period hPeriod) Real
      (EffectiveCover period hPeriod) where
  baseSet := ambientSignBundleBaseSet period hPeriod
  isOpen_baseSet := ambientSignBundleBaseSet_isOpen period hPeriod
  indexAt := ambientSignBundleIndexAt period hPeriod
  mem_baseSet_at := mem_ambientSignBundleBaseSet_indexAt period hPeriod
  coordChange first second base :=
    ambientNormalSignCLM
      (ambientSignTransitionWinding period hPeriod first second base)
  coordChange_self anchor base hBase coefficient := by
    simp [ambientSignTransitionWinding_self period hPeriod anchor base hBase,
      ambientNormalSignCLM, normalSignRepresentation]
  continuousOn_coordChange :=
    continuousOn_ambientSignTransition period hPeriod
  coordChange_comp first second third base hBase coefficient := by
    simp only [ambientNormalSignCLM_apply]
    rw [← mul_assoc, ← Units.val_mul, ← normal_sign_add,
      ambientSignTransitionWinding_add period hPeriod first second third base hBase]

/-- Fiber family of the ambient sign bundle. -/
abbrev AmbientNormalSignFiber :=
  (ambientNormalSignVectorBundleCore period hPeriod).Fiber

theorem ambientNormalSignFiber_isVectorBundle :
    VectorBundle Real Real (AmbientNormalSignFiber period hPeriod) :=
  inferInstance

private theorem contMDiffOn_ambientSignTransition
    (first second : EffectiveCover period hPeriod) :
    letI : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
      reflectedSphereQuotientChartedSpace period hPeriod
    ContMDiffOn coverModelWithCorners
      (modelWithCornersSelf Real (Real →L[Real] Real)) ω
      (fun base ↦ ambientNormalSignCLM
        (ambientSignTransitionWinding period hPeriod first second base))
      (ambientSignBundleBaseSet period hPeriod first ∩
        ambientSignBundleBaseSet period hPeriod second) := by
  letI : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
    reflectedSphereQuotientChartedSpace period hPeriod
  intro base hBase
  let overlap := ambientSignBundleBaseSet period hPeriod first ∩
    ambientSignBundleBaseSet period hPeriod second
  have hWindingEq : Filter.EventuallyEq (nhdsWithin base overlap)
      (ambientSignTransitionWinding period hPeriod first second)
      (fun _ ↦ ambientSignTransitionWinding period hPeriod first second base) :=
    (ambientSignTransitionWinding_eventuallyEq period hPeriod first second base hBase).filter_mono
      inf_le_left
  have hNormalEq := hWindingEq.fun_comp ambientNormalSignCLM
  exact (contMDiffWithinAt_const : ContMDiffWithinAt coverModelWithCorners
      (modelWithCornersSelf Real (Real →L[Real] Real)) ω
      (fun _ : EffectiveQuotient period hPeriod ↦
        ambientNormalSignCLM
          (ambientSignTransitionWinding period hPeriod first second base))
      overlap base).congr_of_eventuallyEq_of_mem hNormalEq hBase

theorem ambientNormalSignVectorBundleCore_isContMDiff :
    letI : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
      reflectedSphereQuotientChartedSpace period hPeriod
    (ambientNormalSignVectorBundleCore period hPeriod).IsContMDiff
      coverModelWithCorners ω := by
  letI : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
    reflectedSphereQuotientChartedSpace period hPeriod
  constructor
  exact contMDiffOn_ambientSignTransition period hPeriod

/-- The sign cocycle is an actual analytic real line bundle on the effective
four-manifold. -/
theorem ambientNormalSignFiber_isContMDiffVectorBundle :
    letI : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
      reflectedSphereQuotientChartedSpace period hPeriod
    letI : (ambientNormalSignVectorBundleCore period hPeriod).IsContMDiff
        coverModelWithCorners ω :=
      ambientNormalSignVectorBundleCore_isContMDiff period hPeriod
    ContMDiffVectorBundle ω Real (AmbientNormalSignFiber period hPeriod)
      coverModelWithCorners := by
  letI : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
    reflectedSphereQuotientChartedSpace period hPeriod
  letI : (ambientNormalSignVectorBundleCore period hPeriod).IsContMDiff
      coverModelWithCorners ω :=
    ambientNormalSignVectorBundleCore_isContMDiff period hPeriod
  infer_instance

theorem normalSignRepresentation_mul_self (winding : Int) :
    (normalSignRepresentation winding : Real) *
        (normalSignRepresentation winding : Real) = 1 := by
  rw [← Units.val_mul, ← normal_sign_add]
  rw [normal_sign_even (winding + winding) ⟨winding, rfl⟩]
  rfl

theorem normalSignRepresentation_neg (winding : Int) :
    normalSignRepresentation (-winding) = normalSignRepresentation winding := by
  simp [normalSignRepresentation, even_neg]

/-- Canonical comparison from the smooth core model to the original orbit
presentation of the associated sign line. -/
def ambientNormalSignBundleToOrbit :
    Bundle.TotalSpace Real (AmbientNormalSignFiber period hPeriod) →
      AmbientNormalSignOrbitLine period hPeriod :=
  fun point ↦
    ambientNormalSignLineMk period hPeriod
      ⟨ambientSignBundleIndexAt period hPeriod point.1, point.2⟩

private def ambientNormalSignFiberOfReal
    (base : EffectiveQuotient period hPeriod) (coefficient : Real) :
    AmbientNormalSignFiber period hPeriod base :=
  coefficient

@[simp]
theorem ambientNormalSignBundleToOrbit_projection
    (point : Bundle.TotalSpace Real
      (AmbientNormalSignFiber period hPeriod)) :
    ambientNormalSignLineProjection period hPeriod
        (ambientNormalSignBundleToOrbit period hPeriod point) = point.1 := by
  exact ambientSignBundleIndexAt_projects period hPeriod point.1

theorem ambientNormalSignBundleToOrbit_surjective :
    Function.Surjective (ambientNormalSignBundleToOrbit period hPeriod) := by
  intro orbitPoint
  induction orbitPoint using Quotient.inductionOn with
  | _ representative =>
      let base := mappingTorusMk (reflectedSphereData period hPeriod)
        representative.base
      have hProjection :
          mappingTorusMk (reflectedSphereData period hPeriod)
              representative.base =
            mappingTorusMk (reflectedSphereData period hPeriod)
              (ambientSignBundleIndexAt period hPeriod base) := by
        exact (ambientSignBundleIndexAt_projects period hPeriod base).symm
      obtain ⟨winding, hWinding⟩ :=
        (mappingTorusMk_eq_iff_exists_vadd
          (reflectedSphereData period hPeriod) representative.base
          (ambientSignBundleIndexAt period hPeriod base)).1 hProjection
      let coefficient :=
        (normalSignRepresentation winding : Real) * representative.coefficient
      let fiberCoefficient :=
        ambientNormalSignFiberOfReal period hPeriod base coefficient
      refine ⟨(⟨base, fiberCoefficient⟩ : Bundle.TotalSpace Real
        (AmbientNormalSignFiber period hPeriod)), ?_⟩
      change ambientNormalSignLineMk period hPeriod
          ⟨ambientSignBundleIndexAt period hPeriod base, coefficient⟩ =
        ambientNormalSignLineMk period hPeriod representative
      apply Quotient.sound
      change AddAction.orbitRel Int (AmbientNormalSignCover period hPeriod)
        ⟨ambientSignBundleIndexAt period hPeriod base, coefficient⟩ representative
      rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff]
      refine ⟨-winding, ?_⟩
      apply AmbientNormalSignCover.ext
      · change (-winding) +ᵥ representative.base =
          ambientSignBundleIndexAt period hPeriod base
        rw [← hWinding, ← add_vadd]
        simp
      · change
          (normalSignRepresentation (-winding) : Real) *
              representative.coefficient = coefficient
        rw [normalSignRepresentation_neg]

theorem ambientNormalSignBundleToOrbit_injective :
    Function.Injective (ambientNormalSignBundleToOrbit period hPeriod) := by
  rintro ⟨firstBase, firstCoefficient⟩ ⟨secondBase, secondCoefficient⟩ hOrbit
  change Real at firstCoefficient secondCoefficient
  have hBase : firstBase = secondBase := by
    have hProjection := congrArg
      (ambientNormalSignLineProjection period hPeriod) hOrbit
    simpa only [ambientNormalSignBundleToOrbit_projection] using hProjection
  subst secondBase
  have hRelation :
      AddAction.orbitRel Int (AmbientNormalSignCover period hPeriod)
        ⟨ambientSignBundleIndexAt period hPeriod firstBase, firstCoefficient⟩
        ⟨ambientSignBundleIndexAt period hPeriod firstBase, secondCoefficient⟩ := by
    exact Quotient.exact hOrbit
  rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hRelation
  rcases hRelation with ⟨winding, hWinding⟩
  have hBaseWinding := congrArg AmbientNormalSignCover.base hWinding
  change winding +ᵥ ambientSignBundleIndexAt period hPeriod firstBase =
      ambientSignBundleIndexAt period hPeriod firstBase at hBaseWinding
  have hWindingZero : winding = 0 := by
    apply IsCancelVAdd.right_cancel _ _
      (ambientSignBundleIndexAt period hPeriod firstBase)
    simpa using hBaseWinding
  subst winding
  have hCoefficient := congrArg AmbientNormalSignCover.coefficient hWinding
  change (normalSignRepresentation 0 : Real) * secondCoefficient =
      firstCoefficient at hCoefficient
  simp [normalSignRepresentation] at hCoefficient
  subst firstCoefficient
  rfl

/-- The smooth-core total space and the previously constructed orbit line are
canonically equivalent over the same quotient base.  The smooth structure is
the one supplied by the vector-bundle core. -/
def ambientNormalSignBundleEquivOrbitLine :
    Bundle.TotalSpace Real (AmbientNormalSignFiber period hPeriod) ≃
      AmbientNormalSignOrbitLine period hPeriod :=
  Equiv.ofBijective (ambientNormalSignBundleToOrbit period hPeriod)
    ⟨ambientNormalSignBundleToOrbit_injective period hPeriod,
      ambientNormalSignBundleToOrbit_surjective period hPeriod⟩

theorem ambientNormalSignBundleEquivOrbitLine_projection
    (point : Bundle.TotalSpace Real
      (AmbientNormalSignFiber period hPeriod)) :
    ambientNormalSignLineProjection period hPeriod
        (ambientNormalSignBundleEquivOrbitLine period hPeriod point) = point.1 :=
  ambientNormalSignBundleToOrbit_projection period hPeriod point

theorem SmoothAmbientNormalSignLift.contMDiff_on_effectiveCover
    (lift : SmoothAmbientNormalSignLift period) :
    letI : ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
      reflectedSphereCoverChartedSpace period hPeriod
    ContMDiff coverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (fun point : EffectiveCover period hPeriod ↦
        lift (coverHomeomorphProd
          (reflectedSphereData period hPeriod) point)) := by
  letI : ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
    reflectedSphereCoverChartedSpace period hPeriod
  exact lift.contMDiff_toFun.comp
    (chartedSpacePullback_toFun_contMDiff coverModelWithCorners ∞
      (coverHomeomorphProd (reflectedSphereData period hPeriod)))

/-- Fiber coefficient in the preferred chart selected by the bundle core. -/
def ambientNormalSignSectionFiber
    (lift : SmoothAmbientNormalSignLift period)
    (base : EffectiveQuotient period hPeriod) :
    AmbientNormalSignFiber period hPeriod base :=
  lift (coverHomeomorphProd (reflectedSphereData period hPeriod)
    (ambientSignBundleIndexAt period hPeriod base))

/-- Total-space section determined by a smooth equivariant cover coefficient. -/
def ambientNormalSignBundleSection
    (lift : SmoothAmbientNormalSignLift period) :
    EffectiveQuotient period hPeriod →
      Bundle.TotalSpace Real (AmbientNormalSignFiber period hPeriod) :=
  fun base ↦ ⟨base, ambientNormalSignSectionFiber period hPeriod lift base⟩

@[simp]
theorem ambientNormalSignBundleSection_proj
    (lift : SmoothAmbientNormalSignLift period) :
    Bundle.TotalSpace.proj ∘
        ambientNormalSignBundleSection period hPeriod lift = id := by
  rfl

/-- In a covering chart, the bundle section has exactly the original
equivariant coefficient evaluated at that chart's local lift. -/
theorem ambientNormalSignBundleSection_localTriv
    (lift : SmoothAmbientNormalSignLift period)
    (anchor : EffectiveCover period hPeriod)
    (base : EffectiveQuotient period hPeriod)
    (hBase : base ∈ ambientSignBundleBaseSet period hPeriod anchor) :
    ((ambientNormalSignVectorBundleCore period hPeriod).localTriv anchor
      (ambientNormalSignBundleSection period hPeriod lift base)).2 =
      lift (coverHomeomorphProd (reflectedSphereData period hPeriod)
        ((ambientProjectionLocalHomeomorph period hPeriod).localInverseAt
          anchor base)) := by
  change
    (normalSignRepresentation
        (ambientSignTransitionWinding period hPeriod
          (ambientSignBundleIndexAt period hPeriod base) anchor base) : Real) *
        lift (coverHomeomorphProd (reflectedSphereData period hPeriod)
          (ambientSignBundleIndexAt period hPeriod base)) =
      lift (coverHomeomorphProd (reflectedSphereData period hPeriod)
        ((ambientProjectionLocalHomeomorph period hPeriod).localInverseAt
          anchor base))
  have hIndexLocalInverse :
      (ambientProjectionLocalHomeomorph period hPeriod).localInverseAt
          (ambientSignBundleIndexAt period hPeriod base) base =
        ambientSignBundleIndexAt period hPeriod base := by
    have hSelf := (ambientProjectionLocalHomeomorph period hPeriod)
      |>.localInverseAt_apply_self
        (x := ambientSignBundleIndexAt period hPeriod base)
    rw [ambientSignBundleIndexAt_projects period hPeriod base] at hSelf
    exact hSelf
  have hTransition := ambientSignTransitionWinding_vadd period hPeriod
    (ambientSignBundleIndexAt period hPeriod base) anchor base
    ⟨mem_ambientSignBundleBaseSet_indexAt period hPeriod base, hBase⟩
  rw [hIndexLocalInverse] at hTransition
  rw [← hTransition,
    coverHomeomorphProd_vadd_eq_reflectedSphereProductDeck,
    SmoothAmbientNormalSignLift.deck_sign]

/-- The local inverse used to define the bundle charts is smooth at its
anchor.  This reconciles the topological covering choice with the independently
chosen local inverse supplied by the local-diffeomorphism theorem. -/
theorem ambientProjectionLocalInverseAt_contMDiffAt
    (anchor : EffectiveCover period hPeriod) :
    letI : ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
      reflectedSphereCoverChartedSpace period hPeriod
    letI : IsManifold coverModelWithCorners ω
        (EffectiveCover period hPeriod) :=
      reflectedSphereCover_isManifold period hPeriod
    letI : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
      reflectedSphereQuotientChartedSpace period hPeriod
    letI : IsManifold coverModelWithCorners ω
        (EffectiveQuotient period hPeriod) :=
      reflectedSphereQuotient_isManifold period hPeriod
    ContMDiffAt coverModelWithCorners coverModelWithCorners ∞
      ((ambientProjectionLocalHomeomorph period hPeriod).localInverseAt anchor)
      (mappingTorusMk (reflectedSphereData period hPeriod) anchor) := by
  letI : ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
    reflectedSphereCoverChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (EffectiveCover period hPeriod) :=
    reflectedSphereCover_isManifold period hPeriod
  letI : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
    reflectedSphereQuotientChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
    reflectedSphereQuotient_isManifold period hPeriod
  let projection :=
    mappingTorusMk (reflectedSphereData period hPeriod)
  let topologicalInverse :=
    (ambientProjectionLocalHomeomorph period hPeriod).localInverseAt anchor
  have hProjection :
      IsLocalDiffeomorph coverModelWithCorners coverModelWithCorners ω projection :=
    reflectedSphere_projection_isLocalDiffeomorph period hPeriod
  let smoothInverse := (hProjection anchor).localInverse
  have hSmooth : ContMDiffAt coverModelWithCorners coverModelWithCorners ∞
      smoothInverse (projection anchor) :=
    (hProjection anchor).localInverse_contMDiffAt.of_le (by simp)
  apply hSmooth.congr_of_eventuallyEq
  have hSmoothAt : smoothInverse (projection anchor) = anchor :=
    (hProjection anchor).localInverse_left_inv
      (hProjection anchor).localInverse_mem_target
  have hTopologicalSource : topologicalInverse.source ∈ nhds (projection anchor) :=
    topologicalInverse.open_source.mem_nhds
      ((ambientProjectionLocalHomeomorph period hPeriod)
        |>.apply_self_mem_localInverseAt_source)
  have hSmoothIntoTarget :
      ∀ᶠ nearby in nhds (projection anchor),
        smoothInverse nearby ∈ topologicalInverse.target := by
    have hTarget : topologicalInverse.target ∈ nhds anchor :=
      topologicalInverse.open_target.mem_nhds
        ((ambientProjectionLocalHomeomorph period hPeriod)
          |>.self_mem_localInverseAt_target)
    have hTendsto : Filter.Tendsto smoothInverse
        (nhds (projection anchor)) (nhds anchor) := by
      exact (congrArg nhds hSmoothAt) ▸ hSmooth.continuousAt
    exact hTendsto hTarget
  have hSmoothRight := (hProjection anchor).localInverse_eventuallyEq_right
  filter_upwards [hTopologicalSource, hSmoothIntoTarget, hSmoothRight]
    with nearby hSource hTarget hRight
  symm
  apply (ambientProjectionLocalHomeomorph period hPeriod)
    |>.injOn_localInverseAt_target hTarget
      (topologicalInverse.map_source hSource)
  exact hRight.trans
    ((ambientProjectionLocalHomeomorph period hPeriod)
      |>.apply_localInverseAt_of_mem hSource).symm

theorem ambientNormalSignBundleSection_contMDiff
    (lift : SmoothAmbientNormalSignLift period) :
    letI : ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
      reflectedSphereCoverChartedSpace period hPeriod
    letI : IsManifold coverModelWithCorners ω
        (EffectiveCover period hPeriod) :=
      reflectedSphereCover_isManifold period hPeriod
    letI : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
      reflectedSphereQuotientChartedSpace period hPeriod
    letI : IsManifold coverModelWithCorners ω
        (EffectiveQuotient period hPeriod) :=
      reflectedSphereQuotient_isManifold period hPeriod
    letI : (ambientNormalSignVectorBundleCore period hPeriod).IsContMDiff
        coverModelWithCorners ω :=
      ambientNormalSignVectorBundleCore_isContMDiff period hPeriod
    ContMDiff coverModelWithCorners
      (coverModelWithCorners.prod (modelWithCornersSelf Real Real)) ∞
      (ambientNormalSignBundleSection period hPeriod lift) := by
  letI : ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
    reflectedSphereCoverChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (EffectiveCover period hPeriod) :=
    reflectedSphereCover_isManifold period hPeriod
  letI : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
    reflectedSphereQuotientChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
    reflectedSphereQuotient_isManifold period hPeriod
  letI : (ambientNormalSignVectorBundleCore period hPeriod).IsContMDiff
      coverModelWithCorners ω :=
    ambientNormalSignVectorBundleCore_isContMDiff period hPeriod
  intro base
  let anchor := ambientSignBundleIndexAt period hPeriod base
  let localTriv :=
    (ambientNormalSignVectorBundleCore period hPeriod).localTriv anchor
  letI : MemTrivializationAtlas localTriv := by
    refine ⟨⟨anchor, ?_⟩⟩
    rfl
  have hBase : base ∈ ambientSignBundleBaseSet period hPeriod anchor :=
    mem_ambientSignBundleBaseSet_indexAt period hPeriod base
  have hSource :
      ambientNormalSignBundleSection period hPeriod lift base ∈ localTriv.source := by
    rw [localTriv.mem_source]
    exact hBase
  rw [localTriv.contMDiffAt_iff hSource]
  constructor
  · exact contMDiffAt_id
  · have hCoverSmooth :=
      SmoothAmbientNormalSignLift.contMDiff_on_effectiveCover
        period hPeriod lift
    have hLocalSmooth :
        ContMDiffAt coverModelWithCorners (modelWithCornersSelf Real Real) ∞
          ((fun point : EffectiveCover period hPeriod ↦
              lift (coverHomeomorphProd
                (reflectedSphereData period hPeriod) point)) ∘
            (ambientProjectionLocalHomeomorph period hPeriod).localInverseAt
              anchor) base := by
      have hBaseProjection :
          mappingTorusMk (reflectedSphereData period hPeriod) anchor = base :=
        ambientSignBundleIndexAt_projects period hPeriod base
      rw [← hBaseProjection]
      exact hCoverSmooth.contMDiffAt.comp _
        (ambientProjectionLocalInverseAt_contMDiffAt period hPeriod anchor)
    apply hLocalSmooth.congr_of_eventuallyEq
    filter_upwards [
      (ambientSignBundleBaseSet_isOpen period hPeriod anchor).mem_nhds hBase]
      with nearby hNearby
    exact ambientNormalSignBundleSection_localTriv period hPeriod lift
      anchor nearby hNearby

/-- Under the canonical equivalence, the smooth-core section is exactly the
previous orbit-quotient section, not merely an abstract section with the same
projection. -/
theorem ambientNormalSignBundleToOrbit_section
    (lift : SmoothAmbientNormalSignLift period)
    (base : EffectiveQuotient period hPeriod) :
    ambientNormalSignBundleToOrbit period hPeriod
        (ambientNormalSignBundleSection period hPeriod lift base) =
      ambientNormalSignOrbitSection period hPeriod lift base := by
  let anchor := ambientSignBundleIndexAt period hPeriod base
  have hSectionBase :
      ambientNormalSignOrbitSection period hPeriod lift base =
        ambientNormalSignOrbitSection period hPeriod lift
          (mappingTorusMk (reflectedSphereData period hPeriod) anchor) :=
    congrArg (ambientNormalSignOrbitSection period hPeriod lift)
      (ambientSignBundleIndexAt_projects period hPeriod base).symm
  rw [hSectionBase, ambientNormalSignOrbitSection_mk]
  rfl

/-- Bundled smooth section of the analytic sign line associated with an
equivariant smooth cover coefficient. -/
def ambientNormalSignSmoothSection
    (lift : SmoothAmbientNormalSignLift period) :
    letI : ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
      reflectedSphereCoverChartedSpace period hPeriod
    letI : IsManifold coverModelWithCorners ω
        (EffectiveCover period hPeriod) :=
      reflectedSphereCover_isManifold period hPeriod
    letI : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
      reflectedSphereQuotientChartedSpace period hPeriod
    letI : IsManifold coverModelWithCorners ω
        (EffectiveQuotient period hPeriod) :=
      reflectedSphereQuotient_isManifold period hPeriod
    letI : (ambientNormalSignVectorBundleCore period hPeriod).IsContMDiff
        coverModelWithCorners ω :=
      ambientNormalSignVectorBundleCore_isContMDiff period hPeriod
    ContMDiffSection coverModelWithCorners Real ∞
      (AmbientNormalSignFiber period hPeriod) := by
  letI : ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
    reflectedSphereCoverChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (EffectiveCover period hPeriod) :=
    reflectedSphereCover_isManifold period hPeriod
  letI : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
    reflectedSphereQuotientChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
    reflectedSphereQuotient_isManifold period hPeriod
  letI : (ambientNormalSignVectorBundleCore period hPeriod).IsContMDiff
      coverModelWithCorners ω :=
    ambientNormalSignVectorBundleCore_isContMDiff period hPeriod
  exact ⟨ambientNormalSignSectionFiber period hPeriod lift,
    ambientNormalSignBundleSection_contMDiff period hPeriod lift⟩

/-- The globally extended latitude current is a genuine smooth section of the
ambient sign line. -/
def equatorialBandScalarCurrentSmoothSignSection
    (field test : SmoothQuotientField period hPeriod Real) :
    letI : ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
      reflectedSphereCoverChartedSpace period hPeriod
    letI : IsManifold coverModelWithCorners ω
        (EffectiveCover period hPeriod) :=
      reflectedSphereCover_isManifold period hPeriod
    letI : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
      reflectedSphereQuotientChartedSpace period hPeriod
    letI : IsManifold coverModelWithCorners ω
        (EffectiveQuotient period hPeriod) :=
      reflectedSphereQuotient_isManifold period hPeriod
    letI : (ambientNormalSignVectorBundleCore period hPeriod).IsContMDiff
        coverModelWithCorners ω :=
      ambientNormalSignVectorBundleCore_isContMDiff period hPeriod
    ContMDiffSection coverModelWithCorners Real ∞
      (AmbientNormalSignFiber period hPeriod) :=
  ambientNormalSignSmoothSection period hPeriod
    (equatorialBandScalarCurrentNormalSignLift period hPeriod field test)

theorem equatorialBandScalarCurrentSmoothSection_toOrbit
    (field test : SmoothQuotientField period hPeriod Real)
    (base : EffectiveQuotient period hPeriod) :
    ambientNormalSignBundleToOrbit period hPeriod
        (ambientNormalSignBundleSection period hPeriod
          (equatorialBandScalarCurrentNormalSignLift period hPeriod field test)
          base) =
      equatorialBandScalarCurrentNormalSignSection period hPeriod field test base :=
  ambientNormalSignBundleToOrbit_section period hPeriod _ base

theorem equatorialBandScalarCurrentSmoothSignSection_localTriv
    (field test : SmoothQuotientField period hPeriod Real)
    (anchor : EffectiveCover period hPeriod)
    (base : EffectiveQuotient period hPeriod)
    (hBase : base ∈ ambientSignBundleBaseSet period hPeriod anchor) :
    letI : ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
      reflectedSphereCoverChartedSpace period hPeriod
    letI : IsManifold coverModelWithCorners ω
        (EffectiveCover period hPeriod) :=
      reflectedSphereCover_isManifold period hPeriod
    letI : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
      reflectedSphereQuotientChartedSpace period hPeriod
    letI : IsManifold coverModelWithCorners ω
        (EffectiveQuotient period hPeriod) :=
      reflectedSphereQuotient_isManifold period hPeriod
    letI : (ambientNormalSignVectorBundleCore period hPeriod).IsContMDiff
        coverModelWithCorners ω :=
      ambientNormalSignVectorBundleCore_isContMDiff period hPeriod
    ((ambientNormalSignVectorBundleCore period hPeriod).localTriv anchor
      ⟨base, equatorialBandScalarCurrentSmoothSignSection
        period hPeriod field test base⟩).2 =
      equatorialBandScalarCurrentZeroExtension period hPeriod field test
        (coverHomeomorphProd (reflectedSphereData period hPeriod)
          ((ambientProjectionLocalHomeomorph period hPeriod).localInverseAt
            anchor base)) := by
  letI : ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
    reflectedSphereCoverChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (EffectiveCover period hPeriod) :=
    reflectedSphereCover_isManifold period hPeriod
  letI : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
    reflectedSphereQuotientChartedSpace period hPeriod
  letI : IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
    reflectedSphereQuotient_isManifold period hPeriod
  letI : (ambientNormalSignVectorBundleCore period hPeriod).IsContMDiff
      coverModelWithCorners ω :=
    ambientNormalSignVectorBundleCore_isContMDiff period hPeriod
  exact ambientNormalSignBundleSection_localTriv period hPeriod
    (equatorialBandScalarCurrentNormalSignLift period hPeriod field test)
      anchor base hBase

end

end P0EFTJanusEquatorialBandScalarCurrentSmoothSignBundle4D
end JanusFormal
