import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothPTInvolution

/-!
# Complete analytic time flow on the effective D8 quotient

Real translation in the cover coordinate commutes with every integer deck
transformation.  It therefore descends to a genuine complete real action on
the effective four-dimensional mapping torus.  Every time slice is an
analytic diffeomorphism, with inverse given by the opposite time.

This is an actual nonzero geometric flow on the installed quotient.  It is
not the flow of an arbitrary diffeomorphism ghost and does not by itself
construct the induced nonlinear flow on the full field space.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCompleteTimeFlow4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusPTInvolution

variable {X : Type*} [TopologicalSpace X]

/-- Translation in the real coordinate of a mapping-torus cover. -/
def coverTimeTranslation (data : MappingTorusData X) (shift : Real) :
    MappingTorusCover data -> MappingTorusCover data :=
  fun point => ⟨point.fiber, point.time + shift⟩

@[simp]
theorem coverTimeTranslation_fiber
    (data : MappingTorusData X) (shift : Real)
    (point : MappingTorusCover data) :
    (coverTimeTranslation data shift point).fiber = point.fiber :=
  rfl

@[simp]
theorem coverTimeTranslation_time
    (data : MappingTorusData X) (shift : Real)
    (point : MappingTorusCover data) :
    (coverTimeTranslation data shift point).time = point.time + shift :=
  rfl

@[simp]
theorem coverTimeTranslation_zero
    (data : MappingTorusData X) (point : MappingTorusCover data) :
    coverTimeTranslation data 0 point = point := by
  ext <;> simp [coverTimeTranslation]

theorem coverTimeTranslation_add
    (data : MappingTorusData X) (first second : Real)
    (point : MappingTorusCover data) :
    coverTimeTranslation data (first + second) point =
      coverTimeTranslation data first
        (coverTimeTranslation data second point) := by
  ext
  · rfl
  · simp [coverTimeTranslation]
    ring

/-- Real time translation commutes exactly with the integer deck action. -/
theorem coverTimeTranslation_vadd
    (data : MappingTorusData X) (shift : Real) (winding : Int)
    (point : MappingTorusCover data) :
    coverTimeTranslation data shift (winding +ᵥ point) =
      winding +ᵥ coverTimeTranslation data shift point := by
  ext
  · rfl
  · simp [coverTimeTranslation]
    ring

/-- The descended real time translation on an arbitrary mapping torus. -/
def quotientTimeTranslation (data : MappingTorusData X) (shift : Real) :
    MappingTorus data -> MappingTorus data :=
  Quotient.map (coverTimeTranslation data shift) fun first second hOrbit => by
    change AddAction.orbitRel Int (MappingTorusCover data) first second at hOrbit
    change AddAction.orbitRel Int (MappingTorusCover data)
      (coverTimeTranslation data shift first)
      (coverTimeTranslation data shift second)
    rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit ⊢
    rcases hOrbit with ⟨winding, hWinding⟩
    exact ⟨winding, (coverTimeTranslation_vadd data shift winding second).symm.trans
      (congrArg (coverTimeTranslation data shift) hWinding)⟩

@[simp]
theorem quotientTimeTranslation_mk
    (data : MappingTorusData X) (shift : Real)
    (point : MappingTorusCover data) :
    quotientTimeTranslation data shift (mappingTorusMk data point) =
      mappingTorusMk data (coverTimeTranslation data shift point) :=
  rfl

@[simp]
theorem quotientTimeTranslation_zero
    (data : MappingTorusData X) (point : MappingTorus data) :
    quotientTimeTranslation data 0 point = point := by
  obtain ⟨point, rfl⟩ := mappingTorusMk_surjective data point
  simp

theorem quotientTimeTranslation_add
    (data : MappingTorusData X) (first second : Real)
    (point : MappingTorus data) :
    quotientTimeTranslation data (first + second) point =
      quotientTimeTranslation data first
        (quotientTimeTranslation data second point) := by
  obtain ⟨point, rfl⟩ := mappingTorusMk_surjective data point
  rw [quotientTimeTranslation_mk, quotientTimeTranslation_mk,
    quotientTimeTranslation_mk, coverTimeTranslation_add]

@[simp]
theorem quotientTimeTranslation_neg_left
    (data : MappingTorusData X) (shift : Real)
    (point : MappingTorus data) :
    quotientTimeTranslation data (-shift)
        (quotientTimeTranslation data shift point) = point := by
  rw [← quotientTimeTranslation_add]
  simp

@[simp]
theorem quotientTimeTranslation_neg_right
    (data : MappingTorusData X) (shift : Real)
    (point : MappingTorus data) :
    quotientTimeTranslation data shift
        (quotientTimeTranslation data (-shift) point) = point := by
  rw [← quotientTimeTranslation_add]
  simp

section SmoothDescent

variable {K E H : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup E] [NormedSpace K E]
  [TopologicalSpace H] [T2Space X] [LocallyCompactSpace X]

/-- A smooth cover translation descends smoothly through the quotient local
diffeomorphism. -/
theorem quotientTimeTranslation_contMDiff
    (I : ModelWithCorners K E H) (n : WithTop ENat)
    (data : MappingTorusData X)
    [ChartedSpace H (MappingTorusCover data)]
    [IsManifold I n (MappingTorusCover data)]
    (hDeck : ∀ winding : Int,
      ContMDiff I I n
        (winding +ᵥ · : MappingTorusCover data -> MappingTorusCover data))
    (shift : Real)
    (hTranslation : ContMDiff I I n (coverTimeTranslation data shift)) :
    letI : ChartedSpace H (MappingTorus data) :=
      mappingTorusSmoothChartedSpace data
    ContMDiff I I n (quotientTimeTranslation data shift) := by
  letI : ChartedSpace H (MappingTorus data) :=
    mappingTorusSmoothChartedSpace data
  letI : IsManifold I n (MappingTorus data) :=
    mappingTorus_isManifold_of_smooth_deck I n data hDeck
  have hProjection :=
    mappingTorus_projection_isLocalDiffeomorph I n data hDeck
  have hLift : ContMDiff I I n
      (fun point => mappingTorusMk data
        (coverTimeTranslation data shift point)) :=
    hProjection.contMDiff.comp hTranslation
  intro quotientPoint
  obtain ⟨anchor, rfl⟩ := mappingTorusMk_surjective data quotientPoint
  have hLocal := hProjection anchor
  have hLocalLift : ContMDiffAt I I n
      ((fun point => mappingTorusMk data
          (coverTimeTranslation data shift point)) ∘ hLocal.localInverse)
      (mappingTorusMk data anchor) :=
    hLift.contMDiffAt.comp _ hLocal.localInverse_contMDiffAt
  apply hLocalLift.congr_of_eventuallyEq
  filter_upwards [hLocal.localInverse_eventuallyEq_right] with point hPoint
  rw [Function.comp_apply, ← quotientTimeTranslation_mk]
  exact congrArg (quotientTimeTranslation data shift) hPoint.symm

end SmoothDescent

section EffectiveD8

open P0EFTJanusReflectionFixedThroat

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private theorem reflectedSphereProductTimeTranslation_contMDiff
    (shift : Real) :
    ContMDiff coverModelWithCorners coverModelWithCorners ω
      (fun point : UnitThreeSphere × Real => (point.1, point.2 + shift)) := by
  have hTime : ContMDiff 𝓘(Real, Real) 𝓘(Real, Real) ω
      (fun time : Real => time + shift) :=
    (contDiff_id.add contDiff_const).contMDiff
  exact (contMDiff_id.prodMap hTime).congr fun _ => rfl

/-- Every real translation is analytic on the reflected-sphere cover. -/
theorem effectiveCoverTimeTranslation_contMDiff (shift : Real) :
    ContMDiff coverModelWithCorners coverModelWithCorners ω
      (coverTimeTranslation (sphereData period hPeriod) shift) := by
  have hTo := chartedSpacePullback_toFun_contMDiff coverModelWithCorners ω
    (coverHomeomorphProd (sphereData period hPeriod))
  have hInv := chartedSpacePullback_invFun_contMDiff coverModelWithCorners ω
    (coverHomeomorphProd (sphereData period hPeriod))
  have hComposite := hInv.comp
    ((reflectedSphereProductTimeTranslation_contMDiff shift).comp hTo)
  exact hComposite.congr fun point => by
    apply MappingTorusCover.ext <;> rfl

/-- The actual complete time flow on the effective D8 quotient. -/
def effectiveTimeFlow (shift : Real) :
    EffectiveQuotient period hPeriod -> EffectiveQuotient period hPeriod :=
  quotientTimeTranslation (sphereData period hPeriod) shift

@[simp]
theorem effectiveTimeFlow_mk (shift : Real)
    (point : EffectiveCover period hPeriod) :
    effectiveTimeFlow period hPeriod shift
        (mappingTorusMk (sphereData period hPeriod) point) =
      mappingTorusMk (sphereData period hPeriod)
        (coverTimeTranslation (sphereData period hPeriod) shift point) :=
  rfl

@[simp]
theorem effectiveTimeFlow_zero
    (point : EffectiveQuotient period hPeriod) :
    effectiveTimeFlow period hPeriod 0 point = point :=
  quotientTimeTranslation_zero _ point

theorem effectiveTimeFlow_add (first second : Real)
    (point : EffectiveQuotient period hPeriod) :
    effectiveTimeFlow period hPeriod (first + second) point =
      effectiveTimeFlow period hPeriod first
        (effectiveTimeFlow period hPeriod second point) :=
  quotientTimeTranslation_add _ first second point

/-- Every slice of the complete D8 time flow is analytic. -/
theorem effectiveTimeFlow_contMDiff (shift : Real) :
    ContMDiff coverModelWithCorners coverModelWithCorners ω
      (effectiveTimeFlow period hPeriod shift) := by
  exact quotientTimeTranslation_contMDiff coverModelWithCorners ω
    (sphereData period hPeriod)
    (reflectedSphereCover_deck_contMDiff period hPeriod) shift
    (effectiveCoverTimeTranslation_contMDiff period hPeriod shift)

/-- PT conjugates the complete time flow to its opposite-time slice. -/
theorem reflectedSpherePT_effectiveTimeFlow (shift : Real)
    (point : EffectiveQuotient period hPeriod) :
    reflectedSpherePT period hPeriod
        (effectiveTimeFlow period hPeriod shift point) =
      effectiveTimeFlow period hPeriod (-shift)
        (reflectedSpherePT period hPeriod point) := by
  obtain ⟨representative, rfl⟩ :=
    mappingTorusMk_surjective (sphereData period hPeriod) point
  change mappingTorusTimeReversal (sphereData period hPeriod)
        sphereReflection_symm
        (quotientTimeTranslation (sphereData period hPeriod) shift
          (mappingTorusMk (sphereData period hPeriod) representative)) =
      quotientTimeTranslation (sphereData period hPeriod) (-shift)
        (mappingTorusTimeReversal (sphereData period hPeriod)
          sphereReflection_symm
          (mappingTorusMk (sphereData period hPeriod) representative))
  rw [quotientTimeTranslation_mk, mappingTorusTimeReversal_mk,
    mappingTorusTimeReversal_mk, quotientTimeTranslation_mk]
  apply congrArg (mappingTorusMk (sphereData period hPeriod))
  apply MappingTorusCover.ext
  · rfl
  · simp [coverTimeTranslation, timeReverseCover]
    ring

/-- Every time slice is an analytic diffeomorphism; its inverse is the
opposite-time slice. -/
def effectiveTimeFlowDiffeomorph (shift : Real) :
    EffectiveQuotient period hPeriod ≃ₘ^ω⟮
      coverModelWithCorners, coverModelWithCorners⟯
      EffectiveQuotient period hPeriod where
  toEquiv :=
    { toFun := effectiveTimeFlow period hPeriod shift
      invFun := effectiveTimeFlow period hPeriod (-shift)
      left_inv := quotientTimeTranslation_neg_left _ shift
      right_inv := quotientTimeTranslation_neg_right _ shift }
  contMDiff_toFun := effectiveTimeFlow_contMDiff period hPeriod shift
  contMDiff_invFun := effectiveTimeFlow_contMDiff period hPeriod (-shift)

/-- Packaged certificate that the D8 quotient carries an actual complete
analytic real action. -/
structure CompleteAnalyticRealAction where
  flow : Real -> EffectiveQuotient period hPeriod ->
    EffectiveQuotient period hPeriod
  flow_zero : ∀ point, flow 0 point = point
  flow_add : ∀ first second point,
    flow (first + second) point = flow first (flow second point)
  analytic_slice : ∀ shift : Real,
    ContMDiff coverModelWithCorners coverModelWithCorners ω (flow shift)
  diffeomorph_slice : Real ->
    EffectiveQuotient period hPeriod ≃ₘ^ω⟮
      coverModelWithCorners, coverModelWithCorners⟯
      EffectiveQuotient period hPeriod
  diffeomorph_slice_apply : ∀ shift point,
    diffeomorph_slice shift point = flow shift point

/-- Unconditional complete analytic action supplied by the mapping-torus
coordinate itself. -/
def effectiveCompleteAnalyticRealAction :
    CompleteAnalyticRealAction period hPeriod where
  flow := effectiveTimeFlow period hPeriod
  flow_zero := effectiveTimeFlow_zero period hPeriod
  flow_add := effectiveTimeFlow_add period hPeriod
  analytic_slice := effectiveTimeFlow_contMDiff period hPeriod
  diffeomorph_slice := effectiveTimeFlowDiffeomorph period hPeriod
  diffeomorph_slice_apply := by intros; rfl

private def timeFlowWitnessFiber : UnitThreeSphere :=
  ⟨fun index => if index = 0 then 1 else 0, by
    simp [OnUnitThreeSphere, radiusSquared]⟩

/-- A concrete quotient point used to certify that the complete action is not
the trivial action. -/
def timeFlowWitnessPoint : EffectiveQuotient period hPeriod :=
  mappingTorusMk (sphereData period hPeriod)
    ⟨timeFlowWitnessFiber, 0⟩

/-- Half a mapping-torus period moves the concrete witness point.  Thus the
complete real action is genuinely nontrivial. -/
theorem effectiveTimeFlow_halfPeriod_ne :
    effectiveTimeFlow period hPeriod (period / 2)
        (timeFlowWitnessPoint period hPeriod) ≠
      timeFlowWitnessPoint period hPeriod := by
  intro hEqual
  have hOrbit :
      mappingTorusMk (sphereData period hPeriod)
          (coverTimeTranslation (sphereData period hPeriod) (period / 2)
            ⟨timeFlowWitnessFiber, 0⟩) =
        mappingTorusMk (sphereData period hPeriod)
          ⟨timeFlowWitnessFiber, 0⟩ := by
    simpa [timeFlowWitnessPoint] using hEqual
  rcases (mappingTorusMk_eq_iff_exists_vadd
    (sphereData period hPeriod) _ _).1 hOrbit with ⟨winding, hWinding⟩
  have hTime := congrArg MappingTorusCover.time hWinding
  change (0 : Real) + (winding : Real) * period = 0 + period / 2 at hTime
  have hProduct : ((winding : Real) - (1 / 2 : Real)) * period = 0 := by
    calc
      ((winding : Real) - (1 / 2 : Real)) * period =
          (winding : Real) * period - period / 2 := by ring
      _ = 0 := by linarith
  have hCast : (winding : Real) = 1 / 2 := by
    have hDifference : (winding : Real) - (1 / 2 : Real) = 0 :=
      (mul_eq_zero.mp hProduct).resolve_right hPeriod
    linarith
  have hTwo : (2 : Real) * (winding : Real) = 1 := by
    linarith
  have hInteger : (2 * winding : Int) = 1 := by
    exact_mod_cast hTwo
  omega

/-- The installed complete analytic action is nontrivial. -/
theorem effectiveCompleteAnalyticRealAction_nontrivial :
    ∃ shift point,
      (effectiveCompleteAnalyticRealAction period hPeriod).flow shift point ≠ point :=
  ⟨period / 2, timeFlowWitnessPoint period hPeriod,
    effectiveTimeFlow_halfPeriod_ne period hPeriod⟩

theorem effective_complete_time_flow4D_closed :
    Nonempty (CompleteAnalyticRealAction period hPeriod) ∧
      ∃ shift point,
        (effectiveCompleteAnalyticRealAction period hPeriod).flow shift point ≠ point :=
  ⟨⟨effectiveCompleteAnalyticRealAction period hPeriod⟩,
    effectiveCompleteAnalyticRealAction_nontrivial period hPeriod⟩

end EffectiveD8

end

end P0EFTJanusMappingTorusCompleteTimeFlow4D
end JanusFormal
