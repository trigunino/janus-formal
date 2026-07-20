import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D

/-!
# Positive-hemisphere model of the cut bulk

The reflected-sphere mapping torus cut along its one-sided equator is modeled
topologically by the closed positive hemisphere with doubled period and
identity monodromy.  Its boundary is the orientation double cover of the
throat.  No manifold-with-boundary or Stokes instance is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D

set_option autoImplicit false

open Set
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusThroatComplementSides

variable (period : Real) (hPeriod : period ≠ 0)

/-- Closed positive hemisphere of the concrete unit three-sphere. -/
def ClosedPositiveHemisphere :=
  {point : UnitThreeSphere // 0 ≤ point.1 0}

instance : TopologicalSpace ClosedPositiveHemisphere :=
  inferInstanceAs (TopologicalSpace {point : UnitThreeSphere // 0 ≤ point.1 0})

def closedPositiveHemisphereInclusion : ClosedPositiveHemisphere → UnitThreeSphere :=
  Subtype.val

theorem continuous_closedPositiveHemisphereInclusion :
    Continuous closedPositiveHemisphereInclusion :=
  continuous_subtype_val

/-- Doubled-period product data for the cut bulk. -/
def cutBulkData : MappingTorusData ClosedPositiveHemisphere where
  monodromy := Homeomorph.refl ClosedPositiveHemisphere
  period := doubledPeriod period
  period_ne_zero := doubledPeriod_ne_zero period hPeriod

abbrev PositiveHemisphereCutBulk := MappingTorus (cutBulkData period hPeriod)

private theorem refl_zpow_apply {X : Type} [TopologicalSpace X]
    (winding : Int) (point : X) :
    ((Homeomorph.refl X) ^ winding) point = point := by
  rw [show ((Homeomorph.refl X) ^ winding) point =
      ((Homeomorph.refl X) ^ winding).toEquiv point from rfl,
    homeomorph_toEquiv_zpow]
  rw [show (Homeomorph.refl X).toEquiv = 1 from rfl, one_zpow]
  rfl

private theorem sphereReflection_even_zpow
    (winding : Int) (point : UnitThreeSphere) :
    (sphereReflection ^ (2 * winding)) point = point := by
  rw [show (sphereReflection ^ (2 * winding)) =
      (sphereReflection ^ (2 : Int)) ^ winding by
        exact zpow_mul sphereReflection 2 winding]
  have hSquare : sphereReflection ^ (2 : Int) = 1 := by
    apply Homeomorph.ext
    intro current
    exact sphereReflection.apply_symm_apply current
  rw [hSquare, one_zpow]
  rfl

/-- Coordinate inclusion of the cut cover into the original ambient cover. -/
def cutBulkCoverToAmbient
    (point : MappingTorusCover (cutBulkData period hPeriod)) :
    MappingTorusCover (reflectedSphereData period hPeriod) :=
  ⟨point.fiber.1, point.time⟩

theorem continuous_cutBulkCoverToAmbient :
    Continuous (cutBulkCoverToAmbient period hPeriod) := by
  have hFiber : Continuous (fun point : MappingTorusCover (cutBulkData period hPeriod) ↦
      point.fiber.1) :=
    continuous_subtype_val.comp (continuous_fiber _)
  have hTime := continuous_time (cutBulkData period hPeriod)
  have h := (coverHomeomorphProd (reflectedSphereData period hPeriod)).symm.continuous.comp
    (hFiber.prodMk hTime)
  exact h.congr fun _ ↦ rfl

/-- A source winding is the even target winding. -/
theorem cutBulkCoverToAmbient_even_equivariant
    (winding : Int) (point : MappingTorusCover (cutBulkData period hPeriod)) :
    cutBulkCoverToAmbient period hPeriod (winding +ᵥ point) =
      (2 * winding) +ᵥ cutBulkCoverToAmbient period hPeriod point := by
  apply MappingTorusCover.ext
  · change (((Homeomorph.refl ClosedPositiveHemisphere) ^ winding)
        point.fiber).1 =
      (sphereReflection ^ (2 * winding)) point.fiber.1
    rw [refl_zpow_apply, sphereReflection_even_zpow]
  · change point.time + (winding : Real) * (2 * period) =
      point.time + ((2 * winding : Int) : Real) * period
    push_cast
    ring

/-- Quotient map from the cut model onto the original effective bulk. -/
def cutBulkToAmbient :
    PositiveHemisphereCutBulk period hPeriod →
      MappingTorus (reflectedSphereData period hPeriod) :=
  Quotient.map (cutBulkCoverToAmbient period hPeriod) fun first second hOrbit ↦ by
    change AddAction.orbitRel Int
      (MappingTorusCover (cutBulkData period hPeriod)) first second at hOrbit
    change AddAction.orbitRel Int
      (MappingTorusCover (reflectedSphereData period hPeriod))
      (cutBulkCoverToAmbient period hPeriod first)
      (cutBulkCoverToAmbient period hPeriod second)
    rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit ⊢
    rcases hOrbit with ⟨winding, hWinding⟩
    refine ⟨2 * winding, ?_⟩
    rw [← cutBulkCoverToAmbient_even_equivariant]
    exact congrArg (cutBulkCoverToAmbient period hPeriod) hWinding

@[simp] theorem cutBulkToAmbient_mk
    (point : MappingTorusCover (cutBulkData period hPeriod)) :
    cutBulkToAmbient period hPeriod
        (mappingTorusMk (cutBulkData period hPeriod) point) =
      mappingTorusMk (reflectedSphereData period hPeriod)
        (cutBulkCoverToAmbient period hPeriod point) := rfl

theorem continuous_cutBulkToAmbient :
    Continuous (cutBulkToAmbient period hPeriod) := by
  apply (continuous_quotient_mk'.comp
    (continuous_cutBulkCoverToAmbient period hPeriod)).quotient_lift

theorem cutBulkToAmbient_surjective :
    Function.Surjective (cutBulkToAmbient period hPeriod) := by
  intro bulk
  refine Quotient.inductionOn bulk ?_
  intro point
  by_cases hPositive : 0 ≤ point.fiber.1 0
  · let cutPoint : MappingTorusCover (cutBulkData period hPeriod) :=
      ⟨⟨point.fiber, hPositive⟩, point.time⟩
    exact ⟨mappingTorusMk (cutBulkData period hPeriod) cutPoint, rfl⟩
  · have hReflected : 0 ≤ (sphereReflection point.fiber).1 0 := by
      rw [sphereReflection_first_coordinate, neg_nonneg]
      exact le_of_not_ge hPositive
    let cutPoint : MappingTorusCover (cutBulkData period hPeriod) :=
      ⟨⟨sphereReflection point.fiber, hReflected⟩, point.time + period⟩
    refine ⟨mappingTorusMk (cutBulkData period hPeriod) cutPoint, ?_⟩
    rw [cutBulkToAmbient_mk, mappingTorusMk_eq_iff_exists_vadd]
    refine ⟨1, ?_⟩
    apply MappingTorusCover.ext
    · rfl
    · dsimp [cutPoint, cutBulkCoverToAmbient]
      simp [reflectedSphereData]

/-- Inclusion of the orientation-double throat into the cut model. -/
def cutBoundaryCoverToCutBulk
    (point : MappingTorusCover (orientationDoubleData period hPeriod)) :
    MappingTorusCover (cutBulkData period hPeriod) :=
  ⟨⟨equatorialSphereInclusion point.fiber, by
      exact le_of_eq point.fiber.2.2.symm⟩, point.time⟩

theorem cutBoundaryCoverToCutBulk_injective :
    Function.Injective (cutBoundaryCoverToCutBulk period hPeriod) := by
  intro first second hEqual
  apply MappingTorusCover.ext
  · apply equatorialSphereInclusion_injective
    exact congrArg (fun point ↦ point.fiber.1) hEqual
  · exact congrArg (fun point : MappingTorusCover (cutBulkData period hPeriod) ↦
      point.time) hEqual

theorem cutBoundaryCoverToCutBulk_equivariant
    (winding : Int)
    (point : MappingTorusCover (orientationDoubleData period hPeriod)) :
    cutBoundaryCoverToCutBulk period hPeriod (winding +ᵥ point) =
      winding +ᵥ cutBoundaryCoverToCutBulk period hPeriod point := by
  apply MappingTorusCover.ext
  · apply Subtype.ext
    change equatorialSphereInclusion
        (((Homeomorph.refl EquatorialTwoSphere) ^ winding) point.fiber) =
      (((Homeomorph.refl ClosedPositiveHemisphere) ^ winding)
        (cutBoundaryCoverToCutBulk period hPeriod point).fiber).1
    rw [refl_zpow_apply, refl_zpow_apply]
    rfl
  · rfl

def cutBoundaryInclusion :
    CutThroatBoundary period hPeriod → PositiveHemisphereCutBulk period hPeriod :=
  Quotient.map (cutBoundaryCoverToCutBulk period hPeriod) fun first second hOrbit ↦ by
    change AddAction.orbitRel Int
      (MappingTorusCover (orientationDoubleData period hPeriod)) first second at hOrbit
    change AddAction.orbitRel Int
      (MappingTorusCover (cutBulkData period hPeriod))
      (cutBoundaryCoverToCutBulk period hPeriod first)
      (cutBoundaryCoverToCutBulk period hPeriod second)
    rw [AddAction.orbitRel_apply, AddAction.mem_orbit_iff] at hOrbit ⊢
    rcases hOrbit with ⟨winding, hWinding⟩
    refine ⟨winding, ?_⟩
    rw [← cutBoundaryCoverToCutBulk_equivariant]
    exact congrArg (cutBoundaryCoverToCutBulk period hPeriod) hWinding

theorem cutBoundaryInclusion_injective :
    Function.Injective (cutBoundaryInclusion period hPeriod) := by
  intro first second
  refine Quotient.inductionOn first ?_
  intro firstRepresentative
  refine Quotient.inductionOn second ?_
  intro secondRepresentative hEqual
  change mappingTorusMk (cutBulkData period hPeriod)
      (cutBoundaryCoverToCutBulk period hPeriod firstRepresentative) =
    mappingTorusMk (cutBulkData period hPeriod)
      (cutBoundaryCoverToCutBulk period hPeriod secondRepresentative) at hEqual
  change mappingTorusMk (orientationDoubleData period hPeriod) firstRepresentative =
    mappingTorusMk (orientationDoubleData period hPeriod) secondRepresentative
  rw [mappingTorusMk_eq_iff_exists_vadd] at hEqual ⊢
  rcases hEqual with ⟨winding, hWinding⟩
  refine ⟨winding, ?_⟩
  apply cutBoundaryCoverToCutBulk_injective period hPeriod
  rw [cutBoundaryCoverToCutBulk_equivariant]
  exact hWinding

theorem continuous_cutBoundaryInclusion :
    Continuous (cutBoundaryInclusion period hPeriod) := by
  apply (continuous_quotient_mk'.comp ?_).quotient_lift
  have hFiber : Continuous (fun point :
      MappingTorusCover (orientationDoubleData period hPeriod) ↦
        (cutBoundaryCoverToCutBulk period hPeriod point).fiber) :=
    (continuous_equatorialSphereInclusion.comp (continuous_fiber _)).subtype_mk _
  have hTime := continuous_time (orientationDoubleData period hPeriod)
  have h := (coverHomeomorphProd (cutBulkData period hPeriod)).symm.continuous.comp
    (hFiber.prodMk hTime)
  exact h.congr fun _ ↦ rfl

/-- The cut boundary square commutes with the original bulk inclusion. -/
theorem cutBulkToAmbient_cutBoundaryInclusion
    (boundary : CutThroatBoundary period hPeriod) :
    cutBulkToAmbient period hPeriod
        (cutBoundaryInclusion period hPeriod boundary) =
      cutThroatBoundaryToBulk period hPeriod boundary := by
  refine Quotient.inductionOn boundary ?_
  intro representative
  change mappingTorusMk (reflectedSphereData period hPeriod)
      (fixedThroatCoverInclusion period hPeriod
        (orientationDoubleCoverHomeomorph period hPeriod representative)) =
    mappingTorusMk (reflectedSphereData period hPeriod)
      (fixedThroatCoverInclusion period hPeriod
        (orientationDoubleCoverHomeomorph period hPeriod representative))
  rfl

end P0EFTJanusMappingTorusPositiveHemisphereCutBulk4D
end JanusFormal
