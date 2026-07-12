import Mathlib

namespace JanusFormal
namespace P0EFTJanusReflectionFixedThroat

set_option autoImplicit false

/-- Coordinate model of the ambient Euclidean four-space. -/
abbrev R4Point := Fin 4 → ℝ

/-- Reflection of the first coordinate. -/
def reflectPoint (x : R4Point) : R4Point :=
  fun i => if i = 0 then -x i else x i

/-- The coordinate reflection is an involution. -/
@[simp] theorem reflect_point_involutive (x : R4Point) :
    reflectPoint (reflectPoint x) = x := by
  funext i
  by_cases h : i = 0
  · subst i
    simp [reflectPoint]
  · simp [reflectPoint, h]

/-- Fixed points are exactly the points with vanishing reflected coordinate. -/
theorem reflect_point_fixed_iff_first_coordinate_zero
    (x : R4Point) :
    reflectPoint x = x ↔ x 0 = 0 := by
  constructor
  · intro hFixed
    have hCoordinate := congrFun hFixed (0 : Fin 4)
    simp [reflectPoint] at hCoordinate
    linarith
  · intro hZero
    funext i
    by_cases h : i = 0
    · subst i
      simp [reflectPoint, hZero]
    · simp [reflectPoint, h]

/-- Squared Euclidean radius. -/
def radiusSquared (x : R4Point) : ℝ :=
  ∑ i, x i ^ 2

/-- Reflection preserves the squared Euclidean radius. -/
@[simp] theorem reflect_point_preserves_radius_squared
    (x : R4Point) :
    radiusSquared (reflectPoint x) = radiusSquared x := by
  unfold radiusSquared
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : i = 0
  · simp [reflectPoint, h]
  · simp [reflectPoint, h]

/-- Algebraic unit three-sphere. -/
def OnUnitThreeSphere (x : R4Point) : Prop :=
  radiusSquared x = 1

/-- Algebraic equatorial two-sphere in the reflected hyperplane. -/
def OnEquatorialTwoSphere (x : R4Point) : Prop :=
  OnUnitThreeSphere x /\ x 0 = 0

/-- The reflection restricts to the unit three-sphere. -/
theorem reflection_preserves_unit_three_sphere
    (x : R4Point)
    (hSphere : OnUnitThreeSphere x) :
    OnUnitThreeSphere (reflectPoint x) := by
  unfold OnUnitThreeSphere at hSphere ⊢
  simpa using hSphere

/-- The fixed set on the unit three-sphere is exactly the equatorial two-sphere. -/
theorem sphere_fixed_set_is_equatorial_two_sphere
    (x : R4Point) :
    (OnUnitThreeSphere x /\ reflectPoint x = x) ↔
      OnEquatorialTwoSphere x := by
  constructor
  · rintro ⟨hSphere, hFixed⟩
    exact ⟨hSphere,
      (reflect_point_fixed_iff_first_coordinate_zero x).mp hFixed⟩
  · rintro ⟨hSphere, hZero⟩
    exact ⟨hSphere,
      (reflect_point_fixed_iff_first_coordinate_zero x).mpr hZero⟩

/--
After taking the mapping torus, this fixed equator is expected to sweep out the
canonical throat `S2 x S1`.  Turning that statement into a homeomorphism or
diffeomorphism is the next topology-level construction target.
-/
structure MappingTorusFixedThroatStatus where
  reflectionActsOnS3 : Prop
  mappingTorusConstructed : Prop
  fixedSetMappingTorusConstructed : Prop
  fixedSetIdentifiedWithS2TimesS1 : Prop
  embeddingIntoFourManifoldDerived : Prop
  normalLineTwistComputed : Prop


def fixedThroatConstructionClosed
    (s : MappingTorusFixedThroatStatus) : Prop :=
  s.reflectionActsOnS3 /\
  s.mappingTorusConstructed /\
  s.fixedSetMappingTorusConstructed /\
  s.fixedSetIdentifiedWithS2TimesS1 /\
  s.embeddingIntoFourManifoldDerived /\
  s.normalLineTwistComputed

end P0EFTJanusReflectionFixedThroat
end JanusFormal
