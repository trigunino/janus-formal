import Mathlib
import JanusFormal.Branches.FundamentalGeometryD.Gates.P0EFTJanusReflectionFixedThroat

namespace JanusFormal
namespace P0EFTJanusEquatorialNormalReflection

set_option autoImplicit false

open P0EFTJanusReflectionFixedThroat

/-- Euclidean dot product in the coordinate model. -/
def dotProduct (first second : R4Point) : ℝ :=
  ∑ index, first index * second index

/-- Unit vector in the reflected coordinate direction. -/
def equatorialNormal : R4Point :=
  fun index => if index = 0 then 1 else 0

@[simp] theorem equatorial_normal_first_coordinate :
    equatorialNormal 0 = 1 := by
  simp [equatorialNormal]

/-- Dotting with the normal extracts the reflected coordinate. -/
theorem equatorial_normal_dot
    (vector : R4Point) :
    dotProduct equatorialNormal vector = vector 0 := by
  unfold dotProduct equatorialNormal
  simp only [Fin.sum_univ_four]
  norm_num

/-- The coordinate reflection sends the normal generator to its negative. -/
theorem reflection_reverses_equatorial_normal :
    reflectPoint equatorialNormal = -equatorialNormal := by
  funext index
  fin_cases index <;> simp [reflectPoint, equatorialNormal]

/-- Algebraic tangent condition for the unit sphere. -/
def IsSphereTangentAt
    (point tangent : R4Point) : Prop :=
  dotProduct point tangent = 0

/-- Algebraic tangent condition for the equatorial sphere. -/
def IsEquatorTangentAt
    (point tangent : R4Point) : Prop :=
  IsSphereTangentAt point tangent /\ tangent 0 = 0

/-- At an equatorial point, the reflected coordinate direction lies in the tangent space of `S3`. -/
theorem equatorial_normal_is_sphere_tangent
    (point : R4Point)
    (hEquator : OnEquatorialTwoSphere point) :
    IsSphereTangentAt point equatorialNormal := by
  unfold IsSphereTangentAt dotProduct equatorialNormal
  rcases hEquator with ⟨_hSphere, hFirst⟩
  simp only [Fin.sum_univ_four]
  norm_num [hFirst]

/-- The normal generator is orthogonal to every equatorial tangent vector. -/
theorem equatorial_normal_orthogonal_to_equator
    (point tangent : R4Point)
    (_hPoint : OnEquatorialTwoSphere point)
    (hTangent : IsEquatorTangentAt point tangent) :
    dotProduct equatorialNormal tangent = 0 := by
  rw [equatorial_normal_dot]
  exact hTangent.2

/-- The normal line is nonzero. -/
theorem equatorial_normal_nonzero :
    equatorialNormal ≠ 0 := by
  intro hZero
  have hFirst := congrFun hZero (0 : Fin 4)
  norm_num [equatorialNormal] at hFirst

/-- Scalar multiples give the algebraic normal line. -/
def OnEquatorialNormalLine (vector : R4Point) : Prop :=
  ∃ coefficient : ℝ, vector = coefficient • equatorialNormal

/-- Reflection acts as multiplication by `-1` on the whole normal line. -/
theorem reflection_is_minus_identity_on_normal_line
    (vector : R4Point)
    (hNormal : OnEquatorialNormalLine vector) :
    reflectPoint vector = -vector := by
  rcases hNormal with ⟨coefficient, rfl⟩
  funext index
  fin_cases index <;> simp [reflectPoint, equatorialNormal]

/--
This computes the clutching transition used by the normal-line quotient: the
reflection fixes the equator pointwise and acts by `-1` on its one-dimensional
normal inside `S3`.
-/
structure EquatorialNormalGeometricStatus where
  sphereTangentSpacesConstructed : Prop
  equatorTangentSpacesConstructed : Prop
  normalLineSubbundleConstructed : Prop
  coordinateNormalSpansNormalLine : Prop
  derivativeOfReflectionComputed : Prop
  derivativeActsMinusIdentity : Prop
  mappingTorusClutchingIdentified : Prop


def equatorialNormalGeometricClosure
    (s : EquatorialNormalGeometricStatus) : Prop :=
  s.sphereTangentSpacesConstructed /\
  s.equatorTangentSpacesConstructed /\
  s.normalLineSubbundleConstructed /\
  s.coordinateNormalSpansNormalLine /\
  s.derivativeOfReflectionComputed /\
  s.derivativeActsMinusIdentity /\
  s.mappingTorusClutchingIdentified

end P0EFTJanusEquatorialNormalReflection
end JanusFormal
