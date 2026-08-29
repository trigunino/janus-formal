import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostTriple4D

/-!
# Finite ambient Lorentz isometry for the three spatial rotations

The explicit finite rotation flow is promoted to a continuous linear map on
`ℝ⁴`, transported to `EuclideanR4`, and extended trivially across ambient
time.  The resulting map preserves the ambient product Minkowski form.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSpatialRotationAmbientLorentzIsometry4D

set_option autoImplicit false

noncomputable section

open scoped BigOperators RealInnerProductSpace
open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusD8NonabelianGhostTriple4D

/-- The explicit finite spatial rotation, now as a linear map on raw
four-coordinate vectors. -/
def ambientR4FiniteSpatialRotationLinearMap
    (axis : Fin 3) (angle : Real) : R4Point →ₗ[Real] R4Point where
  toFun := fun point => ambientSpatialRotationFlow axis (angle, point)
  map_add' := by
    intro first second
    funext index
    fin_cases axis <;> fin_cases index <;>
      simp [ambientSpatialRotationFlow] <;> ring
  map_smul' := by
    intro scalar point
    funext index
    fin_cases axis <;> fin_cases index <;>
      simp [ambientSpatialRotationFlow] <;> ring

/-- Continuous version of the raw finite spatial rotation. -/
def ambientR4FiniteSpatialRotation
    (axis : Fin 3) (angle : Real) : R4Point →L[Real] R4Point :=
  (ambientR4FiniteSpatialRotationLinearMap axis angle).toContinuousLinearMap

@[simp]
theorem ambientR4FiniteSpatialRotation_apply
    (axis : Fin 3) (angle : Real) (point : R4Point) :
    ambientR4FiniteSpatialRotation axis angle point =
      ambientSpatialRotationFlow axis (angle, point) :=
  rfl

/-- The same finite rotation in Mathlib's Euclidean `ℝ⁴` model. -/
def euclideanR4FiniteSpatialRotation
    (axis : Fin 3) (angle : Real) : EuclideanR4 →L[Real] EuclideanR4 :=
  (EuclideanSpace.equiv (Fin 4) Real).symm.toContinuousLinearMap.comp
    ((ambientR4FiniteSpatialRotation axis angle).comp
      (EuclideanSpace.equiv (Fin 4) Real).toContinuousLinearMap)

@[simp]
theorem euclideanR4FiniteSpatialRotation_coordinates
    (axis : Fin 3) (angle : Real) (point : EuclideanR4) :
    EuclideanSpace.equiv (Fin 4) Real
        (euclideanR4FiniteSpatialRotation axis angle point) =
      ambientSpatialRotationFlow axis
        (angle, EuclideanSpace.equiv (Fin 4) Real point) := by
  change WithLp.ofLp (WithLp.toLp 2
      (ambientSpatialRotationFlow axis
        (angle, EuclideanSpace.equiv (Fin 4) Real point))) =
    ambientSpatialRotationFlow axis
      (angle, EuclideanSpace.equiv (Fin 4) Real point)
  exact WithLp.ofLp_toLp _ _

/-- Each finite spatial rotation preserves the Euclidean inner product on
the four spatial ambient coordinates. -/
theorem euclideanR4FiniteSpatialRotation_inner
    (axis : Fin 3) (angle : Real) (first second : EuclideanR4) :
    inner Real (euclideanR4FiniteSpatialRotation axis angle first)
        (euclideanR4FiniteSpatialRotation axis angle second) =
      inner Real first second := by
  simp only [PiLp.inner_apply, Real.inner_apply]
  have hFirst : ∀ index : Fin 4,
      (euclideanR4FiniteSpatialRotation axis angle first) index =
        ambientSpatialRotationFlow axis
          (angle, EuclideanSpace.equiv (Fin 4) Real first) index := by
    intro index
    exact congrFun
      (euclideanR4FiniteSpatialRotation_coordinates axis angle first) index
  have hSecond : ∀ index : Fin 4,
      (euclideanR4FiniteSpatialRotation axis angle second) index =
        ambientSpatialRotationFlow axis
          (angle, EuclideanSpace.equiv (Fin 4) Real second) index := by
    intro index
    exact congrFun
      (euclideanR4FiniteSpatialRotation_coordinates axis angle second) index
  simp_rw [hFirst, hSecond]
  change
    (∑ index : Fin 4,
      ambientSpatialRotationFlow axis
          (angle, EuclideanSpace.equiv (Fin 4) Real first) index *
        ambientSpatialRotationFlow axis
          (angle, EuclideanSpace.equiv (Fin 4) Real second) index) =
      ∑ index : Fin 4,
        EuclideanSpace.equiv (Fin 4) Real first index *
          EuclideanSpace.equiv (Fin 4) Real second index
  have hcos :
      Real.cos angle ^ 2 =
        1 - Real.sin angle ^ 2 := by
    nlinarith [Real.sin_sq_add_cos_sq angle]
  fin_cases axis <;>
    simp [ambientSpatialRotationFlow, Fin.sum_univ_succ] <;>
    ring_nf <;>
    rw [hcos] <;>
    ring

/-- The finite spatial rotation extended trivially across ambient time. -/
def ambientFiniteSpatialRotation
    (axis : Fin 3) (angle : Real) :
    (EuclideanR4 × Real) →L[Real] (EuclideanR4 × Real) :=
  (euclideanR4FiniteSpatialRotation axis angle).prodMap
    (ContinuousLinearMap.id Real Real)

@[simp]
theorem ambientFiniteSpatialRotation_apply
    (axis : Fin 3) (angle : Real) (point : EuclideanR4 × Real) :
    ambientFiniteSpatialRotation axis angle point =
      (euclideanR4FiniteSpatialRotation axis angle point.1, point.2) :=
  rfl

/-- Exact Lorentz-isometry identity for the ambient product Minkowski
pairing. -/
theorem ambientFiniteSpatialRotation_preserves_minkowski
    (axis : Fin 3) (angle : Real)
    (first second : EuclideanR4 × Real) :
    inner Real (ambientFiniteSpatialRotation axis angle first).1
          (ambientFiniteSpatialRotation axis angle second).1 -
        (ambientFiniteSpatialRotation axis angle first).2 *
          (ambientFiniteSpatialRotation axis angle second).2 =
      inner Real first.1 second.1 - first.2 * second.2 := by
  rw [ambientFiniteSpatialRotation_apply,
    ambientFiniteSpatialRotation_apply,
    euclideanR4FiniteSpatialRotation_inner]

end

end P0EFTJanusMappingTorusSpatialRotationAmbientLorentzIsometry4D
end JanusFormal
