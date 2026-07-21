import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusHolonomicCoordinateEquiv4D

/-!
# Normal-first holonomic coordinates for the canonical latitude collar
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeCollarHolonomicCoordinateEquiv4D

set_option autoImplicit false
noncomputable section

abbrev Vector4 := Fin 4 → Real
abbrev CollarModelCoordinates :=
  (EuclideanSpace Real (Fin 2) × Real) × Real

/-- Reorder four holonomic coefficients as
`((two sphere coordinates, time), normal)`. -/
def collarHolonomicCoordinateLinearEquiv :
    Vector4 ≃ₗ[Real] CollarModelCoordinates where
  toFun vector :=
    ((((EuclideanSpace.equiv (Fin 2) Real).symm
        (fun index : Fin 2 ↦ vector index.castSucc.succ)),
      vector (Fin.last 3)), vector 0)
  invFun parameter := fun index ↦
    Fin.cases parameter.2
      (fun tail : Fin 3 ↦
        Fin.lastCases parameter.1.2
          (fun sphereIndex : Fin 2 ↦
            EuclideanSpace.equiv (Fin 2) Real parameter.1.1 sphereIndex) tail)
      index
  left_inv := by
    intro vector
    funext index
    refine Fin.cases ?_ (fun tail : Fin 3 ↦ ?_) index
    · rfl
    · refine Fin.lastCases ?_ (fun sphereIndex : Fin 2 ↦ ?_) tail
      · rfl
      · simp
  right_inv := by
    rintro ⟨⟨sphere, time⟩, normal⟩
    apply Prod.ext
    · apply Prod.ext
      · apply (EuclideanSpace.equiv (Fin 2) Real).injective
        funext index
        simp
      · rfl
    · rfl
  map_add' := by
    intro first second
    apply Prod.ext
    · apply Prod.ext
      · apply (EuclideanSpace.equiv (Fin 2) Real).injective
        funext index
        rfl
      · rfl
    · rfl
  map_smul' := by
    intro scalar vector
    apply Prod.ext
    · apply Prod.ext
      · apply (EuclideanSpace.equiv (Fin 2) Real).injective
        funext index
        rfl
      · rfl
    · rfl

/-- Finite-dimensional continuity upgrade of the exact reordering. -/
def collarHolonomicCoordinateEquiv :
    Vector4 ≃L[Real] CollarModelCoordinates :=
  collarHolonomicCoordinateLinearEquiv.toContinuousLinearEquiv

@[simp] theorem collarHolonomicCoordinateEquiv_normal
    (vector : Vector4) :
    (collarHolonomicCoordinateEquiv vector).2 = vector 0 :=
  rfl

@[simp] theorem collarHolonomicCoordinateEquiv_time
    (vector : Vector4) :
    (collarHolonomicCoordinateEquiv vector).1.2 = vector (Fin.last 3) :=
  rfl

@[simp] theorem collarHolonomicCoordinateEquiv_sphere
    (vector : Vector4) (index : Fin 2) :
    (collarHolonomicCoordinateEquiv vector).1.1 index =
      vector index.castSucc.succ :=
  by simp [collarHolonomicCoordinateEquiv,
    collarHolonomicCoordinateLinearEquiv]

end
end P0EFTJanusMappingTorusCanonicalLatitudeCollarHolonomicCoordinateEquiv4D
end JanusFormal
