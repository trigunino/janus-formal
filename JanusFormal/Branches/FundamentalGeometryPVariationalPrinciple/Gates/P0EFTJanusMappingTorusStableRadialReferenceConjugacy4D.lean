import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusProjection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D

/-!
# Fixed reference conjugacy for the stable radial frame

The canonical coordinate split sends the reflected zeroth ambient coordinate
to the real factor of `CoverCoordinates`.  It therefore conjugates the
geometric ambient reflection to the fixed Pin-minus reference reflection.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusStableRadialReferenceConjugacy4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D

private abbrev AmbientReflection :=
  P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D.euclideanReflection

/-- The fixed linear coordinate split
`(x₀,x₁,x₂,x₃) ↦ ((x₁,x₂,x₃),x₀)`. -/
def stableRadialReferenceLinearEquiv :
    EuclideanR4 ≃ₗ[Real] CoverCoordinates where
  toFun point :=
    ((EuclideanSpace.equiv (Fin 3) Real).symm
      (fun index => point index.succ), point 0)
  invFun coordinates :=
    (EuclideanSpace.equiv (Fin 4) Real).symm
      (fun index => Fin.cases coordinates.2
        (fun tail => coordinates.1 tail) index)
  left_inv point := by
    apply (EuclideanSpace.equiv (Fin 4) Real).injective
    funext index
    refine Fin.cases ?_ (fun tail => ?_) index <;> simp
  right_inv coordinates := by
    apply Prod.ext
    · apply (EuclideanSpace.equiv (Fin 3) Real).injective
      funext index
      simp
    · simp
  map_add' first second := by
    apply Prod.ext
    · apply (EuclideanSpace.equiv (Fin 3) Real).injective
      funext index
      simp
    · simp
  map_smul' scalar point := by
    apply Prod.ext
    · apply (EuclideanSpace.equiv (Fin 3) Real).injective
      funext index
      simp
    · simp

/-- The fixed split as a continuous linear equivalence. -/
def stableRadialReferenceEquiv :
    EuclideanR4 ≃L[Real] CoverCoordinates :=
  stableRadialReferenceLinearEquiv.toContinuousLinearEquiv

@[simp] theorem stableRadialReferenceEquiv_apply_fst
    (point : EuclideanR4) (index : Fin 3) :
    (stableRadialReferenceEquiv point).1 index = point index.succ := by
  rfl

@[simp] theorem stableRadialReferenceEquiv_apply_snd
    (point : EuclideanR4) :
    (stableRadialReferenceEquiv point).2 = point 0 := by
  rfl

@[simp] theorem stableRadialReferenceEquiv_symm_apply_zero
    (coordinates : CoverCoordinates) :
    (stableRadialReferenceEquiv.symm coordinates) 0 = coordinates.2 := by
  rfl

@[simp] theorem stableRadialReferenceEquiv_symm_apply_succ
    (coordinates : CoverCoordinates) (index : Fin 3) :
    (stableRadialReferenceEquiv.symm coordinates) index.succ =
      coordinates.1 index := by
  rfl

/-- The fixed ambient basis vector spanning the reflected axis. -/
def ambientReflectedReferenceVector : EuclideanR4 :=
  EuclideanSpace.single 0 1

@[simp] theorem stableRadialReferenceEquiv_referenceVector :
    stableRadialReferenceEquiv ambientReflectedReferenceVector =
      ambientPinMinusReferenceVector := by
  apply Prod.ext
  · ext index
    simp [ambientReflectedReferenceVector, ambientPinMinusReferenceVector]
  · simp [ambientReflectedReferenceVector, ambientPinMinusReferenceVector]

/-- Pointwise conjugacy of the actual ambient reflection with the fixed
Pin-minus reference reflection. -/
theorem stableRadialReferenceEquiv_euclideanReflection
    (point : EuclideanR4) :
    stableRadialReferenceEquiv (AmbientReflection point) =
      ambientPinMinusReferenceReflection
        (stableRadialReferenceEquiv point) := by
  rw [ambientPinMinusReferenceReflection_apply]
  apply Prod.ext
  · ext index
    simp [AmbientReflection,
      P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D.euclideanReflection_apply]
  · simp [AmbientReflection,
      P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D.euclideanReflection_apply]

/-- Exact equality of linear equivalences expressing the conjugation
`E ∘ R ∘ E⁻¹ = R_ref`. -/
theorem stableRadialReferenceEquiv_conjugation :
    stableRadialReferenceEquiv.toLinearEquiv.symm.trans
        (AmbientReflection.toLinearEquiv.trans
          stableRadialReferenceEquiv.toLinearEquiv) =
      ambientPinMinusReferenceReflection := by
  apply LinearEquiv.ext
  intro coordinates
  change stableRadialReferenceEquiv
      (AmbientReflection (stableRadialReferenceEquiv.symm coordinates)) =
    ambientPinMinusReferenceReflection coordinates
  rw [stableRadialReferenceEquiv_euclideanReflection,
    stableRadialReferenceEquiv.apply_symm_apply]

end

end P0EFTJanusMappingTorusStableRadialReferenceConjugacy4D
end JanusFormal
