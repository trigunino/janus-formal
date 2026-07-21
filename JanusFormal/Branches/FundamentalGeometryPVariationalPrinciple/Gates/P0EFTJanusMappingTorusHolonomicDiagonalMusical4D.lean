import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusHolonomicDiagonalSharp4D

/-!
# Continuous diagonal musical map in holonomic model coordinates

The exact diagonal pairing is promoted to a continuous linear equivalence
between the model tangent space and its continuous dual.  This remains
model-space data and does not assert a global smooth tangent frame.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusHolonomicDiagonalMusical4D

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1ContinuousFrameControl4D
open P0EFTJanusMappingTorusHolonomicCoordinateEquiv4D
open P0EFTJanusMappingTorusHolonomicDiagonalSharp4D

private theorem coefficient_add
    (first second : CoverCoordinates) (index : Fin 4) :
    holonomicVectorCoefficient (first + second) index =
      holonomicVectorCoefficient first index +
        holonomicVectorCoefficient second index := by
  have h := congrFun
    (holonomicCoefficientLinearMap.map_add first second) index
  exact h

private theorem coefficient_smul
    (scalar : Real) (vector : CoverCoordinates) (index : Fin 4) :
    holonomicVectorCoefficient (scalar • vector) index =
      scalar * holonomicVectorCoefficient vector index := by
  have h := congrFun
    (holonomicCoefficientLinearMap.map_smul scalar vector) index
  exact h

private theorem pair_add_right
    (magnitude : HolonomicCoefficients)
    (first second third : CoverCoordinates) :
    holonomicDiagonalPair magnitude first (second + third) =
      holonomicDiagonalPair magnitude first second +
        holonomicDiagonalPair magnitude first third := by
  unfold holonomicDiagonalPair
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  rw [coefficient_add]
  ring

private theorem pair_smul_right
    (magnitude : HolonomicCoefficients)
    (first second : CoverCoordinates) (scalar : Real) :
    holonomicDiagonalPair magnitude first (scalar • second) =
      scalar * holonomicDiagonalPair magnitude first second := by
  unfold holonomicDiagonalPair
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [coefficient_smul]
  ring

private theorem pair_add_left
    (magnitude : HolonomicCoefficients)
    (first second third : CoverCoordinates) :
    holonomicDiagonalPair magnitude (first + second) third =
      holonomicDiagonalPair magnitude first third +
        holonomicDiagonalPair magnitude second third := by
  unfold holonomicDiagonalPair
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro index _
  rw [coefficient_add]
  ring

private theorem pair_smul_left
    (magnitude : HolonomicCoefficients)
    (first second : CoverCoordinates) (scalar : Real) :
    holonomicDiagonalPair magnitude (scalar • first) second =
      scalar * holonomicDiagonalPair magnitude first second := by
  unfold holonomicDiagonalPair
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [coefficient_smul]
  ring

/-- The diagonal pairing with its first argument fixed, as a continuous
model covector. -/
def holonomicDiagonalCovector
    (magnitude : HolonomicCoefficients) (first : CoverCoordinates) :
    CoverCoordinates →L[Real] Real :=
  ({ toFun := fun second => holonomicDiagonalPair magnitude first second
     map_add' := pair_add_right magnitude first
     map_smul' := by
       intro scalar second
       exact pair_smul_right magnitude first second scalar } :
      CoverCoordinates →ₗ[Real] Real).toContinuousLinearMap

@[simp]
theorem holonomicDiagonalCovector_apply
    (magnitude : HolonomicCoefficients) (first second : CoverCoordinates) :
    holonomicDiagonalCovector magnitude first second =
      holonomicDiagonalPair magnitude first second :=
  rfl

/-- The covariant diagonal flat map as a continuous linear operator. -/
def holonomicDiagonalFlat
    (magnitude : HolonomicCoefficients) :
    CoverCoordinates →L[Real] (CoverCoordinates →L[Real] Real) :=
  ({ toFun := holonomicDiagonalCovector magnitude
     map_add' := by
       intro first second
       apply ContinuousLinearMap.ext
       intro third
       exact pair_add_left magnitude first second third
     map_smul' := by
       intro scalar first
       apply ContinuousLinearMap.ext
       intro second
       exact pair_smul_left magnitude first second scalar } :
      CoverCoordinates →ₗ[Real] (CoverCoordinates →L[Real] Real)
    ).toContinuousLinearMap

@[simp]
theorem holonomicDiagonalFlat_apply
    (magnitude : HolonomicCoefficients) (first second : CoverCoordinates) :
    holonomicDiagonalFlat magnitude first second =
      holonomicDiagonalPair magnitude first second :=
  rfl

private theorem signature_ne_zero (index : Fin 4) : signature index ≠ 0 := by
  fin_cases index <;> norm_num [signature]

private theorem pair_tangentCoordinate
    (magnitude : HolonomicCoefficients)
    (vector : CoverCoordinates) (index : Fin 4) :
    holonomicDiagonalPair magnitude vector (tangentCoordinate index) =
      signature index * magnitude index *
        holonomicVectorCoefficient vector index := by
  unfold holonomicDiagonalPair
  simp [holonomicVectorCoefficient_tangentCoordinate]

theorem holonomicDiagonalFlat_bijective
    (magnitude : HolonomicCoefficients)
    (hMagnitude : ∀ index, magnitude index ≠ 0) :
    Function.Bijective (holonomicDiagonalFlat magnitude) := by
  constructor
  · intro first second hEqual
    apply holonomicCoordinateEquiv.injective
    funext index
    have hEvaluation := congrArg
      (fun covector : CoverCoordinates →L[Real] Real =>
        covector (tangentCoordinate index)) hEqual
    simp only [holonomicDiagonalFlat_apply, pair_tangentCoordinate] at hEvaluation
    exact mul_left_cancel₀
      (mul_ne_zero (signature_ne_zero index) (hMagnitude index)) hEvaluation
  · intro covector
    refine ⟨holonomicDiagonalSharp magnitude (fun vector => covector vector), ?_⟩
    apply ContinuousLinearMap.ext
    intro vector
    exact holonomicDiagonalPair_sharp magnitude hMagnitude covector vector

/-- Continuous musical equivalence of the nondegenerate diagonal model
pairing in the exact holonomic coordinates. -/
def holonomicDiagonalMusical
    (magnitude : HolonomicCoefficients)
    (hMagnitude : ∀ index, magnitude index ≠ 0) :
    CoverCoordinates ≃L[Real] (CoverCoordinates →L[Real] Real) :=
  (LinearEquiv.ofBijective (holonomicDiagonalFlat magnitude).toLinearMap
    (holonomicDiagonalFlat_bijective magnitude hMagnitude)).toContinuousLinearEquiv

@[simp]
theorem holonomicDiagonalMusical_apply
    (magnitude : HolonomicCoefficients)
    (hMagnitude : ∀ index, magnitude index ≠ 0)
    (first second : CoverCoordinates) :
    holonomicDiagonalMusical magnitude hMagnitude first second =
      holonomicDiagonalPair magnitude first second :=
  rfl

end

end P0EFTJanusMappingTorusHolonomicDiagonalMusical4D
end JanusFormal
