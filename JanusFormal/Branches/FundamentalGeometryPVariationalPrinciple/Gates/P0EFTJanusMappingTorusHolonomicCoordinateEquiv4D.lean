import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1ContinuousFrameControl4D

/-!
# Continuous holonomic coordinate equivalence

This gate upgrades the explicit time-first decomposition used by the global
scalar action to a continuous linear equivalence of the four-dimensional
model tangent space.  It is algebraic model-space data; no global smooth
tangent frame on the mapping torus is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusHolonomicCoordinateEquiv4D

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1ContinuousFrameControl4D

/-- Time-first coefficient space of the fixed holonomic model basis. -/
abbrev HolonomicCoefficients := Fin 4 → Real

/-- Extraction of the four fixed holonomic coefficients as a linear map. -/
def holonomicCoefficientLinearMap :
    CoverCoordinates →ₗ[Real] HolonomicCoefficients where
  toFun := fun vector index => holonomicVectorCoefficient vector index
  map_add' := by
    intro first second
    funext index
    fin_cases index <;> rfl
  map_smul' := by
    intro scalar vector
    funext index
    fin_cases index <;> rfl

@[simp]
theorem holonomicCoefficientLinearMap_apply
    (vector : CoverCoordinates) (index : Fin 4) :
    holonomicCoefficientLinearMap vector index =
      holonomicVectorCoefficient vector index :=
  rfl

@[simp]
theorem holonomicVectorCoefficient_tangentCoordinate
    (basisIndex coefficientIndex : Fin 4) :
    holonomicVectorCoefficient (tangentCoordinate basisIndex) coefficientIndex =
      if basisIndex = coefficientIndex then 1 else 0 := by
  refine Fin.cases ?_ (fun spatial => ?_) coefficientIndex
  · rw [holonomicVectorCoefficient_zero]
    fin_cases basisIndex <;> norm_num [tangentCoordinate]
  · rw [holonomicVectorCoefficient_succ]
    fin_cases basisIndex <;> fin_cases spatial <;>
      norm_num [tangentCoordinate] <;>
      simp only [Fin.ext_iff] <;> norm_num

/-- Reconstruction from time-first holonomic coefficients. -/
def holonomicReconstructionLinearMap :
    HolonomicCoefficients →ₗ[Real] CoverCoordinates where
  toFun := fun coefficients =>
    ∑ index : Fin 4, coefficients index • tangentCoordinate index
  map_add' := by
    intro first second
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' := by
    intro scalar coefficients
    simp [Finset.smul_sum, smul_smul]

/-- The fixed holonomic vectors and their explicit coefficients are inverse
linear coordinate systems. -/
def holonomicCoordinateLinearEquiv :
    CoverCoordinates ≃ₗ[Real] HolonomicCoefficients where
  toLinearMap := holonomicCoefficientLinearMap
  invFun := holonomicReconstructionLinearMap
  left_inv := holonomic_vector_decomposition
  right_inv := by
    intro coefficients
    funext coefficientIndex
    change holonomicCoefficientLinearMap
      (∑ basisIndex : Fin 4,
        coefficients basisIndex • tangentCoordinate basisIndex)
      coefficientIndex = coefficients coefficientIndex
    rw [map_sum]
    simp [holonomicVectorCoefficient_tangentCoordinate]

/-- Finite-dimensional continuity upgrade of the exact holonomic coordinate
equivalence. -/
def holonomicCoordinateEquiv :
    CoverCoordinates ≃L[Real] HolonomicCoefficients :=
  holonomicCoordinateLinearEquiv.toContinuousLinearEquiv

@[simp]
theorem holonomicCoordinateEquiv_apply
    (vector : CoverCoordinates) (index : Fin 4) :
    holonomicCoordinateEquiv vector index =
      holonomicVectorCoefficient vector index :=
  rfl

@[simp]
theorem holonomicCoordinateEquiv_symm_apply
    (coefficients : HolonomicCoefficients) :
    holonomicCoordinateEquiv.symm coefficients =
      ∑ index : Fin 4, coefficients index • tangentCoordinate index :=
  rfl

end

end P0EFTJanusMappingTorusHolonomicCoordinateEquiv4D
end JanusFormal
