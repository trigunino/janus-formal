import Mathlib.LinearAlgebra.Determinant
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D

namespace JanusFormal
namespace P0EFTJanusProgramPT12ReflectionFrameDeterminant4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusReflectionFixedThroat
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusDeckInvariantLorentzCocycle4D

/-- Ambient coordinates of four vectors, placed in the matrix columns. -/
def frameColumnMatrix (columns : Fin 4 → EuclideanR4) : Matrix (Fin 4) (Fin 4) Real :=
  fun row column => columns column row

/-- Reflection of the ambient first coordinate reverses the frame determinant. -/
theorem frameColumnMatrix_reflection_det (columns : Fin 4 → EuclideanR4) :
    (frameColumnMatrix (fun index => euclideanReflection (columns index))).det =
      -(frameColumnMatrix columns).det := by
  have hMatrix :
      frameColumnMatrix (fun index => euclideanReflection (columns index)) =
        Matrix.of (fun row column =>
          (if row = 0 then (-1 : Real) else 1) * frameColumnMatrix columns row column) := by
    ext row column
    by_cases hRow : row = 0 <;> simp [frameColumnMatrix, hRow]
  rw [hMatrix, Matrix.det_mul_column]
  simp

/-- A continuous linear equivalence sends the standard basis to a nonzero
frame determinant in ambient Euclidean coordinates. -/
theorem frameColumnMatrix_equiv_det_ne_zero
    (equiv : (Fin 4 → Real) ≃L[Real] EuclideanR4) :
    (frameColumnMatrix (fun index => equiv ((Pi.basisFun Real (Fin 4)) index))).det ≠ 0 := by
  let rawEquiv : (Fin 4 → Real) ≃L[Real] (Fin 4 → Real) :=
    equiv.trans (PiLp.continuousLinearEquiv 2 Real (fun _ : Fin 4 => Real))
  have hMatrix :
      frameColumnMatrix (fun index => equiv ((Pi.basisFun Real (Fin 4)) index)) =
        LinearMap.toMatrix (Pi.basisFun Real (Fin 4)) (Pi.basisFun Real (Fin 4))
          rawEquiv.toLinearEquiv.toLinearMap := by
    ext row column
    rw [LinearMap.toMatrix_apply, Pi.basisFun_repr]
    rfl
  rw [hMatrix]
  exact (rawEquiv.toLinearEquiv.isUnit_det
    (Pi.basisFun Real (Fin 4)) (Pi.basisFun Real (Fin 4))).ne_zero

end
end P0EFTJanusProgramPT12ReflectionFrameDeterminant4D
end JanusFormal
