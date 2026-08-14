import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
import Mathlib.Topology.Instances.Matrix
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteFamilyGramBasis4D

/-!
# Local persistence of a finite Gram family

For a continuous finite family of vectors `v_i(a)` in one fixed real inner-product
space, the scalar Gram endomorphism is represented by the matrix

`G(a)_{ij} = <v_j(a), v_i(a)>`.

Its determinant is continuous in the parameter.  If the Gram endomorphism is
injective at one basepoint, the determinant is nonzero there and therefore
remains nonzero on a neighbourhood of that basepoint.  Hence Gram injectivity
persists locally.

This is the finite-dimensional stability mechanism needed for the projected
Candidate-A physical zero modes.  It introduces no global nondegeneracy
premise: only continuity of the already selected vectors and one proved
basepoint injectivity are used.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteFamilyGramLocalPersistence4D

set_option autoImplicit false
noncomputable section

open Filter Topology
open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiniteFamilyGramBasis4D

variable {Parameter Index E : Type*}
  [TopologicalSpace Parameter]
  [Fintype Index] [DecidableEq Index]
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Matrix representing the finite Gram endomorphism.  The row/column order is
chosen so that ordinary matrix-vector multiplication agrees directly with
`finiteFamilyGramMap`. -/
def finiteFamilyGramMatrix (vectors : Index → E) : Matrix Index Index Real :=
  fun row column => inner Real (vectors column) (vectors row)

@[simp]
theorem finiteFamilyGramMatrix_apply
    (vectors : Index → E) (row column : Index) :
    finiteFamilyGramMatrix vectors row column =
      inner Real (vectors column) (vectors row) :=
  rfl

/-- The scalar Gram linear map is ordinary multiplication by its finite Gram
matrix. -/
theorem finiteFamilyGramMatrix_mulVec
    (vectors : Index → E) (coefficient : Index → Real) :
    finiteFamilyGramMatrix vectors *ᵥ coefficient =
      finiteFamilyGramMap vectors coefficient := by
  ext row
  simp [finiteFamilyGramMatrix, Matrix.mulVec, dotProduct,
    finiteFamilyGramMap_apply, finiteFamilySynthesis, sum_inner,
    inner_smul_left, mul_comm]

/-- Finite Gram injectivity is exactly nonvanishing of the scalar Gram
determinant. -/
theorem finiteFamilyGramMap_injective_iff_det_ne_zero
    (vectors : Index → E) :
    Function.Injective (finiteFamilyGramMap vectors) ↔
      (finiteFamilyGramMatrix vectors).det ≠ 0 := by
  constructor
  · intro hInjective hDetZero
    obtain ⟨coefficient, hCoefficient, hKernel⟩ :=
      Matrix.exists_mulVec_eq_zero_iff.mpr hDetZero
    apply hCoefficient
    apply hInjective
    rw [← finiteFamilyGramMatrix_mulVec,
      ← finiteFamilyGramMatrix_mulVec]
    simpa using hKernel
  · intro hDet first second hEqual
    by_contra hFirstSecond
    have hDifference : first - second ≠ 0 :=
      sub_ne_zero.mpr hFirstSecond
    have hGramDifference :
        finiteFamilyGramMap vectors (first - second) = 0 := by
      rw [map_sub, hEqual, sub_self]
    have hMatrixDifference :
        finiteFamilyGramMatrix vectors *ᵥ (first - second) = 0 := by
      rw [finiteFamilyGramMatrix_mulVec]
      exact hGramDifference
    exact hDet <| Matrix.exists_mulVec_eq_zero_iff.mp
      ⟨first - second, hDifference, hMatrixDifference⟩

/-- Entrywise continuity of a finite vector family gives continuity of its Gram
matrix in the finite matrix topology. -/
theorem continuous_finiteFamilyGramMatrix
    (vectors : Parameter → Index → E)
    (hVectors : ∀ index,
      Continuous (fun parameter => vectors parameter index)) :
    Continuous (fun parameter => finiteFamilyGramMatrix (vectors parameter)) := by
  apply continuous_matrix
  intro row column
  simpa [finiteFamilyGramMatrix] using
    (hVectors column).inner (hVectors row)

/-- The finite Gram determinant is continuous in the parameter. -/
theorem continuous_finiteFamilyGramDeterminant
    (vectors : Parameter → Index → E)
    (hVectors : ∀ index,
      Continuous (fun parameter => vectors parameter index)) :
    Continuous
      (fun parameter => (finiteFamilyGramMatrix (vectors parameter)).det) :=
  (continuous_finiteFamilyGramMatrix vectors hVectors).matrix_det

/-- Injectivity of a continuous finite Gram family persists in a neighbourhood
of every basepoint where it has already been proved. -/
theorem eventually_finiteFamilyGramMap_injective
    (vectors : Parameter → Index → E)
    (hVectors : ∀ index,
      Continuous (fun parameter => vectors parameter index))
    (basepoint : Parameter)
    (hBasepoint :
      Function.Injective (finiteFamilyGramMap (vectors basepoint))) :
    ∀ᶠ parameter in 𝓝 basepoint,
      Function.Injective (finiteFamilyGramMap (vectors parameter)) := by
  have hDetBasepoint :
      (finiteFamilyGramMatrix (vectors basepoint)).det ≠ 0 :=
    (finiteFamilyGramMap_injective_iff_det_ne_zero
      (vectors basepoint)).mp hBasepoint
  have hDetEventually :
      ∀ᶠ parameter in 𝓝 basepoint,
        (finiteFamilyGramMatrix (vectors parameter)).det ≠ 0 :=
    (continuous_finiteFamilyGramDeterminant vectors hVectors).continuousAt.
      eventually_ne hDetBasepoint
  filter_upwards [hDetEventually] with parameter hDet
  exact (finiteFamilyGramMap_injective_iff_det_ne_zero
    (vectors parameter)).mpr hDet

/-- Public finite-dimensional local-persistence checkpoint. -/
theorem finite_family_gram_local_persistence_gate
    (vectors : Parameter → Index → E)
    (hVectors : ∀ index,
      Continuous (fun parameter => vectors parameter index))
    (basepoint : Parameter)
    (hBasepoint :
      Function.Injective (finiteFamilyGramMap (vectors basepoint))) :
    Continuous
        (fun parameter => (finiteFamilyGramMatrix (vectors parameter)).det) ∧
      ∀ᶠ parameter in 𝓝 basepoint,
        Function.Injective (finiteFamilyGramMap (vectors parameter)) :=
  ⟨continuous_finiteFamilyGramDeterminant vectors hVectors,
    eventually_finiteFamilyGramMap_injective vectors hVectors basepoint
      hBasepoint⟩

end
end P0EFTJanusProgramPFiniteFamilyGramLocalPersistence4D
end JanusFormal
