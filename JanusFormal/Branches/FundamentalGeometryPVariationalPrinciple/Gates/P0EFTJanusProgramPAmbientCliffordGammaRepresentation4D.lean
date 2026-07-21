import Mathlib.LinearAlgebra.CliffordAlgebra.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPAmbientPinCDeterminantLineBundle4D

/-! # Complex gamma representation of the ambient negative Clifford algebra

Four explicit complex `4 × 4` gamma matrices square to `-1` and anticommute.
Their linear combination satisfies the negative Euclidean Clifford relation,
hence extends by the universal property to an algebra representation of the
ambient Clifford algebra.  Descent of the induced Pin action to `PinC(4)` is
the next card.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPAmbientCliffordGammaRepresentation4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D

abbrev AmbientDiracSpinor4 := Fin 4 → Complex
abbrev AmbientComplexMatrix4 := Matrix (Fin 4) (Fin 4) Complex

/-- Explicit generators for the negative Euclidean complex Clifford action. -/
def ambientGammaBasis : Fin 4 → AmbientComplexMatrix4 :=
  ![
    !![0, 0, Complex.I, 0;
       0, 0, 0, Complex.I;
       Complex.I, 0, 0, 0;
       0, Complex.I, 0, 0],
    !![0, 0, 1, 0;
       0, 0, 0, 1;
       -1, 0, 0, 0;
       0, -1, 0, 0],
    !![0, Complex.I, 0, 0;
       Complex.I, 0, 0, 0;
       0, 0, 0, -Complex.I;
       0, 0, -Complex.I, 0],
    !![0, 1, 0, 0;
       -1, 0, 0, 0;
       0, 0, 0, -1;
       0, 0, 1, 0]
  ]

@[simp] theorem ambientGammaBasis_sq (index : Fin 4) :
    ambientGammaBasis index * ambientGammaBasis index =
      -(1 : AmbientComplexMatrix4) := by
  fin_cases index <;>
    ext row column <;>
    fin_cases row <;> fin_cases column <;>
    simp [ambientGammaBasis, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.I_mul_I]

/-- Gamma contraction with an ambient cover vector. -/
def ambientGammaMatrix (vector : CoverCoordinates) : AmbientComplexMatrix4 :=
  (vector.1 0 : Complex) • ambientGammaBasis 0 +
  (vector.1 1 : Complex) • ambientGammaBasis 1 +
  (vector.1 2 : Complex) • ambientGammaBasis 2 +
  (vector.2 : Complex) • ambientGammaBasis 3

def ambientGammaMatrixLinear :
    CoverCoordinates →ₗ[Real] AmbientComplexMatrix4 where
  toFun := ambientGammaMatrix
  map_add' first second := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [ambientGammaMatrix]
    all_goals ring
  map_smul' scalar vector := by
    ext row column
    fin_cases row <;> fin_cases column <;>
      simp [ambientGammaMatrix]
    all_goals ring

/-- The explicit matrices satisfy the full negative Euclidean Clifford
quadratic relation, not merely the four basis relations. -/
theorem ambientGammaMatrix_sq (vector : CoverCoordinates) :
    ambientGammaMatrix vector * ambientGammaMatrix vector =
      algebraMap Real AmbientComplexMatrix4
        (ambientCoverPinMinusQuadraticForm vector) := by
  have hQuadratic : ambientCoverPinMinusQuadraticForm vector =
      -((vector.1 0) ^ 2 + (vector.1 1) ^ 2 + (vector.1 2) ^ 2 +
        vector.2 ^ 2) := by
    rw [ambientCoverPinMinusQuadraticForm_apply,
      EuclideanSpace.real_norm_sq_eq]
    simp [Fin.sum_univ_succ]
    ring
  rw [hQuadratic]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [ambientGammaMatrix, ambientGammaBasis, Matrix.mul_apply,
      Fin.sum_univ_succ, Matrix.algebraMap_matrix_apply]
  all_goals apply Complex.ext <;> simp [← Complex.ofReal_pow] <;> ring

/-- Algebra representation selected by the explicit gamma matrices. -/
def ambientCliffordGammaRepresentation :
    AmbientPinMinusCliffordAlgebra →ₐ[Real] AmbientComplexMatrix4 :=
  CliffordAlgebra.lift ambientCoverPinMinusQuadraticForm
    ⟨ambientGammaMatrixLinear, ambientGammaMatrix_sq⟩

theorem continuous_ambientCliffordGammaRepresentation :
    Continuous ambientCliffordGammaRepresentation :=
  LinearMap.continuous_of_finiteDimensional
    ambientCliffordGammaRepresentation.toLinearMap

@[simp] theorem ambientCliffordGammaRepresentation_iota
    (vector : CoverCoordinates) :
    ambientCliffordGammaRepresentation
        (CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm vector) =
      ambientGammaMatrix vector := by
  exact CliffordAlgebra.lift_ι_apply _ _ vector

structure ProgramPAmbientCliffordGammaRepresentationCertificate4D where
  spinor : Type
  spinor_eq : spinor = AmbientDiracSpinor4
  gamma : CoverCoordinates →ₗ[Real] AmbientComplexMatrix4
  gammaCanonical : gamma = ambientGammaMatrixLinear
  cliffordRelation : ∀ vector,
    gamma vector * gamma vector =
      algebraMap Real AmbientComplexMatrix4
        (ambientCoverPinMinusQuadraticForm vector)
  representation :
    AmbientPinMinusCliffordAlgebra →ₐ[Real] AmbientComplexMatrix4
  representationCanonical :
    representation = ambientCliffordGammaRepresentation

def programPAmbientCliffordGammaRepresentationCertificate4D :
    ProgramPAmbientCliffordGammaRepresentationCertificate4D where
  spinor := AmbientDiracSpinor4
  spinor_eq := rfl
  gamma := ambientGammaMatrixLinear
  gammaCanonical := rfl
  cliffordRelation := ambientGammaMatrix_sq
  representation := ambientCliffordGammaRepresentation
  representationCanonical := rfl

theorem programPAmbientCliffordGammaRepresentationCertificate4D_nonempty :
    Nonempty ProgramPAmbientCliffordGammaRepresentationCertificate4D :=
  ⟨programPAmbientCliffordGammaRepresentationCertificate4D⟩

end
end P0EFTJanusProgramPAmbientCliffordGammaRepresentation4D
end JanusFormal
