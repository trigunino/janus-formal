import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalDiagonalLorentzRoot4D

/-!
# Positive-spectrum diagonalizable relative roots in dimension four

This gate extends the explicit diagonal construction to every real matrix
equipped with a genuine real diagonalization whose four eigenvalues are
strictly positive.  The selected similarity root squares exactly to the
target.  Independence of the chosen eigenbasis, Jordan blocks and global
patching of diagonalizations are deliberately not asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveDiagonalizableRelativeRoot4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius
open P0EFTJanusGlobalDiagonalLorentzRoot4D

abbrev Matrix4 := P0EFTJanusGlobalDiagonalLorentzRoot4D.Matrix4
abbrev Spectrum4 := Fin 4 → Real

/-- Explicit real diagonalization data for a relative metric with strictly
positive spectrum.  Both inverse identities are stored so the change of basis
is genuinely invertible, rather than only a formal factorization. -/
structure PositiveDiagonalizableRelativeMatrix where
  target : Matrix4
  eigenbasis : Matrix4
  eigenbasisInv : Matrix4
  eigenvalue : Spectrum4
  eigenvalue_pos : ∀ index, 0 < eigenvalue index
  inv_mul_basis : eigenbasisInv * eigenbasis = 1
  basis_mul_inv : eigenbasis * eigenbasisInv = 1
  target_eq :
    target = eigenbasis * Matrix.diagonal eigenvalue * eigenbasisInv

/-- Positive square roots of the supplied real eigenvalues. -/
def positiveSimilarityRootSpectrum
    (data : PositiveDiagonalizableRelativeMatrix) : Spectrum4 :=
  fun index => Real.sqrt (data.eigenvalue index)

theorem positiveSimilarityRootSpectrum_pos
    (data : PositiveDiagonalizableRelativeMatrix) (index : Fin 4) :
    0 < positiveSimilarityRootSpectrum data index :=
  Real.sqrt_pos.2 (data.eigenvalue_pos index)

/-- The diagonal square root in the supplied eigenbasis. -/
def positiveSimilarityDiagonalRoot
    (data : PositiveDiagonalizableRelativeMatrix) : Matrix4 :=
  Matrix.diagonal (positiveSimilarityRootSpectrum data)

theorem positiveSimilarityDiagonalRoot_square
    (data : PositiveDiagonalizableRelativeMatrix) :
    positiveSimilarityDiagonalRoot data *
        positiveSimilarityDiagonalRoot data =
      Matrix.diagonal data.eigenvalue := by
  ext first second
  by_cases hIndices : first = second
  · subst second
    simp [positiveSimilarityDiagonalRoot, positiveSimilarityRootSpectrum,
      Real.mul_self_sqrt (le_of_lt (data.eigenvalue_pos first))]
  · simp [positiveSimilarityDiagonalRoot, hIndices]

/-- Selected real root obtained by conjugating the positive diagonal root.
It is called a similarity root rather than a principal root because basis
independence has not yet been proved. -/
def positiveSimilarityRoot
    (data : PositiveDiagonalizableRelativeMatrix) : Matrix4 :=
  data.eigenbasis * positiveSimilarityDiagonalRoot data * data.eigenbasisInv

theorem positiveSimilarityRoot_square
    (data : PositiveDiagonalizableRelativeMatrix) :
    positiveSimilarityRoot data * positiveSimilarityRoot data = data.target := by
  rw [data.target_eq]
  unfold positiveSimilarityRoot
  calc
    (data.eigenbasis * positiveSimilarityDiagonalRoot data * data.eigenbasisInv) *
          (data.eigenbasis * positiveSimilarityDiagonalRoot data *
            data.eigenbasisInv) =
        data.eigenbasis * positiveSimilarityDiagonalRoot data *
          (data.eigenbasisInv * data.eigenbasis) *
          positiveSimilarityDiagonalRoot data * data.eigenbasisInv := by
            noncomm_ring
    _ = data.eigenbasis * positiveSimilarityDiagonalRoot data * 1 *
          positiveSimilarityDiagonalRoot data * data.eigenbasisInv := by
            rw [data.inv_mul_basis]
    _ = data.eigenbasis *
          (positiveSimilarityDiagonalRoot data *
            positiveSimilarityDiagonalRoot data) * data.eigenbasisInv := by
            simp [mul_assoc]
    _ = data.eigenbasis * Matrix.diagonal data.eigenvalue *
          data.eigenbasisInv := by
            rw [positiveSimilarityDiagonalRoot_square]

/-- A nonempty base point for the positive diagonalizable locus. -/
def identityPositiveDiagonalizableRelativeMatrix :
    PositiveDiagonalizableRelativeMatrix where
  target := 1
  eigenbasis := 1
  eigenbasisInv := 1
  eigenvalue := fun _ => 1
  eigenvalue_pos := by intro; norm_num
  inv_mul_basis := by simp
  basis_mul_inv := by simp
  target_eq := by
    ext first second
    by_cases hIndices : first = second
    · subst second
      simp
    · simp [hIndices]

theorem positiveDiagonalizableRelativeMatrix_nonempty :
    Nonempty PositiveDiagonalizableRelativeMatrix :=
  ⟨identityPositiveDiagonalizableRelativeMatrix⟩

@[simp]
theorem identityPositiveDiagonalizableRelativeMatrix_root :
    positiveSimilarityRoot identityPositiveDiagonalizableRelativeMatrix =
      (1 : Matrix4) := by
  ext first second
  by_cases hIndices : first = second
  · subst second
    simp [positiveSimilarityRoot, positiveSimilarityDiagonalRoot,
      positiveSimilarityRootSpectrum,
      identityPositiveDiagonalizableRelativeMatrix]
  · simp [positiveSimilarityRoot, positiveSimilarityDiagonalRoot,
      positiveSimilarityRootSpectrum,
      identityPositiveDiagonalizableRelativeMatrix, hIndices]

/-- Closure statement for the precise locus treated in this gate. -/
theorem positive_diagonalizable_relative_root_closure
    (data : PositiveDiagonalizableRelativeMatrix) :
    (∀ index, 0 < positiveSimilarityRootSpectrum data index) ∧
      positiveSimilarityRoot data * positiveSimilarityRoot data = data.target :=
  ⟨positiveSimilarityRootSpectrum_pos data,
    positiveSimilarityRoot_square data⟩

end

end P0EFTJanusPositiveDiagonalizableRelativeRoot4D
end JanusFormal
