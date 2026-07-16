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

/-- Commuting with the positive diagonal target already forces commutation
with its selected positive square root.  Entrywise, off-eigenspace matrix
coefficients vanish, while equal eigenspaces have equal positive roots. -/
theorem commute_diagonal_eigenvalue_implies_commute_positive_root
    (data : PositiveDiagonalizableRelativeMatrix)
    (scale : Matrix4)
    (hCommute : scale * Matrix.diagonal data.eigenvalue =
      Matrix.diagonal data.eigenvalue * scale) :
    scale * positiveSimilarityDiagonalRoot data =
      positiveSimilarityDiagonalRoot data * scale := by
  ext first second
  have hEntry := congrArg (fun matrix => matrix first second) hCommute
  simp [Matrix.mul_apply, Matrix.diagonal,
    positiveSimilarityDiagonalRoot, positiveSimilarityRootSpectrum] at hEntry ⊢
  by_cases hEigenvalue : data.eigenvalue first = data.eigenvalue second
  · rw [hEigenvalue]
    ring
  · have hScale : scale first second = 0 := by
      have hProduct : scale first second *
          (data.eigenvalue second - data.eigenvalue first) = 0 := by
        nlinarith [hEntry]
      exact (mul_eq_zero.mp hProduct).resolve_right
        (sub_ne_zero.mpr (Ne.symm hEigenvalue))
    rw [hScale]
    simp

/-- Any linear change supported inside equal-eigenvalue blocks commutes with
the selected positive diagonal root.  Thus arbitrary mixing inside repeated
eigenspaces is allowed, not only diagonal rescaling. -/
theorem positiveSimilarityDiagonalRoot_commutes_of_preserves_eigenspaces
    (data : PositiveDiagonalizableRelativeMatrix)
    (change : Matrix4)
    (hPreserves : ∀ first second,
      change first second ≠ 0 →
        data.eigenvalue first = data.eigenvalue second) :
    change * positiveSimilarityDiagonalRoot data =
      positiveSimilarityDiagonalRoot data * change := by
  ext first second
  unfold positiveSimilarityDiagonalRoot
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  by_cases hEntry : change first second = 0
  · simp [hEntry]
  · have hRoot : positiveSimilarityRootSpectrum data first =
        positiveSimilarityRootSpectrum data second := by
      simp only [positiveSimilarityRootSpectrum]
      rw [hPreserves first second hEntry]
    rw [hRoot]
    ring

/-- Selected real root obtained by conjugating the positive diagonal root.
It is called a similarity root rather than a principal root because basis
independence has not yet been proved. -/
def positiveSimilarityRoot
    (data : PositiveDiagonalizableRelativeMatrix) : Matrix4 :=
  data.eigenbasis * positiveSimilarityDiagonalRoot data * data.eigenbasisInv

/-- The selected similarity root is unchanged by an invertible rescaling of
the supplied eigenbasis that commutes with the positive diagonal root.  This
removes the diagonal commutant part of the eigenbasis ambiguity; arbitrary
changes inside repeated eigenspaces and global gluing remain separate. -/
theorem positiveSimilarityRoot_invariant_under_commuting_rescaling
    (data : PositiveDiagonalizableRelativeMatrix)
    (scale scaleInv : Matrix4)
    (hInv : scale * scaleInv = 1)
    (hCommute : scale * positiveSimilarityDiagonalRoot data =
      positiveSimilarityDiagonalRoot data * scale) :
    (data.eigenbasis * scale) * positiveSimilarityDiagonalRoot data *
        (scaleInv * data.eigenbasisInv) =
      positiveSimilarityRoot data := by
  unfold positiveSimilarityRoot
  calc
    (data.eigenbasis * scale) * positiveSimilarityDiagonalRoot data *
          (scaleInv * data.eigenbasisInv) =
        data.eigenbasis * (scale * positiveSimilarityDiagonalRoot data) *
          scaleInv * data.eigenbasisInv := by noncomm_ring
    _ = data.eigenbasis * (positiveSimilarityDiagonalRoot data * scale) *
          scaleInv * data.eigenbasisInv := by rw [hCommute]
    _ = data.eigenbasis * positiveSimilarityDiagonalRoot data *
          (scale * scaleInv) * data.eigenbasisInv := by noncomm_ring
    _ = data.eigenbasis * positiveSimilarityDiagonalRoot data *
          data.eigenbasisInv := by rw [hInv]; simp

/-- It is enough to check commutation with the supplied diagonal eigenvalue
matrix: positivity then transfers commutation to the selected diagonal root. -/
theorem positiveSimilarityRoot_invariant_under_eigenvalue_commuting_rescaling
    (data : PositiveDiagonalizableRelativeMatrix)
    (scale scaleInv : Matrix4)
    (hInv : scale * scaleInv = 1)
    (hCommute : scale * Matrix.diagonal data.eigenvalue =
      Matrix.diagonal data.eigenvalue * scale) :
    (data.eigenbasis * scale) * positiveSimilarityDiagonalRoot data *
        (scaleInv * data.eigenbasisInv) =
      positiveSimilarityRoot data :=
  positiveSimilarityRoot_invariant_under_commuting_rescaling data scale scaleInv
    hInv (commute_diagonal_eigenvalue_implies_commute_positive_root
      data scale hCommute)

/-- Consequently, every invertible change of basis acting only inside repeated
eigenspaces leaves the selected similarity root unchanged. -/
theorem positiveSimilarityRoot_invariant_under_eigenspace_change
    (data : PositiveDiagonalizableRelativeMatrix)
    (change changeInv : Matrix4)
    (hInv : change * changeInv = 1)
    (hPreserves : ∀ first second,
      change first second ≠ 0 →
        data.eigenvalue first = data.eigenvalue second) :
    (data.eigenbasis * change) * positiveSimilarityDiagonalRoot data *
        (changeInv * data.eigenbasisInv) =
      positiveSimilarityRoot data :=
  positiveSimilarityRoot_invariant_under_commuting_rescaling data change changeInv
    hInv (positiveSimilarityDiagonalRoot_commutes_of_preserves_eigenspaces
      data change hPreserves)

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
