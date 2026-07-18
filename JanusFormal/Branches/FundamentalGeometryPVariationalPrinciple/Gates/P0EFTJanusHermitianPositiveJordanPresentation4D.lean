import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRawSpectralBridgeReduction4D

/-!
# Positive real Jordan presentation on the Hermitian raw sector

Mathlib's spectral theorem supplies an orthonormal eigenbasis for every real
Hermitian matrix.  Hence the missing raw Jordan-basis bridge is unconditional
on this sector: positivity of the four spectral values packages directly as
the diagonal member of the unified positive Jordan presentation.
-/

namespace JanusFormal
namespace P0EFTJanusHermitianPositiveJordanPresentation4D

set_option autoImplicit false

noncomputable section

open Matrix Unitary
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveRealJordanPartitionSelector4D
open P0EFTJanusPositiveRealJordanPresentationBridge4D
open P0EFTJanusRawSpectralBridgeReduction4D

abbrev Matrix4 := P0EFTJanusRawSpectralBridgeReduction4D.Matrix4

/-- The spectral-theorem diagonal presentation attached to a real Hermitian
matrix whose eigenvalues are strictly positive. -/
def hermitianPositiveDiagonalPresentation
    (target : Matrix4) (hHermitian : target.IsHermitian)
    (hPositive : ∀ index, 0 < hHermitian.eigenvalues index) :
    PositiveDiagonalPresentation4 :=
  ⟨(⟨hHermitian.eigenvalues, hPositive⟩,
      ((hHermitian.eigenvectorUnitary : Matrix4),
        star (hHermitian.eigenvectorUnitary : Matrix4))),
    Unitary.coe_star_mul_self hHermitian.eigenvectorUnitary,
    Unitary.coe_mul_star_self hHermitian.eigenvectorUnitary⟩

theorem hermitianPositiveDiagonalPresentation_target
    (target : Matrix4) (hHermitian : target.IsHermitian)
    (hPositive : ∀ index, 0 < hHermitian.eigenvalues index) :
    diagonalPresentationTarget
        (hermitianPositiveDiagonalPresentation target hHermitian hPositive) =
      target := by
  simpa [hermitianPositiveDiagonalPresentation, diagonalPresentationTarget,
    diagonalPresentationChange, diagonalPresentationSpectrum,
    diagonalPresentationInverse, Unitary.conjStarAlgAut_apply] using
      hHermitian.spectral_theorem.symm

/-- Concrete intrinsic spectral data suffice to construct the unified
positive real Jordan presentation; no Jordan-chain basis is assumed. -/
theorem hasPositiveRealJordanPresentation_of_isHermitian_eigenvalues_pos
    (target : Matrix4) (hHermitian : target.IsHermitian)
    (hPositive : ∀ index, 0 < hHermitian.eigenvalues index) :
    HasPositiveRealJordanPresentation target := by
  exact ⟨.diagonal
      (hermitianPositiveDiagonalPresentation target hHermitian hPositive),
    hermitianPositiveDiagonalPresentation_target target hHermitian hPositive⟩

/-- Positive definiteness is a standard concrete sufficient hypothesis for
the previously missing raw presentation. -/
theorem posDef_hasPositiveRealJordanPresentation
    {target : Matrix4} (hTarget : target.PosDef) :
    HasPositiveRealJordanPresentation target :=
  hasPositiveRealJordanPresentation_of_isHermitian_eigenvalues_pos target
    hTarget.isHermitian hTarget.eigenvalues_pos

/-- A positive split characteristic polynomial closes the presentation bridge
whenever the raw matrix is Hermitian. -/
theorem positiveRealSplit_isHermitian_hasPositiveRealJordanPresentation
    {target : Matrix4} (hSpectrum : PositiveRealSplitCharpoly4 target)
    (hHermitian : target.IsHermitian) :
    HasPositiveRealJordanPresentation target := by
  apply hasPositiveRealJordanPresentation_of_isHermitian_eigenvalues_pos
    target hHermitian
  intro index
  exact hSpectrum.2 (hHermitian.eigenvalues index)
    (Matrix.mem_spectrum_iff_isRoot_charpoly.mp
      (hHermitian.eigenvalues_mem_spectrum_real index))

/-- All downstream analytic regularity follows on the Hermitian positive raw
sector from the constructed diagonal presentation. -/
theorem positiveRealSplit_isHermitian_hasSylvesterRegularRealSquareRoot
    {target : Matrix4} (hSpectrum : PositiveRealSplitCharpoly4 target)
    (hHermitian : target.IsHermitian) :
    HasSylvesterRegularRealSquareRoot target :=
  hasSylvesterRegularRealSquareRoot_of_presentation target
    (positiveRealSplit_isHermitian_hasPositiveRealJordanPresentation
      hSpectrum hHermitian)

/-- The unresolved positive raw presentation bridge is reduced exactly to
the non-Hermitian sector. -/
def PositiveRealNonHermitianJordanPresentationResidual4 : Prop :=
  ∀ target : Matrix4, PositiveRealSplitCharpoly4 target →
    ¬ target.IsHermitian → HasPositiveRealJordanPresentation target

theorem positiveRealJordanBasisBridge4_iff_nonHermitianResidual :
    PositiveRealJordanBasisBridge4 ↔
      PositiveRealNonHermitianJordanPresentationResidual4 := by
  constructor
  · intro bridge target hSpectrum _hNonHermitian
    exact bridge target hSpectrum
  · intro residual target hSpectrum
    by_cases hHermitian : target.IsHermitian
    · exact positiveRealSplit_isHermitian_hasPositiveRealJordanPresentation
        hSpectrum hHermitian
    · exact residual target hSpectrum hHermitian

end

end P0EFTJanusHermitianPositiveJordanPresentation4D
end JanusFormal
