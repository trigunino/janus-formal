import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMatrixZeroOverZeroUniversalExtensionNoGo4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalDiagonalPowerLawZeroOverZeroClassification4D

/-!
# Fixed-similarity matrix zero-over-zero obstruction

The diagonal coefficient family is embedded into real `4 × 4` matrices and
transported by one fixed similarity.  Conjugating back recovers every
principal-root coordinate exactly.  Hence the diagonal two-path obstruction
also rules out a continuous single-valued extension on this entire fixed
simultaneously-diagonalizable matrix class.
-/

namespace JanusFormal
namespace P0EFTJanusFixedSimilarityMatrixZeroOverZeroNoGo4D

set_option autoImplicit false

open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusGlobalDiagonalZeroOverZeroPathDependence4D
open P0EFTJanusMatrixZeroOverZeroUniversalExtensionNoGo4D
open P0EFTJanusGlobalDiagonalPowerLawZeroOverZeroClassification4D

abbrev Matrix4 := Matrix (Fin 4) (Fin 4) Real
abbrev CoefficientPair :=
  P0EFTJanusGlobalDiagonalZeroOverZeroPathDependence4D.CoefficientPair
abbrev Coefficients4 :=
  P0EFTJanusGlobalDiagonalZeroOverZeroPathDependence4D.Coefficients4

def fixedSimilarityMatrixPair
    (change inverse : Matrix4) (coefficients : CoefficientPair) : Matrix4 × Matrix4 :=
  (change * Matrix.diagonal coefficients.1 * inverse,
    change * Matrix.diagonal coefficients.2 * inverse)

def fixedSimilarityExtractSpectrum
    (inverse change root : Matrix4) : Coefficients4 :=
  fun i => (inverse * root * change) i i

noncomputable def fixedSimilarityPrincipalRoot
    (change inverse : Matrix4) (coefficients : CoefficientPair) : Matrix4 :=
  change * Matrix.diagonal (principalRootSpectrum coefficients) * inverse

theorem fixedSimilarityExtractSpectrum_transport
    (change inverse : Matrix4) (hInverse : inverse * change = 1)
    (spectrum : Coefficients4) :
    fixedSimilarityExtractSpectrum inverse change
        (change * Matrix.diagonal spectrum * inverse) = spectrum := by
  funext i
  unfold fixedSimilarityExtractSpectrum
  have hMatrix :
      inverse * (change * Matrix.diagonal spectrum * inverse) * change =
        Matrix.diagonal spectrum := by
    calc
      inverse * (change * Matrix.diagonal spectrum * inverse) * change =
          (inverse * change) * Matrix.diagonal spectrum * (inverse * change) := by
        noncomm_ring
      _ = Matrix.diagonal spectrum := by rw [hInverse]; simp
  rw [hMatrix]
  simp

theorem fixedSimilarityPowerLaw_equal_exponents_tendsto_one
    (change inverse : Matrix4) (hInverse : inverse * change = 1)
    (point : CoefficientPair) (i : Fin 4) (m : Nat) (hm : 0 < m) :
    Filter.Tendsto
      (fun t => fixedSimilarityExtractSpectrum inverse change
        (fixedSimilarityPrincipalRoot change inverse
          (powerLawZeroOverZeroPath point i m m t)) i)
      (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 1) := by
  simpa [fixedSimilarityPrincipalRoot,
    fixedSimilarityExtractSpectrum_transport change inverse hInverse] using
    powerLawZeroOverZeroPath_equal_exponents_tendsto_one point i m hm

theorem fixedSimilarityPowerLaw_numerator_faster_tendsto_zero
    (change inverse : Matrix4) (hInverse : inverse * change = 1)
    (point : CoefficientPair) (i : Fin 4) (m n : Nat)
    (hm : 0 < m) (hn : 0 < n) (hnm : n < m) :
    Filter.Tendsto
      (fun t => fixedSimilarityExtractSpectrum inverse change
        (fixedSimilarityPrincipalRoot change inverse
          (powerLawZeroOverZeroPath point i m n t)) i)
      (nhdsWithin (0 : Real) (Set.Ioi 0)) (nhds 0) := by
  simpa [fixedSimilarityPrincipalRoot,
    fixedSimilarityExtractSpectrum_transport change inverse hInverse] using
    powerLawZeroOverZeroPath_numerator_faster_tendsto_zero point i m n hm hn hnm

theorem fixedSimilarityPowerLaw_denominator_faster_tendsto_atTop
    (change inverse : Matrix4) (hInverse : inverse * change = 1)
    (point : CoefficientPair) (i : Fin 4) (m n : Nat)
    (hm : 0 < m) (hn : 0 < n) (hmn : m < n) :
    Filter.Tendsto
      (fun t => fixedSimilarityExtractSpectrum inverse change
        (fixedSimilarityPrincipalRoot change inverse
          (powerLawZeroOverZeroPath point i m n t)) i)
      (nhdsWithin (0 : Real) (Set.Ioi 0)) Filter.atTop := by
  simpa [fixedSimilarityPrincipalRoot,
    fixedSimilarityExtractSpectrum_transport change inverse hInverse] using
    powerLawZeroOverZeroPath_denominator_faster_tendsto_atTop point i m n hm hn hmn

theorem no_continuous_fixed_similarity_matrix_root_extension
    {point : CoefficientPair} (hPoint : point ∈ globalDiagonalLorentzDomain)
    (i : Fin 4) (change inverse : Matrix4)
    (matrixRootExtension : Matrix4 × Matrix4 → Matrix4)
    (hContinuousRestriction : ContinuousAt
      (fun coefficients =>
        fixedSimilarityExtractSpectrum inverse change
          (matrixRootExtension
            (fixedSimilarityMatrixPair change inverse coefficients)))
      (equalRateZeroOverZeroPath point i 0))
    (hAgrees : ∀ interior, interior ∈ globalDiagonalLorentzDomain →
      fixedSimilarityExtractSpectrum inverse change
          (matrixRootExtension
            (fixedSimilarityMatrixPair change inverse interior)) =
        principalRootSpectrum interior) : False := by
  exact no_continuous_universal_matrix_extension_of_diagonal_restriction
    hPoint i (fixedSimilarityMatrixPair change inverse)
    (fun state => fixedSimilarityExtractSpectrum inverse change (matrixRootExtension state))
    hContinuousRestriction hAgrees

end P0EFTJanusFixedSimilarityMatrixZeroOverZeroNoGo4D
end JanusFormal
