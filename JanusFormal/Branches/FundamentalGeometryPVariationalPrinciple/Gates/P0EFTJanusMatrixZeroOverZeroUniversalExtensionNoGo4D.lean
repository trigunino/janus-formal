import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalDiagonalZeroOverZeroPathDependence4D

/-!
# Matrix zero-over-zero universal-extension obstruction

Any continuous single-valued root extension on a matrix state space that
contains the diagonal coefficient family would restrict to a forbidden
continuous extension at the diagonal zero-over-zero corner.  This does not
classify matrix or Jordan paths; it rules out a universal path-independent
continuous value before such a classification is attempted.
-/

namespace JanusFormal
namespace P0EFTJanusMatrixZeroOverZeroUniversalExtensionNoGo4D

set_option autoImplicit false

open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusGlobalDiagonalZeroOverZeroPathDependence4D

variable {MatrixState : Type*}

theorem no_continuous_universal_matrix_extension_of_diagonal_restriction
    {point : P0EFTJanusGlobalDiagonalZeroOverZeroPathDependence4D.CoefficientPair}
    (hPoint : point ∈ globalDiagonalLorentzDomain)
    (i : Fin 4)
    (diagonalEmbedding :
      P0EFTJanusGlobalDiagonalZeroOverZeroPathDependence4D.CoefficientPair → MatrixState)
    (matrixRootExtension : MatrixState →
      P0EFTJanusGlobalDiagonalZeroOverZeroPathDependence4D.Coefficients4)
    (hContinuousDiagonalRestriction :
      ContinuousAt (matrixRootExtension ∘ diagonalEmbedding)
        (equalRateZeroOverZeroPath point i 0))
    (hAgreesOnDiagonal : ∀ interior,
      interior ∈ globalDiagonalLorentzDomain →
      matrixRootExtension (diagonalEmbedding interior) =
        principalRootSpectrum interior) : False := by
  apply no_continuous_principalRootSpectrum_extension_at_zeroOverZero hPoint i
  exact ⟨matrixRootExtension ∘ diagonalEmbedding,
    hContinuousDiagonalRestriction, hAgreesOnDiagonal⟩

end P0EFTJanusMatrixZeroOverZeroUniversalExtensionNoGo4D
end JanusFormal
