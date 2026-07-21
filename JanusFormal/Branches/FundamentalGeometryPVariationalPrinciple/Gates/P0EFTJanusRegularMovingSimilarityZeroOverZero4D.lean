import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFixedSimilarityMatrixZeroOverZeroNoGo4D

/-!
# Regular moving similarities at a matrix zero-over-zero corner

A regular moving frame has convergent change-of-frame and inverse matrices and
an exact inverse law along the path.  Matrix limits then transport by
continuity of multiplication.  Independently, conjugating back recovers each
root coordinate exactly, so the monomial `0/0` trichotomy survives every such
moving frame.  No conclusion is asserted for singular moving frames.
-/

namespace JanusFormal
namespace P0EFTJanusRegularMovingSimilarityZeroOverZero4D

set_option autoImplicit false

open Filter
open scoped Topology
open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusGlobalDiagonalPowerLawZeroOverZeroClassification4D
open P0EFTJanusFixedSimilarityMatrixZeroOverZeroNoGo4D

abbrev Matrix4 := P0EFTJanusFixedSimilarityMatrixZeroOverZeroNoGo4D.Matrix4
abbrev CoefficientPair :=
  P0EFTJanusGlobalDiagonalPowerLawZeroOverZeroClassification4D.CoefficientPair
abbrev Coefficients4 :=
  P0EFTJanusGlobalDiagonalPowerLawZeroOverZeroClassification4D.Coefficients4

structure RegularMovingSimilarityAt
    (filter : Filter Real)
    (change inverse : Real → Matrix4)
    (limitChange limitInverse : Matrix4) : Prop where
  change_tendsto : Tendsto change filter (nhds limitChange)
  inverse_tendsto : Tendsto inverse filter (nhds limitInverse)
  leftInverse : ∀ t, inverse t * change t = 1

noncomputable def movingSimilarityPrincipalRoot
    (change inverse : Real → Matrix4)
    (path : Real → CoefficientPair) (t : Real) : Matrix4 :=
  change t * Matrix.diagonal (principalRootSpectrum (path t)) * inverse t

def movingSimilarityExtractSpectrum
    (change inverse : Real → Matrix4)
    (root : Real → Matrix4) (t : Real) : Coefficients4 :=
  fun i => (inverse t * root t * change t) i i

theorem movingSimilarityExtractSpectrum_principalRoot
    (change inverse : Real → Matrix4)
    (hInverse : ∀ t, inverse t * change t = 1)
    (path : Real → CoefficientPair) (t : Real) :
    movingSimilarityExtractSpectrum change inverse
        (movingSimilarityPrincipalRoot change inverse path) t =
      principalRootSpectrum (path t) := by
  exact fixedSimilarityExtractSpectrum_transport (change t) (inverse t)
    (hInverse t) (principalRootSpectrum (path t))

theorem regularMovingSimilarity_transport_matrix_limit
    {filter : Filter Real}
    (change inverse : Real → Matrix4)
    (limitChange limitInverse : Matrix4)
    (hRegular : RegularMovingSimilarityAt filter change inverse
      limitChange limitInverse)
    (diagonalRoot : Real → Matrix4) (limitDiagonalRoot : Matrix4)
    (hDiagonal : Tendsto diagonalRoot filter (nhds limitDiagonalRoot)) :
    Tendsto (fun t => change t * diagonalRoot t * inverse t) filter
      (nhds (limitChange * limitDiagonalRoot * limitInverse)) := by
  exact (hRegular.change_tendsto.mul hDiagonal).mul hRegular.inverse_tendsto

theorem regularMovingSimilarity_equal_exponents_tendsto_one
    (change inverse : Real → Matrix4)
    (hInverse : ∀ t, inverse t * change t = 1)
    (point : CoefficientPair) (i : Fin 4) (m : Nat) (hm : 0 < m) :
    Tendsto
      (fun t => movingSimilarityExtractSpectrum change inverse
        (movingSimilarityPrincipalRoot change inverse
          (fun s => powerLawZeroOverZeroPath point i m m s)) t i)
      (𝓝[>] (0 : Real)) (nhds 1) := by
  simpa [movingSimilarityExtractSpectrum_principalRoot change inverse hInverse] using
    powerLawZeroOverZeroPath_equal_exponents_tendsto_one point i m hm

theorem regularMovingSimilarity_numerator_faster_tendsto_zero
    (change inverse : Real → Matrix4)
    (hInverse : ∀ t, inverse t * change t = 1)
    (point : CoefficientPair) (i : Fin 4) (m n : Nat)
    (hm : 0 < m) (hn : 0 < n) (hnm : n < m) :
    Tendsto
      (fun t => movingSimilarityExtractSpectrum change inverse
        (movingSimilarityPrincipalRoot change inverse
          (fun s => powerLawZeroOverZeroPath point i m n s)) t i)
      (𝓝[>] (0 : Real)) (nhds 0) := by
  simpa [movingSimilarityExtractSpectrum_principalRoot change inverse hInverse] using
    powerLawZeroOverZeroPath_numerator_faster_tendsto_zero point i m n hm hn hnm

theorem regularMovingSimilarity_denominator_faster_tendsto_atTop
    (change inverse : Real → Matrix4)
    (hInverse : ∀ t, inverse t * change t = 1)
    (point : CoefficientPair) (i : Fin 4) (m n : Nat)
    (hm : 0 < m) (hn : 0 < n) (hmn : m < n) :
    Tendsto
      (fun t => movingSimilarityExtractSpectrum change inverse
        (movingSimilarityPrincipalRoot change inverse
          (fun s => powerLawZeroOverZeroPath point i m n s)) t i)
      (𝓝[>] (0 : Real)) atTop := by
  simpa [movingSimilarityExtractSpectrum_principalRoot change inverse hInverse] using
    powerLawZeroOverZeroPath_denominator_faster_tendsto_atTop point i m n hm hn hmn

end P0EFTJanusRegularMovingSimilarityZeroOverZero4D
end JanusFormal
