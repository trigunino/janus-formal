import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalDiagonalFunctionalZeroOverZeroClassification4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularMovingSimilarityFullMatrixLimit4D

/-!
# Functional zero-over-zero paths in a regular moving frame

A finite ratio limit gives an explicit limit of the entire conjugated root
matrix.  A ratio diverging to `+∞` excludes every finite matrix limit.  The
moving frame and its inverse must both converge.
-/

namespace JanusFormal
namespace P0EFTJanusRegularMovingSimilarityFunctionalZeroOverZero4D

set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology
open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusGlobalDiagonalRootFrontierControl4D
open P0EFTJanusGlobalDiagonalFunctionalZeroOverZeroClassification4D
open P0EFTJanusRegularMovingSimilarityZeroOverZero4D
open P0EFTJanusRegularMovingSimilarityFullMatrixLimit4D

abbrev Matrix4 := P0EFTJanusRegularMovingSimilarityZeroOverZero4D.Matrix4
abbrev CoefficientPair :=
  P0EFTJanusGlobalDiagonalLorentzRoot4D.CoefficientPair
abbrev Coefficients4 :=
  P0EFTJanusGlobalDiagonalLorentzRoot4D.Coefficients4

def functionalFiniteLimitSpectrum
    (point : CoefficientPair) (i : Fin 4) (ratio : Real) : Coefficients4 :=
  Function.update (principalRootSpectrum point) i (Real.sqrt ratio)

theorem functionalZeroOverZeroPath_root_eq_of_ne
    (point : CoefficientPair) (i j : Fin 4)
    (numerator denominator : Real → Real) (hji : j ≠ i) (t : Real) :
    principalRootSpectrum
        (functionalZeroOverZeroPath point i numerator denominator t) j =
      principalRootSpectrum point j := by
  simp [principalRootSpectrum, relativeRatio, functionalZeroOverZeroPath,
    replaceMagnitude, hji]

theorem functionalSpectrum_tendsto_of_ratio
    {filter : Filter Real} (point : CoefficientPair) (i : Fin 4)
    (numerator denominator : Real → Real) (ratio : Real)
    (hRatio : Tendsto (fun t => numerator t / denominator t)
      filter (nhds ratio)) :
    Tendsto
      (fun t => principalRootSpectrum
        (functionalZeroOverZeroPath point i numerator denominator t))
      filter (nhds (functionalFiniteLimitSpectrum point i ratio)) := by
  rw [tendsto_pi_nhds]
  intro j
  by_cases hji : j = i
  · subst j
    simpa [functionalFiniteLimitSpectrum] using
      functionalZeroOverZeroPath_root_tendsto_of_ratio
        point i numerator denominator ratio hRatio
  · simpa [functionalFiniteLimitSpectrum, hji,
      functionalZeroOverZeroPath_root_eq_of_ne
        point i j numerator denominator hji] using
      (tendsto_const_nhds : Tendsto
        (fun _ : Real => principalRootSpectrum point j)
        filter (nhds (principalRootSpectrum point j)))

theorem regularMovingSimilarity_functional_full_matrix_limit
    {filter : Filter Real}
    (change inverse : Real → Matrix4) (limitChange limitInverse : Matrix4)
    (hRegular : RegularMovingSimilarityAt filter change inverse
      limitChange limitInverse)
    (point : CoefficientPair) (i : Fin 4)
    (numerator denominator : Real → Real) (ratio : Real)
    (hRatio : Tendsto (fun t => numerator t / denominator t)
      filter (nhds ratio)) :
    Tendsto
      (movingSimilarityPrincipalRoot change inverse
        (functionalZeroOverZeroPath point i numerator denominator))
      filter
      (nhds (limitChange *
        Matrix.diagonal (functionalFiniteLimitSpectrum point i ratio) *
        limitInverse)) := by
  apply regularMovingSimilarity_transport_matrix_limit
    change inverse limitChange limitInverse hRegular
  exact diagonalMatrix_tendsto_of_spectrum_tendsto _ _
    (functionalSpectrum_tendsto_of_ratio
      point i numerator denominator ratio hRatio)

theorem regularMovingSimilarity_functional_no_finite_matrix_limit
    {filter : Filter Real} [filter.NeBot]
    (change inverse : Real → Matrix4) (limitChange limitInverse : Matrix4)
    (hRegular : RegularMovingSimilarityAt filter change inverse
      limitChange limitInverse)
    (point : CoefficientPair) (i : Fin 4)
    (numerator denominator : Real → Real)
    (hRatio : Tendsto (fun t => numerator t / denominator t)
      filter atTop) (candidate : Matrix4) :
    ¬ Tendsto
      (movingSimilarityPrincipalRoot change inverse
        (functionalZeroOverZeroPath point i numerator denominator))
      filter (nhds candidate) := by
  intro hMatrix
  have hConjugated : Tendsto
      (fun t => inverse t *
        movingSimilarityPrincipalRoot change inverse
          (functionalZeroOverZeroPath point i numerator denominator) t *
        change t)
      filter (nhds (limitInverse * candidate * limitChange)) :=
    (hRegular.inverse_tendsto.mul hMatrix).mul hRegular.change_tendsto
  have hFinite : Tendsto
      (fun t => movingSimilarityExtractSpectrum change inverse
        (movingSimilarityPrincipalRoot change inverse
          (functionalZeroOverZeroPath point i numerator denominator)) t i)
      filter (nhds ((limitInverse * candidate * limitChange) i i)) := by
    simpa [movingSimilarityExtractSpectrum, Function.comp_def] using
      (continuous_id.matrix_elem i i).continuousAt.tendsto.comp hConjugated
  have hDiverges : Tendsto
      (fun t => movingSimilarityExtractSpectrum change inverse
        (movingSimilarityPrincipalRoot change inverse
          (functionalZeroOverZeroPath point i numerator denominator)) t i)
      filter atTop := by
    simpa [movingSimilarityExtractSpectrum_principalRoot
      change inverse hRegular.leftInverse] using
      functionalZeroOverZeroPath_root_tendsto_atTop_of_ratio
        point i numerator denominator hRatio
  exact not_tendsto_atTop_of_tendsto_nhds hFinite hDiverges

end

end P0EFTJanusRegularMovingSimilarityFunctionalZeroOverZero4D
end JanusFormal
