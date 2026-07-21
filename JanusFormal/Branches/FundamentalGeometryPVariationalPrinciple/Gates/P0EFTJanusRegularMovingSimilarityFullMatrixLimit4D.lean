import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularMovingSimilarityZeroOverZero4D

/-!
# Full matrix limits in a regular moving frame

The finite branches of the diagonal monomial `0/0` trichotomy converge as
whole matrices after any regular moving similarity.  Singular moving frames
and general matrix paths are not covered.
-/

namespace JanusFormal
namespace P0EFTJanusRegularMovingSimilarityFullMatrixLimit4D

set_option autoImplicit false

noncomputable section

open Filter
open scoped Topology
open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusGlobalDiagonalRootFrontierControl4D
open P0EFTJanusGlobalDiagonalPowerLawZeroOverZeroClassification4D
open P0EFTJanusRegularMovingSimilarityZeroOverZero4D

abbrev Matrix4 := P0EFTJanusRegularMovingSimilarityZeroOverZero4D.Matrix4
abbrev CoefficientPair :=
  P0EFTJanusGlobalDiagonalPowerLawZeroOverZeroClassification4D.CoefficientPair
abbrev Coefficients4 :=
  P0EFTJanusGlobalDiagonalPowerLawZeroOverZeroClassification4D.Coefficients4

def powerLawFiniteLimitSpectrum
    (point : CoefficientPair) (i : Fin 4) (value : Real) : Coefficients4 :=
  Function.update (principalRootSpectrum point) i value

theorem powerLawZeroOverZeroPath_root_eq_of_ne
    (point : CoefficientPair) (i j : Fin 4) (m n : Nat) (hji : j ≠ i)
    (t : Real) :
    principalRootSpectrum (powerLawZeroOverZeroPath point i m n t) j =
      principalRootSpectrum point j := by
  simp [principalRootSpectrum, relativeRatio, powerLawZeroOverZeroPath,
    replaceMagnitude, hji]

theorem powerLawSpectrum_equal_exponents_tendsto
    (point : CoefficientPair) (i : Fin 4) (m : Nat) (hm : 0 < m) :
    Tendsto
      (fun t => principalRootSpectrum
        (powerLawZeroOverZeroPath point i m m t))
      (𝓝[>] (0 : Real))
      (nhds (powerLawFiniteLimitSpectrum point i 1)) := by
  rw [tendsto_pi_nhds]
  intro j
  by_cases hji : j = i
  · subst j
    simpa [powerLawFiniteLimitSpectrum] using
      powerLawZeroOverZeroPath_equal_exponents_tendsto_one point i m hm
  · simpa [powerLawFiniteLimitSpectrum, hji,
      powerLawZeroOverZeroPath_root_eq_of_ne point i j m m hji] using
      (tendsto_const_nhds : Tendsto
        (fun _ : Real => principalRootSpectrum point j)
        (𝓝[>] (0 : Real)) (nhds (principalRootSpectrum point j)))

theorem powerLawSpectrum_numerator_faster_tendsto
    (point : CoefficientPair) (i : Fin 4) (m n : Nat)
    (hm : 0 < m) (hn : 0 < n) (hnm : n < m) :
    Tendsto
      (fun t => principalRootSpectrum
        (powerLawZeroOverZeroPath point i m n t))
      (𝓝[>] (0 : Real))
      (nhds (powerLawFiniteLimitSpectrum point i 0)) := by
  rw [tendsto_pi_nhds]
  intro j
  by_cases hji : j = i
  · subst j
    simpa [powerLawFiniteLimitSpectrum] using
      powerLawZeroOverZeroPath_numerator_faster_tendsto_zero
        point i m n hm hn hnm
  · simpa [powerLawFiniteLimitSpectrum, hji,
      powerLawZeroOverZeroPath_root_eq_of_ne point i j m n hji] using
      (tendsto_const_nhds : Tendsto
        (fun _ : Real => principalRootSpectrum point j)
        (𝓝[>] (0 : Real)) (nhds (principalRootSpectrum point j)))

theorem diagonalMatrix_tendsto_of_spectrum_tendsto
    (spectrum : Real → Coefficients4) (limitSpectrum : Coefficients4)
    {filter : Filter Real}
    (hSpectrum : Tendsto spectrum filter (nhds limitSpectrum)) :
    Tendsto (fun t => Matrix.diagonal (spectrum t)) filter
      (nhds (Matrix.diagonal limitSpectrum)) :=
  continuous_id.matrix_diagonal.continuousAt.tendsto.comp hSpectrum

theorem regularMovingSimilarity_equal_exponents_full_matrix_limit
    (change inverse : Real → Matrix4) (limitChange limitInverse : Matrix4)
    (hRegular : RegularMovingSimilarityAt (𝓝[>] (0 : Real)) change inverse
      limitChange limitInverse)
    (point : CoefficientPair) (i : Fin 4) (m : Nat) (hm : 0 < m) :
    Tendsto
      (movingSimilarityPrincipalRoot change inverse
        (fun t => powerLawZeroOverZeroPath point i m m t))
      (𝓝[>] (0 : Real))
      (nhds (limitChange *
        Matrix.diagonal (powerLawFiniteLimitSpectrum point i 1) *
        limitInverse)) := by
  apply regularMovingSimilarity_transport_matrix_limit
    change inverse limitChange limitInverse hRegular
  exact diagonalMatrix_tendsto_of_spectrum_tendsto _ _
    (powerLawSpectrum_equal_exponents_tendsto point i m hm)

theorem regularMovingSimilarity_numerator_faster_full_matrix_limit
    (change inverse : Real → Matrix4) (limitChange limitInverse : Matrix4)
    (hRegular : RegularMovingSimilarityAt (𝓝[>] (0 : Real)) change inverse
      limitChange limitInverse)
    (point : CoefficientPair) (i : Fin 4) (m n : Nat)
    (hm : 0 < m) (hn : 0 < n) (hnm : n < m) :
    Tendsto
      (movingSimilarityPrincipalRoot change inverse
        (fun t => powerLawZeroOverZeroPath point i m n t))
      (𝓝[>] (0 : Real))
      (nhds (limitChange *
        Matrix.diagonal (powerLawFiniteLimitSpectrum point i 0) *
        limitInverse)) := by
  apply regularMovingSimilarity_transport_matrix_limit
    change inverse limitChange limitInverse hRegular
  exact diagonalMatrix_tendsto_of_spectrum_tendsto _ _
    (powerLawSpectrum_numerator_faster_tendsto point i m n hm hn hnm)

theorem regularMovingSimilarity_denominator_faster_no_finite_matrix_limit
    (change inverse : Real → Matrix4) (limitChange limitInverse : Matrix4)
    (hRegular : RegularMovingSimilarityAt (𝓝[>] (0 : Real)) change inverse
      limitChange limitInverse)
    (point : CoefficientPair) (i : Fin 4) (m n : Nat)
    (hm : 0 < m) (hn : 0 < n) (hmn : m < n) (candidate : Matrix4) :
    ¬ Tendsto
      (movingSimilarityPrincipalRoot change inverse
        (fun t => powerLawZeroOverZeroPath point i m n t))
      (𝓝[>] (0 : Real)) (nhds candidate) := by
  intro hMatrix
  have hConjugated : Tendsto
      (fun t => inverse t *
        movingSimilarityPrincipalRoot change inverse
          (fun s => powerLawZeroOverZeroPath point i m n s) t *
        change t)
      (𝓝[>] (0 : Real))
      (nhds (limitInverse * candidate * limitChange)) :=
    (hRegular.inverse_tendsto.mul hMatrix).mul hRegular.change_tendsto
  have hFinite : Tendsto
      (fun t => movingSimilarityExtractSpectrum change inverse
        (movingSimilarityPrincipalRoot change inverse
          (fun s => powerLawZeroOverZeroPath point i m n s)) t i)
      (𝓝[>] (0 : Real))
      (nhds ((limitInverse * candidate * limitChange) i i)) := by
    simpa [movingSimilarityExtractSpectrum, Function.comp_def] using
      (continuous_id.matrix_elem i i).continuousAt.tendsto.comp hConjugated
  have hDiverges :=
    regularMovingSimilarity_denominator_faster_tendsto_atTop
      change inverse hRegular.leftInverse point i m n hm hn hmn
  exact not_tendsto_atTop_of_tendsto_nhds hFinite hDiverges

end

end P0EFTJanusRegularMovingSimilarityFullMatrixLimit4D
end JanusFormal
