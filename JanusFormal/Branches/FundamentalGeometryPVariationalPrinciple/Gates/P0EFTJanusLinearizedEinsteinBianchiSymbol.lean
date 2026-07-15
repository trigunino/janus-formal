import Mathlib

/-!
# Linearized Einstein symbol and flat Bianchi identity

On the local Minkowski coordinate model with indices `Fin 4`, this gate
defines the principal symbol of the linearized Einstein tensor on a symmetric
covariant perturbation `h`.  With `k` a covector and
`k^mu = eta^{mu nu} k_nu`, the convention used here is

`R_mu_nu(k,h) = 1/2 (k_mu k^rho h_rho_nu + k_nu k^rho h_rho_mu
  - k^2 h_mu_nu - k_mu k_nu tr_eta h)`

and `G_mu_nu = R_mu_nu - 1/2 eta_mu_nu R`.  All contractions are finite
explicit sums.  Lean proves symmetry, the symbol-level Bianchi identity
`k^mu G_mu_nu = 0`, and annihilation of every pure-gauge symbol
`h_mu_nu = k_mu xi_nu + k_nu xi_mu` by direct calculation.

This is a flat, pointwise principal-symbol calculation.  It does not construct
the nonlinear Einstein tensor, a curved covariant divergence, a spacetime
action, boundary terms, or the Candidate-A field equations.
-/

namespace JanusFormal
namespace P0EFTJanusLinearizedEinsteinBianchiSymbol

set_option autoImplicit false

noncomputable section

abbrev Index4 := Fin 4
abbrev Covector4 := Index4 → ℝ
abbrev Tensor2 := Matrix Index4 Index4 ℝ

/-- Diagonal signs of `eta = diag(-1,1,1,1)`. -/
def etaSign (index : Index4) : ℝ :=
  if index = 0 then -1 else 1

@[simp]
theorem etaSign_sq (index : Index4) : etaSign index * etaSign index = 1 := by
  fin_cases index <;> norm_num [etaSign]

/-- Covariant and contravariant Minkowski matrices coincide in this chart. -/
def minkowskiMetric (first second : Index4) : ℝ :=
  if first = second then etaSign first else 0

theorem minkowskiMetric_symmetric (first second : Index4) :
    minkowskiMetric first second = minkowskiMetric second first := by
  by_cases hEqual : first = second
  · subst second
    rfl
  · simp [minkowskiMetric, hEqual, Ne.symm hEqual]

/-- Raise the single index of a covector with the diagonal Minkowski metric. -/
def raiseCovector (covector : Covector4) (index : Index4) : ℝ :=
  etaSign index * covector index

/-- Explicit Lorentzian square `k^2 = k^mu k_mu`. -/
def covectorSquare (covector : Covector4) : ℝ :=
  ∑ index, raiseCovector covector index * covector index

/-- A symmetric covariant rank-two perturbation. -/
structure SymmetricPerturbation where
  tensor : Tensor2
  tensor_symmetric : tensor.transpose = tensor

theorem SymmetricPerturbation.apply_comm
    (perturbation : SymmetricPerturbation) (first second : Index4) :
    perturbation.tensor first second = perturbation.tensor second first := by
  have hEntry := congrFun
    (congrFun perturbation.tensor_symmetric first) second
  simpa [Matrix.transpose_apply] using hEntry.symm

/-- Minkowski trace `eta^{rho sigma} h_rho_sigma`. -/
def minkowskiTrace (perturbation : SymmetricPerturbation) : ℝ :=
  ∑ index, etaSign index * perturbation.tensor index index

/-- One momentum contraction `k^rho h_rho_nu`. -/
def momentumContraction
    (covector : Covector4) (perturbation : SymmetricPerturbation)
    (index : Index4) : ℝ :=
  ∑ contracted,
    raiseCovector covector contracted * perturbation.tensor contracted index

/-- Double momentum contraction `k^rho k^sigma h_rho_sigma`. -/
def doubleMomentumContraction
    (covector : Covector4) (perturbation : SymmetricPerturbation) : ℝ :=
  ∑ index, raiseCovector covector index *
    momentumContraction covector perturbation index

/-- Principal symbol of the flat linearized Ricci tensor.  An overall sign
depends on the Fourier convention and is immaterial to the identities below. -/
def linearizedRicciSymbol
    (covector : Covector4) (perturbation : SymmetricPerturbation) : Tensor2 :=
  fun first second => (1 / 2 : ℝ) *
    (covector first * momentumContraction covector perturbation second +
      covector second * momentumContraction covector perturbation first -
      covectorSquare covector * perturbation.tensor first second -
      covector first * covector second * minkowskiTrace perturbation)

/-- Principal symbol of the flat linearized scalar curvature. -/
def linearizedScalarCurvatureSymbol
    (covector : Covector4) (perturbation : SymmetricPerturbation) : ℝ :=
  doubleMomentumContraction covector perturbation -
    covectorSquare covector * minkowskiTrace perturbation

/-- Principal symbol of the flat linearized Einstein tensor. -/
def linearizedEinsteinSymbol
    (covector : Covector4) (perturbation : SymmetricPerturbation) : Tensor2 :=
  fun first second =>
    linearizedRicciSymbol covector perturbation first second -
      (1 / 2 : ℝ) * minkowskiMetric first second *
        linearizedScalarCurvatureSymbol covector perturbation

/-- The Ricci principal symbol is symmetric on symmetric perturbations. -/
theorem linearizedRicciSymbol_symmetric
    (covector : Covector4) (perturbation : SymmetricPerturbation)
    (first second : Index4) :
    linearizedRicciSymbol covector perturbation first second =
      linearizedRicciSymbol covector perturbation second first := by
  simp only [linearizedRicciSymbol]
  rw [perturbation.apply_comm first second]
  ring

/-- The Einstein principal symbol is symmetric. -/
theorem linearizedEinsteinSymbol_symmetric
    (covector : Covector4) (perturbation : SymmetricPerturbation)
    (first second : Index4) :
    linearizedEinsteinSymbol covector perturbation first second =
      linearizedEinsteinSymbol covector perturbation second first := by
  rw [linearizedEinsteinSymbol, linearizedEinsteinSymbol,
    linearizedRicciSymbol_symmetric covector perturbation first second,
    minkowskiMetric_symmetric first second]

/-- Four-term expansion used to make the finite index calculations explicit. -/
theorem sum_fin_four (term : Index4 → ℝ) :
    ∑ index, term index = term 0 + term 1 + term 2 + term 3 := by
  simp [Fin.sum_univ_succ]
  ring

/-- Raised momentum contracted into the covariant Minkowski metric gives the
original covector. -/
theorem raisedCovector_contract_minkowski
    (covector : Covector4) (index : Index4) :
    ∑ contracted,
        raiseCovector covector contracted *
          minkowskiMetric contracted index =
      covector index := by
  fin_cases index <;>
    simp [raiseCovector, minkowskiMetric, etaSign]

/-- Symbol-level divergence `k^mu G_mu_nu`. -/
def einsteinSymbolDivergence
    (covector : Covector4) (perturbation : SymmetricPerturbation)
    (index : Index4) : ℝ :=
  ∑ contracted, raiseCovector covector contracted *
    linearizedEinsteinSymbol covector perturbation contracted index

/-- Flat linearized Bianchi identity, proved from the displayed symbol rather
than supplied as a conservation hypothesis. -/
theorem linearizedEinsteinSymbol_bianchi
    (covector : Covector4) (perturbation : SymmetricPerturbation)
    (index : Index4) :
    einsteinSymbolDivergence covector perturbation index = 0 := by
  fin_cases index <;>
    simp [einsteinSymbolDivergence, linearizedEinsteinSymbol,
      linearizedRicciSymbol, linearizedScalarCurvatureSymbol,
      doubleMomentumContraction, momentumContraction, minkowskiTrace,
      covectorSquare, raiseCovector, minkowskiMetric, etaSign,
      sum_fin_four] <;>
    ring

/-- Pure linearized diffeomorphism direction
`h_mu_nu = k_mu xi_nu + k_nu xi_mu`. -/
def pureGaugePerturbation
    (covector gaugeParameter : Covector4) : SymmetricPerturbation where
  tensor := fun first second =>
    covector first * gaugeParameter second +
      covector second * gaugeParameter first
  tensor_symmetric := by
    ext first second
    simp [Matrix.transpose_apply]
    ring

@[simp]
theorem pureGaugePerturbation_apply
    (covector gaugeParameter : Covector4) (first second : Index4) :
    (pureGaugePerturbation covector gaugeParameter).tensor first second =
      covector first * gaugeParameter second +
        covector second * gaugeParameter first := by
  rfl

/-- The flat Einstein symbol annihilates every pure-gauge perturbation. -/
theorem linearizedEinsteinSymbol_pureGauge_eq_zero
    (covector gaugeParameter : Covector4) :
    linearizedEinsteinSymbol covector
        (pureGaugePerturbation covector gaugeParameter) = 0 := by
  ext first second
  fin_cases first <;> fin_cases second <;>
    simp [linearizedEinsteinSymbol, linearizedRicciSymbol,
      linearizedScalarCurvatureSymbol, doubleMomentumContraction,
      momentumContraction, minkowskiTrace, covectorSquare,
      pureGaugePerturbation, raiseCovector, minkowskiMetric, etaSign,
      sum_fin_four] <;>
    ring

end

end P0EFTJanusLinearizedEinsteinBianchiSymbol
end JanusFormal
