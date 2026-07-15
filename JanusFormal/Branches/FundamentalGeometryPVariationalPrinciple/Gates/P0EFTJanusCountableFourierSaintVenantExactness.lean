import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFourierZeroModeCohomology

/-!
# Countable axial-Fourier Saint-Venant exactness

This gate upgrades the finite coefficient models to the countable mode set
`Z`.  The explicit axial frequency is `xi_n = n e_1`.  Away from `n = 0`,
compatible symmetric metric coefficients are reconstructed coefficientwise.
The inverse multiplier is uniformly bounded by one, so coordinatewise square
summability of the metric coefficients is preserved by reconstruction.

At `n = 0` the Gram symbol vanishes.  The remaining coefficient is isolated
as an explicit zero-mode residual.  Thus exactness holds on the compatible
subspace with zero residual.  This is a controlled countable Fourier model,
not a global PDE, convergence of differentiated Fourier series, or a boundary
solvability theorem.
-/

namespace JanusFormal
namespace P0EFTJanusCountableFourierSaintVenantExactness

set_option autoImplicit false

noncomputable section

open P0EFTJanusArbitraryFrequencySaintVenantExactness
open P0EFTJanusFiniteFourierSaintVenantExactness

abbrev CountablePotential := ℤ → Vector4
abbrev CountableMetricCoefficient := ℤ → CovariantTwoTensor
abbrev CountableCurvatureCoefficient := ℤ → CovariantFourTensor

/-- The axial integer Fourier frequency `n e_1`. -/
def axialFrequency (mode : ℤ) : Covector4 :=
  fun index => if index = 1 then (mode : ℝ) else 0

@[simp]
theorem axialFrequency_zero : axialFrequency 0 = 0 := by
  funext index
  simp [axialFrequency]

@[simp]
theorem axialFrequency_pivot (mode : ℤ) :
    axialFrequency mode 1 = (mode : ℝ) := by
  simp [axialFrequency]

theorem axialFrequency_ne_zero {mode : ℤ} (hMode : mode ≠ 0) :
    axialFrequency mode ≠ 0 := by
  intro hZero
  have hEntry := congrFun hZero 1
  simp [axialFrequency] at hEntry
  exact hMode (Int.cast_injective hEntry)

theorem axialFrequency_pivot_ne_zero {mode : ℤ} (hMode : mode ≠ 0) :
    axialFrequency mode 1 ≠ 0 := by
  simpa [axialFrequency] using (Int.cast_ne_zero.mpr hMode : (mode : ℝ) ≠ 0)

/-- Lorentz-Gram and Saint-Venant symbols on all integer modes. -/
def countableLorentzGram (potential : CountablePotential) :
    CountableMetricCoefficient :=
  finiteFourierLorentzGram axialFrequency potential

def countableSaintVenant (tensor : CountableMetricCoefficient) :
    CountableCurvatureCoefficient :=
  finiteFourierSaintVenant axialFrequency tensor

def SymmetricCoefficients (tensor : CountableMetricCoefficient) : Prop :=
  ∀ mode, (tensor mode).transpose = tensor mode

def VanishesAtZero (potential : CountablePotential) : Prop :=
  potential 0 = 0

/-- The complete zero-frequency obstruction in this axial family. -/
def zeroModeResidual (tensor : CountableMetricCoefficient) :
    CountableMetricCoefficient :=
  fun mode => if mode = 0 then tensor mode else 0

@[simp]
theorem zeroModeResidual_zero (tensor : CountableMetricCoefficient) :
    zeroModeResidual tensor 0 = tensor 0 := by
  simp [zeroModeResidual]

theorem zeroModeResidual_nonzero (tensor : CountableMetricCoefficient)
    {mode : ℤ} (_hMode : mode ≠ 0) :
    zeroModeResidual tensor mode = 0 := by
  simp [zeroModeResidual, _hMode]

/-- Explicit potential reconstructed using the fixed nonzero pivot `1`. -/
def axialReconstructedPotential (tensor : CountableMetricCoefficient) :
    CountablePotential :=
  fun mode =>
    if mode ≠ 0 then
      lorentzLower
        (reconstructedVariation (axialFrequency mode) 1 (tensor mode))
    else 0

@[simp]
theorem axialReconstructedPotential_zero
    (tensor : CountableMetricCoefficient) :
    axialReconstructedPotential tensor 0 = 0 := by
  simp [axialReconstructedPotential]

theorem axialReconstructedPotential_vanishesAtZero
    (tensor : CountableMetricCoefficient) :
    VanishesAtZero (axialReconstructedPotential tensor) :=
  axialReconstructedPotential_zero tensor

theorem countableSaintVenant_countableLorentzGram_eq_zero
    (potential : CountablePotential) :
    countableSaintVenant (countableLorentzGram potential) = 0 :=
  finiteFourierSaintVenant_finiteFourierLorentzGram_eq_zero
    axialFrequency potential

/-- Compatible coefficients split into their reconstructed nonzero modes and
the sole zero-mode obstruction. -/
theorem countable_zeroMode_decomposition
    (tensor : CountableMetricCoefficient)
    (hSymmetric : SymmetricCoefficients tensor)
    (hCompatible : countableSaintVenant tensor = 0) :
    tensor = countableLorentzGram (axialReconstructedPotential tensor) +
      zeroModeResidual tensor := by
  funext mode
  by_cases hMode : mode = 0
  · subst mode
    simp [countableLorentzGram, finiteFourierLorentzGram,
      zeroModeResidual]
  · have hKernel : saintVenantSymbol (axialFrequency mode) (tensor mode) = 0 := by
      exact congrFun hCompatible mode
    have hReconstruction :=
      tensor_eq_strainSymbol_reconstructed_of_pivot
        (axialFrequency mode) 1 (axialFrequency_pivot_ne_zero hMode)
        (tensor mode) (hSymmetric mode) hKernel
    simpa [countableLorentzGram, finiteFourierLorentzGram,
      axialReconstructedPotential, zeroModeResidual, hMode,
      lorentzGramSymbol] using hReconstruction

/-- Exactness on compatible coefficients with vanishing zero mode. -/
theorem compatible_zeroModeFree_iff_exists_normalizedPotential
    (tensor : CountableMetricCoefficient)
    (hSymmetric : SymmetricCoefficients tensor) :
    countableSaintVenant tensor = 0 ∧ zeroModeResidual tensor = 0 ↔
      ∃ potential : CountablePotential,
        VanishesAtZero potential ∧ tensor = countableLorentzGram potential := by
  constructor
  · rintro ⟨hCompatible, hResidual⟩
    refine ⟨axialReconstructedPotential tensor,
      axialReconstructedPotential_vanishesAtZero tensor, ?_⟩
    simpa [hResidual] using
      countable_zeroMode_decomposition tensor hSymmetric hCompatible
  · rintro ⟨potential, _hPotentialZero, rfl⟩
    constructor
    · exact countableSaintVenant_countableLorentzGram_eq_zero potential
    · funext mode
      by_cases hMode : mode = 0
      · subst mode
        simp [zeroModeResidual, countableLorentzGram,
          finiteFourierLorentzGram]
      · simp [zeroModeResidual, hMode]

/-- Coordinatewise square summability, equivalent to finite-dimensional
coefficientwise `ell^2` control for the present purposes. -/
def PotentialSquareSummable (potential : CountablePotential) : Prop :=
  ∀ index, Summable fun mode : ℤ => (potential mode index) ^ 2

def MetricSquareSummable (tensor : CountableMetricCoefficient) : Prop :=
  ∀ row column, Summable fun mode : ℤ => (tensor mode row column) ^ 2

theorem one_le_sq_intCast {mode : ℤ} (hMode : mode ≠ 0) :
    (1 : ℝ) ≤ (mode : ℝ) ^ 2 := by
  have hAbsInt : (1 : ℤ) ≤ |mode| := Int.one_le_abs hMode
  have hAbsReal : (1 : ℝ) ≤ |(mode : ℝ)| := by
    exact_mod_cast hAbsInt
  nlinarith [sq_abs (mode : ℝ)]

theorem div_intCast_sq_le_sq (value : ℝ) {mode : ℤ} (hMode : mode ≠ 0) :
    (value / (mode : ℝ)) ^ 2 ≤ value ^ 2 := by
  have hCast : (mode : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hMode
  have hModeSqPos : 0 < (mode : ℝ) ^ 2 := sq_pos_of_ne_zero hCast
  rw [div_pow]
  apply (div_le_iff₀ hModeSqPos).2
  have hProduct := mul_nonneg (sq_nonneg value)
    (sub_nonneg.mpr (one_le_sq_intCast hMode))
  nlinarith

theorem half_div_intCast_sq_le_sq
    (value : ℝ) {mode : ℤ} (hMode : mode ≠ 0) :
    (value / (2 * (mode : ℝ))) ^ 2 ≤ value ^ 2 := by
  have hCast : (mode : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hMode
  have hDenominator : (2 * (mode : ℝ)) ≠ 0 := mul_ne_zero (by norm_num) hCast
  have hDenominatorSqPos : 0 < (2 * (mode : ℝ)) ^ 2 :=
    sq_pos_of_ne_zero hDenominator
  rw [div_pow]
  apply (div_le_iff₀ hDenominatorSqPos).2
  have hModeSq := one_le_sq_intCast hMode
  have hProduct := mul_nonneg (sq_nonneg value)
    (show 0 ≤ (2 * (mode : ℝ)) ^ 2 - 1 by nlinarith)
  nlinarith

/-- Uniform norm-one coordinate bound for the inverse Fourier multiplier. -/
theorem axialReconstructedPotential_sq_le
    (tensor : CountableMetricCoefficient) (mode : ℤ) (index : Index4) :
    (axialReconstructedPotential tensor mode index) ^ 2 ≤
      (tensor mode 1 index) ^ 2 := by
  by_cases hMode : mode = 0
  · subst mode
    have hZero := congrFun (axialReconstructedPotential_zero tensor) index
    rw [hZero]
    simpa using sq_nonneg (tensor 0 1 index)
  · have hCast : (mode : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hMode
    fin_cases index
    · simpa [axialReconstructedPotential, hMode, lorentzLower, lorentzSign,
        reconstructedVariation, axialFrequency] using
        div_intCast_sq_le_sq (tensor mode 1 0) hMode
    · have hFormula :
          axialReconstructedPotential tensor mode 1 =
            tensor mode 1 1 / (2 * (mode : ℝ)) := by
        simp [axialReconstructedPotential, hMode, lorentzLower, lorentzSign,
          reconstructedVariation, axialFrequency]
        field_simp [hCast]
        ring
      change (axialReconstructedPotential tensor mode (1 : Index4)) ^ 2 ≤
        (tensor mode 1 (1 : Index4)) ^ 2
      rw [hFormula]
      exact half_div_intCast_sq_le_sq (tensor mode 1 1) hMode
    · simpa [axialReconstructedPotential, hMode, lorentzLower, lorentzSign,
        reconstructedVariation, axialFrequency] using
        div_intCast_sq_le_sq (tensor mode 1 2) hMode
    · simpa [axialReconstructedPotential, hMode, lorentzLower, lorentzSign,
        reconstructedVariation, axialFrequency] using
        div_intCast_sq_le_sq (tensor mode 1 3) hMode

/-- The coefficientwise reconstruction preserves square summability. -/
theorem axialReconstructedPotential_squareSummable
    (tensor : CountableMetricCoefficient)
    (hSummable : MetricSquareSummable tensor) :
    PotentialSquareSummable (axialReconstructedPotential tensor) := by
  intro index
  exact Summable.of_nonneg_of_le
    (fun mode => sq_nonneg (axialReconstructedPotential tensor mode index))
    (fun mode => axialReconstructedPotential_sq_le tensor mode index)
    (hSummable 1 index)

/-- The zero-mode residual is square summable without any hypothesis. -/
theorem zeroModeResidual_squareSummable
    (tensor : CountableMetricCoefficient) :
    MetricSquareSummable (zeroModeResidual tensor) := by
  intro row column
  apply summable_of_ne_finset_zero (s := {0})
  intro mode hMode
  simp only [Finset.mem_singleton] at hMode
  simp [zeroModeResidual, hMode]

/-- Countable controlled exactness certificate, including the zero-mode
residual and `ell^2` preservation of the explicit reconstruction. -/
theorem countable_fourier_saintVenant_exactness_gate :
    (∀ tensor : CountableMetricCoefficient,
      SymmetricCoefficients tensor → countableSaintVenant tensor = 0 →
      tensor = countableLorentzGram (axialReconstructedPotential tensor) +
        zeroModeResidual tensor) ∧
    (∀ tensor : CountableMetricCoefficient,
      MetricSquareSummable tensor →
      PotentialSquareSummable (axialReconstructedPotential tensor)) ∧
    (∀ tensor : CountableMetricCoefficient,
      SymmetricCoefficients tensor →
      (countableSaintVenant tensor = 0 ∧ zeroModeResidual tensor = 0 ↔
        ∃ potential : CountablePotential,
          VanishesAtZero potential ∧ tensor = countableLorentzGram potential)) := by
  exact ⟨countable_zeroMode_decomposition,
    axialReconstructedPotential_squareSummable,
    compatible_zeroModeFree_iff_exists_normalizedPotential⟩

end

end P0EFTJanusCountableFourierSaintVenantExactness
end JanusFormal
