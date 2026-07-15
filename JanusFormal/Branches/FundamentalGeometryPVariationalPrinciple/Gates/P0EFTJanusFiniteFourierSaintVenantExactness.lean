import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusArbitraryFrequencySaintVenantExactness

/-!
# Finite-Fourier Saint-Venant exactness

This gate lifts the arbitrary nonzero-frequency Lorentz Gram--Saint-Venant
symbol sequence to a finite family of Fourier coefficients.  Compatibility,
potential reconstruction, and exactness are proved coefficient by coefficient.

The result is a finite-support coefficient model.  Every listed frequency is
assumed nonzero; the zero mode is excluded.  No continuum PDE solvability,
boundary condition, convergence, or infinite Fourier-series statement is
claimed.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFourierSaintVenantExactness

set_option autoImplicit false

noncomputable section

open P0EFTJanusArbitraryFrequencySaintVenantExactness

variable {Mode : Type*}

abbrev FrequencyFamily (Mode : Type*) := Mode -> Covector4
abbrev FourierPotential (Mode : Type*) := Mode -> Vector4
abbrev FourierMetricCoefficient (Mode : Type*) := Mode -> CovariantTwoTensor
abbrev FourierCurvatureCoefficient (Mode : Type*) :=
  Mode -> CovariantFourTensor

/-- Lorentzian Gram symbol applied independently at every Fourier mode. -/
def finiteFourierLorentzGram
    (frequency : FrequencyFamily Mode) (potential : FourierPotential Mode) :
    FourierMetricCoefficient Mode :=
  fun mode => lorentzGramSymbol (frequency mode) (potential mode)

/-- Saint-Venant compatibility symbol applied independently at every mode. -/
def finiteFourierSaintVenant
    (frequency : FrequencyFamily Mode)
    (tensor : FourierMetricCoefficient Mode) :
    FourierCurvatureCoefficient Mode :=
  fun mode => saintVenantSymbol (frequency mode) (tensor mode)

/-- Every coefficient family on the finite mode set has finite support. -/
def coefficientSupport {Coefficient : Type*} [Zero Coefficient]
    (coefficient : Mode -> Coefficient) : Set Mode :=
  Function.support coefficient

theorem coefficientSupport_finite
    [Fintype Mode] {Coefficient : Type*} [Zero Coefficient]
    (coefficient : Mode -> Coefficient) :
    (coefficientSupport coefficient).Finite := by
  exact Set.toFinite _

/-- The finite Fourier sequence is a complex. -/
theorem finiteFourierSaintVenant_finiteFourierLorentzGram_eq_zero
    (frequency : FrequencyFamily Mode) (potential : FourierPotential Mode) :
    finiteFourierSaintVenant frequency
      (finiteFourierLorentzGram frequency potential) = 0 := by
  funext mode
  exact saintVenantSymbol_lorentzGramSymbol_eq_zero
    (frequency mode) (potential mode)

/-- A nonzero coordinate pivot chosen independently for every nonzero mode. -/
def frequencyPivot
    (frequency : FrequencyFamily Mode)
    (hNonzero : forall mode : Mode, frequency mode ≠ 0)
    (mode : Mode) : Index4 :=
  Classical.choose (exists_nonzero_pivot (frequency mode) (hNonzero mode))

theorem frequencyPivot_nonzero
    (frequency : FrequencyFamily Mode)
    (hNonzero : forall mode : Mode, frequency mode ≠ 0)
    (mode : Mode) :
    frequency mode (frequencyPivot frequency hNonzero mode) ≠ 0 :=
  Classical.choose_spec
    (exists_nonzero_pivot (frequency mode) (hNonzero mode))

/-- Explicit coefficientwise Lorentz potential reconstructed from a compatible
metric coefficient family. -/
def reconstructedFourierPotential
    (frequency : FrequencyFamily Mode)
    (hNonzero : forall mode : Mode, frequency mode ≠ 0)
    (tensor : FourierMetricCoefficient Mode) : FourierPotential Mode :=
  fun mode =>
    lorentzLower
      (reconstructedVariation
        (frequency mode) (frequencyPivot frequency hNonzero mode) (tensor mode))

theorem reconstructedFourierPotential_support_finite
    [Fintype Mode] (frequency : FrequencyFamily Mode)
    (hNonzero : forall mode : Mode, frequency mode ≠ 0)
    (tensor : FourierMetricCoefficient Mode) :
    (coefficientSupport
      (reconstructedFourierPotential frequency hNonzero tensor)).Finite :=
  coefficientSupport_finite _

/-- Coefficientwise compatibility reconstructs the original finite Fourier
metric family exactly. -/
theorem finiteFourierLorentzGram_reconstructed_eq
    (frequency : FrequencyFamily Mode)
    (hNonzero : forall mode : Mode, frequency mode ≠ 0)
    (tensor : FourierMetricCoefficient Mode)
    (hSymmetric : forall mode : Mode, (tensor mode).transpose = tensor mode)
    (hCompatible : finiteFourierSaintVenant frequency tensor = 0) :
    finiteFourierLorentzGram frequency
      (reconstructedFourierPotential frequency hNonzero tensor) = tensor := by
  funext mode
  have hModeCompatible :
      saintVenantSymbol (frequency mode) (tensor mode) = 0 := by
    exact congrFun hCompatible mode
  have hReconstruction :=
    tensor_eq_strainSymbol_reconstructed_of_pivot
      (frequency mode) (frequencyPivot frequency hNonzero mode)
      (frequencyPivot_nonzero frequency hNonzero mode)
      (tensor mode) (hSymmetric mode) hModeCompatible
  simpa [finiteFourierLorentzGram, reconstructedFourierPotential,
    lorentzGramSymbol] using hReconstruction.symm

theorem finiteFourierLorentzGram_injective
    (frequency : FrequencyFamily Mode)
    (hNonzero : forall mode : Mode, frequency mode ≠ 0) :
    Function.Injective (finiteFourierLorentzGram frequency) := by
  intro first second hEqual
  funext mode
  apply lorentzGramSymbol_injective (frequency mode) (hNonzero mode)
  exact congrFun hEqual mode

theorem finiteFourierSaintVenant_eq_zero_iff_exists_potential
    (frequency : FrequencyFamily Mode)
    (hNonzero : forall mode : Mode, frequency mode ≠ 0)
    (tensor : FourierMetricCoefficient Mode)
    (hSymmetric : forall mode : Mode, (tensor mode).transpose = tensor mode) :
    finiteFourierSaintVenant frequency tensor = 0 <->
      Exists fun potential : FourierPotential Mode =>
        tensor = finiteFourierLorentzGram frequency potential := by
  constructor
  · intro hCompatible
    refine Exists.intro
      (reconstructedFourierPotential frequency hNonzero tensor) ?_
    exact (finiteFourierLorentzGram_reconstructed_eq
      frequency hNonzero tensor hSymmetric hCompatible).symm
  · rintro ⟨potential, rfl⟩
    exact finiteFourierSaintVenant_finiteFourierLorentzGram_eq_zero
      frequency potential

/-- Equality of the finite Fourier Lorentz-Gram image with the symmetric
coefficientwise Saint-Venant kernel. -/
theorem range_finiteFourierLorentzGram_eq_symmetric_saintVenant_kernel
    (frequency : FrequencyFamily Mode)
    (hNonzero : forall mode : Mode, frequency mode ≠ 0) :
    Set.range (finiteFourierLorentzGram frequency) =
      {tensor : FourierMetricCoefficient Mode |
        (forall mode : Mode, (tensor mode).transpose = tensor mode) /\
          finiteFourierSaintVenant frequency tensor = 0} := by
  ext tensor
  constructor
  · rintro ⟨potential, rfl⟩
    constructor
    · intro mode
      exact strainSymbol_symmetric
        (frequency mode) (lorentzLower (potential mode))
    · exact finiteFourierSaintVenant_finiteFourierLorentzGram_eq_zero
        frequency potential
  · rintro ⟨hSymmetric, hCompatible⟩
    refine ⟨reconstructedFourierPotential frequency hNonzero tensor, ?_⟩
    exact finiteFourierLorentzGram_reconstructed_eq
      frequency hNonzero tensor hSymmetric hCompatible

/-- Combined finite-support Fourier exactness certificate. -/
theorem finite_fourier_saintVenant_sequence_exact
    (frequency : FrequencyFamily Mode)
    (hNonzero : forall mode : Mode, frequency mode ≠ 0) :
    Function.Injective (finiteFourierLorentzGram frequency) /\
      Set.range (finiteFourierLorentzGram frequency) =
        {tensor : FourierMetricCoefficient Mode |
          (forall mode : Mode, (tensor mode).transpose = tensor mode) /\
            finiteFourierSaintVenant frequency tensor = 0} := by
  exact ⟨finiteFourierLorentzGram_injective frequency hNonzero,
    range_finiteFourierLorentzGram_eq_symmetric_saintVenant_kernel
      frequency hNonzero⟩

/-- The global finite-coefficient gate: exactness together with finite support
of every potential and metric coefficient family on the chosen mode set. -/
theorem finite_fourier_saintVenant_exactness_gate
    [Fintype Mode]
    (frequency : FrequencyFamily Mode)
    (hNonzero : forall mode : Mode, frequency mode ≠ 0) :
    (Function.Injective (finiteFourierLorentzGram frequency) /\
      Set.range (finiteFourierLorentzGram frequency) =
        {tensor : FourierMetricCoefficient Mode |
          (forall mode : Mode, (tensor mode).transpose = tensor mode) /\
            finiteFourierSaintVenant frequency tensor = 0}) /\
      (forall potential : FourierPotential Mode,
        (coefficientSupport potential).Finite) /\
      (forall tensor : FourierMetricCoefficient Mode,
        (coefficientSupport tensor).Finite) := by
  exact ⟨finite_fourier_saintVenant_sequence_exact frequency hNonzero,
    fun potential => coefficientSupport_finite potential,
    fun tensor => coefficientSupport_finite tensor⟩

end

end P0EFTJanusFiniteFourierSaintVenantExactness
end JanusFormal
