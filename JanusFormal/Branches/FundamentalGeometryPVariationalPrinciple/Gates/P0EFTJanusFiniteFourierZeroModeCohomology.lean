import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFourierSaintVenantExactness

/-!
# Finite-Fourier zero-mode cohomology

This gate allows zero frequencies in a finite Fourier family.  Every symmetric
Saint-Venant-compatible coefficient family splits uniquely as a Lorentz-Gram
image whose potential vanishes at zero frequency plus a symmetric residual
supported exactly on the zero-frequency modes.

The residual is the complete obstruction to exactness in this finite
coefficient model.  No continuum PDE solvability, Fourier convergence,
boundary condition, or infinite-series statement is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusFiniteFourierZeroModeCohomology

set_option autoImplicit false

noncomputable section

open P0EFTJanusArbitraryFrequencySaintVenantExactness
open P0EFTJanusFiniteFourierSaintVenantExactness

variable {Mode : Type*}

/-- The set of modes at which the listed frequency vanishes. -/
def zeroModes (frequency : FrequencyFamily Mode) : Set Mode :=
  {mode | frequency mode = 0}

/-- A potential normalized to zero at every zero-frequency mode. -/
def VanishesOnZeroModes
    (frequency : FrequencyFamily Mode) (potential : FourierPotential Mode) :
    Prop :=
  forall mode, frequency mode = 0 -> potential mode = 0

/-- A coefficient family supported only at zero-frequency modes. -/
def SupportedOnZeroModes
    (frequency : FrequencyFamily Mode)
    (tensor : FourierMetricCoefficient Mode) : Prop :=
  forall mode, frequency mode ≠ 0 -> tensor mode = 0

/-- Coefficientwise symmetry. -/
def SymmetricCoefficients (tensor : FourierMetricCoefficient Mode) : Prop :=
  forall mode, (tensor mode).transpose = tensor mode

@[simp]
theorem lorentzGramSymbol_zero_frequency (variation : Vector4) :
    lorentzGramSymbol 0 variation = 0 := by
  ext row column
  simp [lorentzGramSymbol, strainSymbol]

/-- The canonical projection onto the zero-frequency coefficients. -/
def zeroModeResidual
    (frequency : FrequencyFamily Mode)
    (tensor : FourierMetricCoefficient Mode) :
    FourierMetricCoefficient Mode :=
  fun mode => if frequency mode = 0 then tensor mode else 0

theorem zeroModeResidual_apply_of_zero
    (frequency : FrequencyFamily Mode)
    (tensor : FourierMetricCoefficient Mode) (mode : Mode)
    (hZero : frequency mode = 0) :
    zeroModeResidual frequency tensor mode = tensor mode := by
  simp [zeroModeResidual, hZero]

theorem zeroModeResidual_apply_of_nonzero
    (frequency : FrequencyFamily Mode)
    (tensor : FourierMetricCoefficient Mode) (mode : Mode)
    (hNonzero : frequency mode ≠ 0) :
    zeroModeResidual frequency tensor mode = 0 := by
  simp [zeroModeResidual, hNonzero]

theorem zeroModeResidual_supported
    (frequency : FrequencyFamily Mode)
    (tensor : FourierMetricCoefficient Mode) :
    SupportedOnZeroModes frequency (zeroModeResidual frequency tensor) := by
  intro mode hNonzero
  exact zeroModeResidual_apply_of_nonzero frequency tensor mode hNonzero

theorem zeroModeResidual_symmetric
    (frequency : FrequencyFamily Mode)
    (tensor : FourierMetricCoefficient Mode)
    (hSymmetric : SymmetricCoefficients tensor) :
    SymmetricCoefficients (zeroModeResidual frequency tensor) := by
  intro mode
  by_cases hZero : frequency mode = 0
  · simpa [zeroModeResidual, hZero] using hSymmetric mode
  · simp [zeroModeResidual, hZero]

theorem zeroModeResidual_eq_self_of_supported
    (frequency : FrequencyFamily Mode)
    (tensor : FourierMetricCoefficient Mode)
    (hSupported : SupportedOnZeroModes frequency tensor) :
    zeroModeResidual frequency tensor = tensor := by
  funext mode
  by_cases hZero : frequency mode = 0
  · simp [zeroModeResidual, hZero]
  · simp [zeroModeResidual, hZero, hSupported mode hZero]

theorem zeroModeResidual_idempotent
    (frequency : FrequencyFamily Mode)
    (tensor : FourierMetricCoefficient Mode) :
    zeroModeResidual frequency (zeroModeResidual frequency tensor) =
      zeroModeResidual frequency tensor :=
  zeroModeResidual_eq_self_of_supported frequency _
    (zeroModeResidual_supported frequency tensor)

/-- A pivot chosen only when the current mode has nonzero frequency. -/
def nonzeroModePivot
    (frequency : FrequencyFamily Mode) (mode : Mode)
    (hNonzero : frequency mode ≠ 0) : Index4 :=
  Classical.choose (exists_nonzero_pivot (frequency mode) hNonzero)

theorem nonzeroModePivot_ne_zero
    (frequency : FrequencyFamily Mode) (mode : Mode)
    (hNonzero : frequency mode ≠ 0) :
    frequency mode (nonzeroModePivot frequency mode hNonzero) ≠ 0 :=
  Classical.choose_spec (exists_nonzero_pivot (frequency mode) hNonzero)

/-- The canonical reconstructed potential, normalized to zero on zero modes. -/
def reconstructedNonzeroModePotential
    (frequency : FrequencyFamily Mode)
    (tensor : FourierMetricCoefficient Mode) : FourierPotential Mode :=
  fun mode =>
    if hNonzero : frequency mode ≠ 0 then
      lorentzLower
        (reconstructedVariation
          (frequency mode) (nonzeroModePivot frequency mode hNonzero)
          (tensor mode))
    else 0

theorem reconstructedNonzeroModePotential_vanishes
    (frequency : FrequencyFamily Mode)
    (tensor : FourierMetricCoefficient Mode) :
    VanishesOnZeroModes frequency
      (reconstructedNonzeroModePotential frequency tensor) := by
  intro mode hZero
  simp [reconstructedNonzeroModePotential, hZero]

theorem finiteFourierLorentzGram_symmetric
    (frequency : FrequencyFamily Mode) (potential : FourierPotential Mode) :
    SymmetricCoefficients
      (finiteFourierLorentzGram frequency potential) := by
  intro mode
  exact strainSymbol_symmetric
    (frequency mode) (lorentzLower (potential mode))

theorem finiteFourierSaintVenant_add
    (frequency : FrequencyFamily Mode)
    (first second : FourierMetricCoefficient Mode) :
    finiteFourierSaintVenant frequency (first + second) =
      finiteFourierSaintVenant frequency first +
        finiteFourierSaintVenant frequency second := by
  funext mode firstIndex secondIndex thirdIndex fourthIndex
  simp [finiteFourierSaintVenant, saintVenantSymbol]
  ring

theorem finiteFourierSaintVenant_eq_zero_of_supportedOnZeroModes
    (frequency : FrequencyFamily Mode)
    (tensor : FourierMetricCoefficient Mode)
    (hSupported : SupportedOnZeroModes frequency tensor) :
    finiteFourierSaintVenant frequency tensor = 0 := by
  funext mode firstIndex secondIndex thirdIndex fourthIndex
  by_cases hZero : frequency mode = 0
  · simp [finiteFourierSaintVenant, saintVenantSymbol, hZero]
  · simp [finiteFourierSaintVenant, saintVenantSymbol,
      hSupported mode hZero]

/-- Every symmetric compatible family splits into a reconstructed nonzero-mode
Gram image and its zero-mode residual. -/
theorem finiteFourier_zeroMode_decomposition
    (frequency : FrequencyFamily Mode)
    (tensor : FourierMetricCoefficient Mode)
    (hSymmetric : SymmetricCoefficients tensor)
    (hCompatible : finiteFourierSaintVenant frequency tensor = 0) :
    tensor =
      finiteFourierLorentzGram frequency
          (reconstructedNonzeroModePotential frequency tensor) +
        zeroModeResidual frequency tensor := by
  funext mode
  by_cases hZero : frequency mode = 0
  · simp [finiteFourierLorentzGram, reconstructedNonzeroModePotential,
      zeroModeResidual, hZero]
  · have hModeCompatible :
        saintVenantSymbol (frequency mode) (tensor mode) = 0 := by
      exact congrFun hCompatible mode
    have hReconstruction :=
      tensor_eq_strainSymbol_reconstructed_of_pivot
        (frequency mode) (nonzeroModePivot frequency mode hZero)
        (nonzeroModePivot_ne_zero frequency mode hZero)
        (tensor mode) (hSymmetric mode) hModeCompatible
    simpa [finiteFourierLorentzGram,
      reconstructedNonzeroModePotential, zeroModeResidual, hZero,
      lorentzGramSymbol] using hReconstruction

/-- Conversely, a symmetric zero-mode residual added to a Gram image is
symmetric and Saint-Venant compatible. -/
theorem finiteFourier_zeroMode_decomposition_converse
    (frequency : FrequencyFamily Mode)
    (potential : FourierPotential Mode)
    (residual : FourierMetricCoefficient Mode)
    (hResidualSymmetric : SymmetricCoefficients residual)
    (hResidualSupported : SupportedOnZeroModes frequency residual) :
    SymmetricCoefficients
        (finiteFourierLorentzGram frequency potential + residual) /\
      finiteFourierSaintVenant frequency
          (finiteFourierLorentzGram frequency potential + residual) = 0 := by
  constructor
  · intro mode
    simp only [Pi.add_apply, Matrix.transpose_add]
    rw [finiteFourierLorentzGram_symmetric frequency potential mode,
      hResidualSymmetric mode]
  · rw [finiteFourierSaintVenant_add,
      finiteFourierSaintVenant_finiteFourierLorentzGram_eq_zero]
    simp [finiteFourierSaintVenant_eq_zero_of_supportedOnZeroModes
      frequency residual hResidualSupported]

/-- Gram is injective after fixing the otherwise invisible zero-mode values of
the potential to zero. -/
theorem finiteFourierLorentzGram_injective_on_normalized_potentials
    (frequency : FrequencyFamily Mode)
    (first second : FourierPotential Mode)
    (hFirst : VanishesOnZeroModes frequency first)
    (hSecond : VanishesOnZeroModes frequency second)
    (hGram : finiteFourierLorentzGram frequency first =
      finiteFourierLorentzGram frequency second) :
    first = second := by
  funext mode
  by_cases hZero : frequency mode = 0
  · rw [hFirst mode hZero, hSecond mode hZero]
  · apply lorentzGramSymbol_injective (frequency mode) hZero
    exact congrFun hGram mode

/-- Both normalized potential and zero-mode residual are unique. -/
theorem finiteFourier_zeroMode_decomposition_unique
    (frequency : FrequencyFamily Mode)
    (tensor : FourierMetricCoefficient Mode)
    (firstPotential secondPotential : FourierPotential Mode)
    (firstResidual secondResidual : FourierMetricCoefficient Mode)
    (hFirstPotential : VanishesOnZeroModes frequency firstPotential)
    (hSecondPotential : VanishesOnZeroModes frequency secondPotential)
    (hFirstResidual : SupportedOnZeroModes frequency firstResidual)
    (hSecondResidual : SupportedOnZeroModes frequency secondResidual)
    (hFirstDecomposition : tensor =
      finiteFourierLorentzGram frequency firstPotential + firstResidual)
    (hSecondDecomposition : tensor =
      finiteFourierLorentzGram frequency secondPotential + secondResidual) :
    firstPotential = secondPotential /\ firstResidual = secondResidual := by
  have hPotential : firstPotential = secondPotential := by
    funext mode
    by_cases hZero : frequency mode = 0
    · rw [hFirstPotential mode hZero, hSecondPotential mode hZero]
    · apply lorentzGramSymbol_injective (frequency mode) hZero
      have hFirst := congrFun hFirstDecomposition mode
      have hSecond := congrFun hSecondDecomposition mode
      simp [finiteFourierLorentzGram, hFirstResidual mode hZero] at hFirst
      simp [finiteFourierLorentzGram, hSecondResidual mode hZero] at hSecond
      exact hFirst.symm.trans hSecond
  have hResidual : firstResidual = secondResidual := by
    funext mode
    by_cases hZero : frequency mode = 0
    · have hFirst := congrFun hFirstDecomposition mode
      have hSecond := congrFun hSecondDecomposition mode
      simp [finiteFourierLorentzGram, hZero]
        at hFirst hSecond
      exact hFirst.symm.trans hSecond
    · rw [hFirstResidual mode hZero, hSecondResidual mode hZero]
  exact And.intro hPotential hResidual

/-- Exact existence and uniqueness of the normalized decomposition. -/
theorem compatible_iff_existsUnique_zeroMode_decomposition
    (frequency : FrequencyFamily Mode)
    (tensor : FourierMetricCoefficient Mode)
    (hSymmetric : SymmetricCoefficients tensor) :
    finiteFourierSaintVenant frequency tensor = 0 <->
      ExistsUnique fun decomposition :
          FourierPotential Mode × FourierMetricCoefficient Mode =>
        VanishesOnZeroModes frequency decomposition.1 /\
          SymmetricCoefficients decomposition.2 /\
          SupportedOnZeroModes frequency decomposition.2 /\
          tensor = finiteFourierLorentzGram frequency decomposition.1 +
            decomposition.2 := by
  constructor
  · intro hCompatible
    let potential := reconstructedNonzeroModePotential frequency tensor
    let residual := zeroModeResidual frequency tensor
    refine ExistsUnique.intro (potential, residual) ?_ ?_
    · exact And.intro
        (reconstructedNonzeroModePotential_vanishes frequency tensor)
        (And.intro (zeroModeResidual_symmetric frequency tensor hSymmetric)
          (And.intro (zeroModeResidual_supported frequency tensor)
            (finiteFourier_zeroMode_decomposition frequency tensor hSymmetric
              hCompatible)))
    · rintro ⟨otherPotential, otherResidual⟩
      rintro ⟨hOtherPotential, _hOtherSymmetric, hOtherResidual,
        hOtherDecomposition⟩
      have hUnique := finiteFourier_zeroMode_decomposition_unique
        frequency tensor potential otherPotential residual otherResidual
        (reconstructedNonzeroModePotential_vanishes frequency tensor)
        hOtherPotential (zeroModeResidual_supported frequency tensor)
        hOtherResidual
        (finiteFourier_zeroMode_decomposition frequency tensor hSymmetric
          hCompatible)
        hOtherDecomposition
      exact (Prod.ext hUnique.1 hUnique.2).symm
  · rintro ⟨⟨potential, residual⟩, _hCandidate, _hUnique⟩
    rw [_hCandidate.2.2.2]
    exact (finiteFourier_zeroMode_decomposition_converse frequency
      potential residual _hCandidate.2.1 _hCandidate.2.2.1).2

/-- The zero-mode projection kills every Lorentz-Gram family. -/
theorem zeroModeResidual_finiteFourierLorentzGram_eq_zero
    (frequency : FrequencyFamily Mode) (potential : FourierPotential Mode) :
    zeroModeResidual frequency
      (finiteFourierLorentzGram frequency potential) = 0 := by
  funext mode
  by_cases hZero : frequency mode = 0
  · simp [zeroModeResidual, finiteFourierLorentzGram, hZero]
  · simp [zeroModeResidual, hZero]

/-- Kernel/image characterization: among symmetric compatible coefficients,
zero residual is equivalent to exactness by a normalized potential. -/
theorem zeroModeResidual_eq_zero_iff_exists_normalized_potential
    (frequency : FrequencyFamily Mode)
    (tensor : FourierMetricCoefficient Mode)
    (hSymmetric : SymmetricCoefficients tensor)
    (hCompatible : finiteFourierSaintVenant frequency tensor = 0) :
    zeroModeResidual frequency tensor = 0 <->
      Exists fun potential : FourierPotential Mode =>
        VanishesOnZeroModes frequency potential /\
          tensor = finiteFourierLorentzGram frequency potential := by
  constructor
  · intro hResidual
    refine ⟨reconstructedNonzeroModePotential frequency tensor,
      reconstructedNonzeroModePotential_vanishes frequency tensor, ?_⟩
    have hDecomposition := finiteFourier_zeroMode_decomposition
      frequency tensor hSymmetric hCompatible
    simpa [hResidual] using hDecomposition
  · rintro ⟨potential, _hNormalized, rfl⟩
    exact zeroModeResidual_finiteFourierLorentzGram_eq_zero
      frequency potential

/-- Complete finite cohomology certificate: compatible coefficients are a
unique normalized Gram image plus a symmetric zero-mode representative. -/
theorem finite_fourier_zeroMode_cohomology_gate
    [Fintype Mode] (frequency : FrequencyFamily Mode) :
    (forall tensor : FourierMetricCoefficient Mode,
      SymmetricCoefficients tensor ->
      finiteFourierSaintVenant frequency tensor = 0 ->
      ExistsUnique fun decomposition :
          FourierPotential Mode × FourierMetricCoefficient Mode =>
        VanishesOnZeroModes frequency decomposition.1 /\
          SymmetricCoefficients decomposition.2 /\
          SupportedOnZeroModes frequency decomposition.2 /\
          tensor = finiteFourierLorentzGram frequency decomposition.1 +
            decomposition.2) /\
      (forall tensor : FourierMetricCoefficient Mode,
        (coefficientSupport tensor).Finite) := by
  constructor
  · intro tensor hSymmetric hCompatible
    exact (compatible_iff_existsUnique_zeroMode_decomposition
      frequency tensor hSymmetric).mp hCompatible
  · exact fun tensor => coefficientSupport_finite tensor

end

end P0EFTJanusFiniteFourierZeroModeCohomology
end JanusFormal
