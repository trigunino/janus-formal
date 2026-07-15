import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusReciprocalBimetricPotential

/-!
An explicit candidate for the two interaction densities left symbolic in M30.
On a real diagonalizable branch, the four entries are the positive eigenvalues
of `X = sqrt(g_plus^{-1} g_minus)`.  The two M30 density slots are defined as
half of the two reciprocal representations of one elementary-symmetric
bimetric potential.  Their sum therefore counts one common interaction, not
two independent interactions.

This file closes the algebraic four-eigenvalue formula and encodes the
candidate choice of matter independence.  It does not claim that M30 forces
that choice, nor construct metric variations, Hassan--Rosen constraints, or a
spacetime action integral.
-/

namespace JanusFormal
namespace P0EFTJanusExplicitReciprocalCrossDensities

set_option autoImplicit false

noncomputable section

open P0EFTJanusReciprocalBimetricPotential

/-- Ordered spectrum of a real four-dimensional square-root branch. -/
abbrev SquareRootSpectrum := Fin 4 → ℝ

/-- Every square-root eigenvalue is nonzero. -/
def SpectrumNonzero (spectrum : SquareRootSpectrum) : Prop :=
  ∀ i, spectrum i ≠ 0

/-- The physical positive square-root branch. -/
def SpectrumPositive (spectrum : SquareRootSpectrum) : Prop :=
  ∀ i, 0 < spectrum i

theorem spectrumPositive_implies_nonzero
    {spectrum : SquareRootSpectrum}
    (hPositive : SpectrumPositive spectrum) :
    SpectrumNonzero spectrum := by
  intro i
  exact ne_of_gt (hPositive i)

/-- Algebraic reciprocal spectrum.  Its physical `X⁻¹` interpretation is used
only through `NonzeroSquareRootSpectrum` below. -/
def inverseSpectrum (spectrum : SquareRootSpectrum) : SquareRootSpectrum :=
  fun i => (spectrum i)⁻¹

/-- Physical domain of the reciprocal M30 slots. -/
abbrev NonzeroSquareRootSpectrum :=
  { spectrum : SquareRootSpectrum // SpectrumNonzero spectrum }

def inverseNonzeroSpectrum
    (spectrum : NonzeroSquareRootSpectrum) : NonzeroSquareRootSpectrum :=
  ⟨inverseSpectrum spectrum.1, fun i => inv_ne_zero (spectrum.2 i)⟩

theorem inverseSpectrum_positive
    {spectrum : SquareRootSpectrum}
    (hPositive : SpectrumPositive spectrum) :
    SpectrumPositive (inverseSpectrum spectrum) := by
  intro i
  exact inv_pos.mpr (hPositive i)

@[simp]
theorem inverseNonzeroSpectrum_involution
    (spectrum : NonzeroSquareRootSpectrum) :
    inverseNonzeroSpectrum (inverseNonzeroSpectrum spectrum) = spectrum := by
  ext i
  simp [inverseNonzeroSpectrum, inverseSpectrum]

/-- Four-dimensional elementary symmetric polynomials of the spectrum. -/
def elementary0 (_spectrum : SquareRootSpectrum) : ℝ := 1

def elementary1 (spectrum : SquareRootSpectrum) : ℝ :=
  spectrum 0 + spectrum 1 + spectrum 2 + spectrum 3

def elementary2 (spectrum : SquareRootSpectrum) : ℝ :=
  spectrum 0 * spectrum 1 + spectrum 0 * spectrum 2 +
    spectrum 0 * spectrum 3 + spectrum 1 * spectrum 2 +
    spectrum 1 * spectrum 3 + spectrum 2 * spectrum 3

def elementary3 (spectrum : SquareRootSpectrum) : ℝ :=
  spectrum 0 * spectrum 1 * spectrum 2 +
    spectrum 0 * spectrum 1 * spectrum 3 +
    spectrum 0 * spectrum 2 * spectrum 3 +
    spectrum 1 * spectrum 2 * spectrum 3

def elementary4 (spectrum : SquareRootSpectrum) : ℝ :=
  spectrum 0 * spectrum 1 * spectrum 2 * spectrum 3

/-- `det X`, hence the positive-branch ratio `sqrt(|g_minus|/|g_plus|)`. -/
def volumeRatio (spectrum : SquareRootSpectrum) : ℝ :=
  elementary4 spectrum

theorem volumeRatio_positive
    {spectrum : SquareRootSpectrum}
    (hPositive : SpectrumPositive spectrum) :
    0 < volumeRatio spectrum := by
  unfold SpectrumPositive at hPositive
  unfold volumeRatio elementary4
  exact mul_pos (mul_pos (mul_pos (hPositive 0) (hPositive 1))
    (hPositive 2)) (hPositive 3)

/-- Full four-eigenvalue elementary-symmetric potential. -/
def spectralPotential
    (coefficients : PotentialCoefficients)
    (spectrum : SquareRootSpectrum) : ℝ :=
  coefficients.beta0 * elementary0 spectrum +
    coefficients.beta1 * elementary1 spectrum +
    coefficients.beta2 * elementary2 spectrum +
    coefficients.beta3 * elementary3 spectrum +
    coefficients.beta4 * elementary4 spectrum

/-- Equal eigenvalues recover the already audited proportional potential. -/
def proportionalSpectrum (c : ℝ) : SquareRootSpectrum :=
  fun _ => c

theorem spectralPotential_on_proportionalSpectrum
    (coefficients : PotentialCoefficients) (c : ℝ) :
    spectralPotential coefficients (proportionalSpectrum c) =
      proportionalPotential coefficients c := by
  unfold spectralPotential proportionalSpectrum proportionalPotential
    elementary0 elementary1 elementary2 elementary3 elementary4
  norm_num
  ring

theorem volumeRatio_mul_elementary0_inverse
    (spectrum : SquareRootSpectrum) :
    volumeRatio spectrum * elementary0 (inverseSpectrum spectrum) =
      elementary4 spectrum := by
  simp [volumeRatio, elementary0, elementary4]

theorem volumeRatio_mul_elementary1_inverse
    (spectrum : SquareRootSpectrum)
    (hNonzero : SpectrumNonzero spectrum) :
    volumeRatio spectrum * elementary1 (inverseSpectrum spectrum) =
      elementary3 spectrum := by
  unfold SpectrumNonzero at hNonzero
  unfold volumeRatio elementary4 elementary1 elementary3 inverseSpectrum
  field_simp [hNonzero 0, hNonzero 1, hNonzero 2, hNonzero 3]
  ring

theorem volumeRatio_mul_elementary2_inverse
    (spectrum : SquareRootSpectrum)
    (hNonzero : SpectrumNonzero spectrum) :
    volumeRatio spectrum * elementary2 (inverseSpectrum spectrum) =
      elementary2 spectrum := by
  unfold SpectrumNonzero at hNonzero
  unfold volumeRatio elementary4 elementary2 inverseSpectrum
  field_simp [hNonzero 0, hNonzero 1, hNonzero 2, hNonzero 3]
  ring

theorem volumeRatio_mul_elementary3_inverse
    (spectrum : SquareRootSpectrum)
    (hNonzero : SpectrumNonzero spectrum) :
    volumeRatio spectrum * elementary3 (inverseSpectrum spectrum) =
      elementary1 spectrum := by
  unfold SpectrumNonzero at hNonzero
  unfold volumeRatio elementary4 elementary3 elementary1 inverseSpectrum
  field_simp [hNonzero 0, hNonzero 1, hNonzero 2, hNonzero 3]
  ring

theorem volumeRatio_mul_elementary4_inverse
    (spectrum : SquareRootSpectrum)
    (hNonzero : SpectrumNonzero spectrum) :
    volumeRatio spectrum * elementary4 (inverseSpectrum spectrum) =
      elementary0 spectrum := by
  unfold SpectrumNonzero at hNonzero
  unfold volumeRatio elementary4 elementary0 inverseSpectrum
  field_simp [hNonzero 0, hNonzero 1, hNonzero 2, hNonzero 3]

/-- Full-spectrum reciprocal identity, beyond the proportional slice. -/
theorem spectralPotential_reciprocity
    (coefficients : PotentialCoefficients)
    (spectrum : SquareRootSpectrum)
    (hNonzero : SpectrumNonzero spectrum) :
    volumeRatio spectrum *
        spectralPotential (reversed coefficients) (inverseSpectrum spectrum) =
      spectralPotential coefficients spectrum := by
  have h0 := volumeRatio_mul_elementary0_inverse spectrum
  have h1 := volumeRatio_mul_elementary1_inverse spectrum hNonzero
  have h2 := volumeRatio_mul_elementary2_inverse spectrum hNonzero
  have h3 := volumeRatio_mul_elementary3_inverse spectrum hNonzero
  have h4 := volumeRatio_mul_elementary4_inverse spectrum hNonzero
  unfold spectralPotential reversed
  calc
    volumeRatio spectrum *
        (coefficients.beta4 * elementary0 (inverseSpectrum spectrum) +
          coefficients.beta3 * elementary1 (inverseSpectrum spectrum) +
          coefficients.beta2 * elementary2 (inverseSpectrum spectrum) +
          coefficients.beta1 * elementary3 (inverseSpectrum spectrum) +
          coefficients.beta0 * elementary4 (inverseSpectrum spectrum)) =
      coefficients.beta4 *
          (volumeRatio spectrum * elementary0 (inverseSpectrum spectrum)) +
        coefficients.beta3 *
          (volumeRatio spectrum * elementary1 (inverseSpectrum spectrum)) +
        coefficients.beta2 *
          (volumeRatio spectrum * elementary2 (inverseSpectrum spectrum)) +
        coefficients.beta1 *
          (volumeRatio spectrum * elementary3 (inverseSpectrum spectrum)) +
        coefficients.beta0 *
          (volumeRatio spectrum * elementary4 (inverseSpectrum spectrum)) := by
            ring
    _ = coefficients.beta4 * elementary4 spectrum +
        coefficients.beta3 * elementary3 spectrum +
        coefficients.beta2 * elementary2 spectrum +
        coefficients.beta1 * elementary1 spectrum +
        coefficients.beta0 * elementary0 spectrum := by
          rw [h0, h1, h2, h3, h4]
    _ = coefficients.beta0 * elementary0 spectrum +
        coefficients.beta1 * elementary1 spectrum +
        coefficients.beta2 * elementary2 spectrum +
        coefficients.beta3 * elementary3 spectrum +
        coefficients.beta4 * elementary4 spectrum := by
          ring

/-- A measure-free M30 interaction slot may syntactically receive both matter
sectors.  The spacetime volume measure is not included here. -/
abbrev CrossDensity (MatterPlus MatterMinus : Type*) :=
  NonzeroSquareRootSpectrum → MatterPlus → MatterMinus → ℝ

/-- First M30 density slot: half of the common pure-metric interaction. -/
def plusCrossDensity
    {MatterPlus MatterMinus : Type*}
    (interactionScale : ℝ)
    (coefficients : PotentialCoefficients) :
    CrossDensity MatterPlus MatterMinus :=
  fun spectrum _matterPlus _matterMinus =>
    -(interactionScale / 2) * spectralPotential coefficients spectrum.1

/-- Second M30 density slot: the reciprocal half under the second measure. -/
def minusCrossDensity
    {MatterPlus MatterMinus : Type*}
    (interactionScale : ℝ)
    (coefficients : PotentialCoefficients) :
    CrossDensity MatterPlus MatterMinus :=
  fun spectrum _matterPlus _matterMinus =>
    -(interactionScale / 2) *
      spectralPotential (reversed coefficients) (inverseSpectrum spectrum.1)

/-- The candidate makes the cross densities explicitly matter-independent;
matter remains in separate sector actions. -/
theorem crossDensities_matter_independent
    {MatterPlus MatterMinus : Type*}
    (interactionScale : ℝ)
    (coefficients : PotentialCoefficients)
    (spectrum : NonzeroSquareRootSpectrum)
    (plusA plusB : MatterPlus) (minusA minusB : MatterMinus) :
    plusCrossDensity interactionScale coefficients spectrum plusA minusA =
        plusCrossDensity interactionScale coefficients spectrum plusB minusB ∧
      minusCrossDensity interactionScale coefficients spectrum plusA minusA =
        minusCrossDensity interactionScale coefficients spectrum plusB minusB := by
  constructor <;> rfl

/-- The two density slots give equal weighted halves of one interaction. -/
theorem weighted_crossDensities_equal
    {MatterPlus MatterMinus : Type*}
    (interactionScale plusVolume : ℝ)
    (coefficients : PotentialCoefficients)
    (spectrum : NonzeroSquareRootSpectrum)
    (matterPlus : MatterPlus) (matterMinus : MatterMinus) :
    plusVolume *
        plusCrossDensity interactionScale coefficients spectrum
          matterPlus matterMinus =
      (plusVolume * volumeRatio spectrum.1) *
        minusCrossDensity interactionScale coefficients spectrum
          matterPlus matterMinus := by
  have hReciprocal :=
    spectralPotential_reciprocity coefficients spectrum.1 spectrum.2
  unfold plusCrossDensity minusCrossDensity
  calc
    plusVolume * (-(interactionScale / 2) *
        spectralPotential coefficients spectrum) =
      -(interactionScale / 2) * plusVolume *
        spectralPotential coefficients spectrum := by ring
    _ = -(interactionScale / 2) * plusVolume *
        (volumeRatio spectrum.1 *
          spectralPotential (reversed coefficients)
            (inverseSpectrum spectrum.1)) := by rw [hReciprocal]
    _ = (plusVolume * volumeRatio spectrum.1) *
        (-(interactionScale / 2) *
          spectralPotential (reversed coefficients)
            (inverseSpectrum spectrum.1)) := by ring

/-- One unsplit common interaction potential before the plus-sector measure. -/
def commonInteractionPotential
    (interactionScale : ℝ)
    (coefficients : PotentialCoefficients)
    (spectrum : SquareRootSpectrum) : ℝ :=
  -interactionScale * spectralPotential coefficients spectrum

/-- Exact no-double-counting theorem: the two weighted half-densities sum to
one common elementary-symmetric interaction. -/
theorem two_M30_density_slots_eq_one_common_interaction
    {MatterPlus MatterMinus : Type*}
    (interactionScale plusVolume : ℝ)
    (coefficients : PotentialCoefficients)
    (spectrum : NonzeroSquareRootSpectrum)
    (matterPlus : MatterPlus) (matterMinus : MatterMinus) :
    plusVolume *
          plusCrossDensity interactionScale coefficients spectrum
            matterPlus matterMinus +
        (plusVolume * volumeRatio spectrum.1) *
          minusCrossDensity interactionScale coefficients spectrum
            matterPlus matterMinus =
      plusVolume *
        commonInteractionPotential interactionScale coefficients spectrum.1 := by
  have hEqual := weighted_crossDensities_equal interactionScale plusVolume
    coefficients spectrum matterPlus matterMinus
  rw [← hEqual]
  unfold plusCrossDensity commonInteractionPotential
  ring

/-- PT-symmetric coefficients identify the second density with the first
density evaluated on the inverse square-root spectrum. -/
theorem pt_symmetric_minusDensity_eq_plusDensity_inverse
    {MatterPlus MatterMinus : Type*}
    (interactionScale : ℝ)
    (coefficients : PotentialCoefficients)
    (hPT : PTSymmetric coefficients)
    (spectrum : NonzeroSquareRootSpectrum)
    (matterPlus : MatterPlus) (matterMinus : MatterMinus) :
    minusCrossDensity interactionScale coefficients spectrum
        matterPlus matterMinus =
      plusCrossDensity interactionScale coefficients
        (inverseNonzeroSpectrum spectrum) matterPlus matterMinus := by
  have hFixed := pt_symmetric_coefficients_are_reversal_fixed coefficients hPT
  simp [minusCrossDensity, plusCrossDensity, inverseNonzeroSpectrum, hFixed]

end

end P0EFTJanusExplicitReciprocalCrossDensities
end JanusFormal
