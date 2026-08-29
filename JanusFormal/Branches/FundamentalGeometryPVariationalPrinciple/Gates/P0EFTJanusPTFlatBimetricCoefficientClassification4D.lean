import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPTFlatBimetricVariationalBridge

/-!
# Exact coefficient classification of the PT-flat bimetric interaction

For the four-dimensional elementary-symmetric potential, exchange symmetry
and vanishing at the symmetric proportional point are equivalent to the
existing two-parameter `ptFlatCoefficients` family.  Stationarity then follows
automatically.  Fixing the Fierz--Pauli mass leaves one genuine parameter,
even inside the positive cone.
-/

namespace JanusFormal
namespace P0EFTJanusPTFlatBimetricCoefficientClassification4D

set_option autoImplicit false

open P0EFTJanusReciprocalBimetricPotential
open P0EFTJanusPTSymmetricFlatBimetricBranch
open P0EFTJanusPTFlatBimetricVariationalBridge

/-- Exchange symmetry together with zero potential at the symmetric point. -/
def PTSymmetricFlat
    (coefficients : PotentialCoefficients) : Prop :=
  PTSymmetric coefficients ∧ proportionalPotential coefficients 1 = 0

/-- Converse to the existing construction: every PT-symmetric flat
coefficient package is exactly in the displayed two-parameter family. -/
theorem eq_ptFlatCoefficients_of_ptSymmetricFlat
    (coefficients : PotentialCoefficients)
    (hPT : PTSymmetric coefficients)
    (hFlat : proportionalPotential coefficients 1 = 0) :
    coefficients =
      ptFlatCoefficients coefficients.beta1 coefficients.beta2 := by
  rcases hPT with ⟨h04, h13⟩
  cases coefficients with
  | mk beta0 beta1 beta2 beta3 beta4 =>
      dsimp only at h04 h13
      dsimp [proportionalPotential] at hFlat
      subst beta4
      subst beta3
      dsimp [ptFlatCoefficients]
      congr <;> linarith

/-- Exact iff classification. -/
theorem ptSymmetricFlat_iff_eq_ptFlatCoefficients
    (coefficients : PotentialCoefficients) :
    PTSymmetricFlat coefficients ↔
      coefficients =
        ptFlatCoefficients coefficients.beta1 coefficients.beta2 := by
  constructor
  · intro h
    exact eq_ptFlatCoefficients_of_ptSymmetricFlat
      coefficients h.1 h.2
  · intro h
    rw [h]
    constructor
    · exact pt_flat_coefficients_are_symmetric _ _
    · simp [proportionalPotential, ptFlatCoefficients]
      ring

/-- The two parameters are unique, not merely witnesses. -/
theorem ptSymmetricFlat_unique_parameters
    (coefficients : PotentialCoefficients)
    (hFlat : PTSymmetricFlat coefficients) :
    ∃! parameters : ℝ × ℝ,
      coefficients =
        ptFlatCoefficients parameters.1 parameters.2 := by
  refine ⟨(coefficients.beta1, coefficients.beta2),
    (ptSymmetricFlat_iff_eq_ptFlatCoefficients coefficients).1 hFlat, ?_⟩
  intro parameters hParameters
  apply Prod.ext
  · have hBeta1 :=
      congrArg PotentialCoefficients.beta1 hParameters
    simpa [ptFlatCoefficients] using hBeta1.symm
  · have hBeta2 :=
      congrArg PotentialCoefficients.beta2 hParameters
    simpa [ptFlatCoefficients] using hBeta2.symm

/-- Flatness plus PT already imply stationarity of the positive-energy
convention at the symmetric point. -/
theorem ptSymmetricFlat_energy_stationary
    (coefficients : PotentialCoefficients)
    (hFlat : PTSymmetricFlat coefficients) :
    HasDerivAt (fun c => -proportionalPotential coefficients c) 0 1 := by
  rw [(ptSymmetricFlat_iff_eq_ptFlatCoefficients coefficients).1 hFlat]
  change HasDerivAt
    (proportionalInteractionEnergy coefficients.beta1 coefficients.beta2) 0 1
  exact
    proportionalInteractionEnergy_hasDerivAt_symmetric_point
      coefficients.beta1 coefficients.beta2

/-- The complete PT-flat family at a fixed Fierz--Pauli mass combination.
`total` is `beta1 + beta2`; `parameter` is the remaining coupling. -/
def fixedMassPTFlatFamily
    (total parameter : ℝ) : PotentialCoefficients :=
  ptFlatCoefficients parameter (total - parameter)

theorem fixedMassPTFlatFamily_is_ptSymmetricFlat
    (total parameter : ℝ) :
    PTSymmetricFlat (fixedMassPTFlatFamily total parameter) := by
  rw [ptSymmetricFlat_iff_eq_ptFlatCoefficients]
  rfl

/-- Every member has the same Fierz--Pauli mass combination. -/
@[simp]
theorem fixedMassPTFlatFamily_fpMassCombination
    (total parameter : ℝ) :
    fpMassCombination (fixedMassPTFlatFamily total parameter) =
      2 * total := by
  rw [fixedMassPTFlatFamily, pt_flat_fp_mass_combination]
  ring

/-- The residual parameter labels genuinely distinct coefficient packages. -/
theorem fixedMassPTFlatFamily_injective
    (total : ℝ) :
    Function.Injective (fixedMassPTFlatFamily total) := by
  intro first second hEqual
  have hBeta1 := congrArg PotentialCoefficients.beta1 hEqual
  simpa [fixedMassPTFlatFamily, ptFlatCoefficients] using hBeta1

/-- Explicit no-go inside the positive cone: PT, flatness, stationarity,
positive coefficients and one fixed Fierz--Pauli mass still do not determine
the interaction. -/
theorem pt_flat_positive_fixed_mass_not_unique :
    ∃ first second : PotentialCoefficients,
      PTSymmetricFlat first ∧
      PTSymmetricFlat second ∧
      HasDerivAt (fun c => -proportionalPotential first c) 0 1 ∧
      HasDerivAt (fun c => -proportionalPotential second c) 0 1 ∧
      fpMassCombination first = fpMassCombination second ∧
      (0 : ℝ) < first.beta1 ∧
      0 ≤ first.beta2 ∧
      (0 : ℝ) < second.beta1 ∧
      0 ≤ second.beta2 ∧
      first ≠ second := by
  let first := fixedMassPTFlatFamily 2 1
  let second := fixedMassPTFlatFamily 2 2
  have hFirst : PTSymmetricFlat first :=
    fixedMassPTFlatFamily_is_ptSymmetricFlat 2 1
  have hSecond : PTSymmetricFlat second :=
    fixedMassPTFlatFamily_is_ptSymmetricFlat 2 2
  refine ⟨first, second, hFirst, hSecond,
    ptSymmetricFlat_energy_stationary first hFirst,
    ptSymmetricFlat_energy_stationary second hSecond, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [first, second]
  · norm_num [first, fixedMassPTFlatFamily, ptFlatCoefficients]
  · norm_num [first, fixedMassPTFlatFamily, ptFlatCoefficients]
  · norm_num [second, fixedMassPTFlatFamily, ptFlatCoefficients]
  · norm_num [second, fixedMassPTFlatFamily, ptFlatCoefficients]
  · intro hEqual
    have hParameter :=
      fixedMassPTFlatFamily_injective 2 hEqual
    norm_num at hParameter

end P0EFTJanusPTFlatBimetricCoefficientClassification4D
end JanusFormal
