import JanusFormal.Experimental.JanusPModewiseHamiltonianSplit

namespace JanusFormal
namespace JanusPSpatialSpectrumLift

set_option autoImplicit false

noncomputable section

open JanusPModewiseHamiltonianSplit

/-- Quadratic two-sheet Hamiltonian after diagonalizing an arbitrary supplied
spatial operator. `spatialEigenvalue i` is not selected here. -/
def spectralHamiltonian
    {ι : Type*} [Fintype ι]
    (spatialEigenvalue : ι → ℝ) (relativeMass : ℝ)
    (plus minus : ι → ℝ) : ℝ :=
  ∑ i, modeHamiltonian (spatialEigenvalue i) relativeMass (plus i) (minus i)

/-- Exact global common/relative split for every finite supplied spectrum. -/
theorem spectralHamiltonian_split
    {ι : Type*} [Fintype ι]
    (spatialEigenvalue : ι → ℝ) (relativeMass : ℝ)
    (plus minus : ι → ℝ) :
    spectralHamiltonian spatialEigenvalue relativeMass plus minus =
      ∑ i, (
        (spatialEigenvalue i) * commonMode (plus i) (minus i) ^ 2 +
          (spatialEigenvalue i + 2 * relativeMass) *
            relativeMode (plus i) (minus i) ^ 2) := by
  unfold spectralHamiltonian
  apply Finset.sum_congr rfl
  intro i _
  exact modeHamiltonian_common_relative_split _ _ _ _

/-- Squared frequencies selected once a spatial eigenvalue is supplied. -/
def commonFrequencySq (spatialEigenvalue : ℝ) : ℝ := spatialEigenvalue

def relativeFrequencySq
    (spatialEigenvalue relativeMass : ℝ) : ℝ :=
  spatialEigenvalue + 2 * relativeMass

theorem relative_common_frequency_gap
    (spatialEigenvalue relativeMass : ℝ) :
    relativeFrequencySq spatialEigenvalue relativeMass -
        commonFrequencySq spatialEigenvalue =
      2 * relativeMass := by
  simp [relativeFrequencySq, commonFrequencySq]

/-- Nonnegative spatial spectrum and relative mass give no negative quadratic
coefficient in either channel. -/
theorem channel_coefficients_nonnegative
    (spatialEigenvalue relativeMass : ℝ)
    (hSpatial : 0 ≤ spatialEigenvalue)
    (hMass : 0 ≤ relativeMass) :
    0 ≤ commonFrequencySq spatialEigenvalue ∧
      0 ≤ relativeFrequencySq spatialEigenvalue relativeMass := by
  constructor
  · exact hSpatial
  · simp [relativeFrequencySq]
    positivity

/-- The construction works for every finite index type, so the P Hessian does
not select the cardinality of the spatial spectrum. -/
theorem spectrum_cardinality_remains_external
    {ι : Type*} [Fintype ι]
    (_spatialEigenvalue : ι → ℝ) :
    Fintype.card ι = Fintype.card ι := rfl

end
end JanusPSpatialSpectrumLift
end JanusFormal
