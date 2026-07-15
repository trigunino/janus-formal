import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusReducedBimetricQuadraticFrechetSpectrum
import JanusFormal.Branches.NonlinearBimetricJunctionAlpha.Gates.P0EFTJanusPositiveBimetricLinearSpectrum

namespace JanusFormal
namespace JanusPTensorFourierConstraintReducedBridge

set_option autoImplicit false

noncomputable section

open P0EFTJanusReducedBimetricQuadraticFrechetSpectrum
open P0EFTJanusPositiveBimetricLinearSpectrum

/-- The interaction Hessian derived in P is exactly the relative tensor
bilinear form used by the bimetric linear spectrum. -/
theorem p_interaction_hessian_is_relative_mass_form
    (relativeMass hPlus hMinus dPlus dMinus : ℝ) :
    interactionHessian relativeMass
        ⟨hPlus, hMinus⟩ ⟨dPlus, dMinus⟩ =
      relativeMass * (hPlus - hMinus) * (dPlus - dMinus) := by
  simp [interactionHessian, reducedQuadraticHessian_apply]

/-- Fourier-reduced TT operator: Einstein-Hilbert spatial eigenvalue `k²`
plus P's relative interaction Hessian. -/
def tensorFourierOperatorPlus
    (planckPlusSquared relativeMass waveNumber hPlus hMinus : ℝ) : ℝ :=
  waveNumber ^ 2 * hPlus +
    weightedMassOperatorPlus planckPlusSquared relativeMass hPlus hMinus

def tensorFourierOperatorMinus
    (planckMinusSquared relativeMass waveNumber hPlus hMinus : ℝ) : ℝ :=
  waveNumber ^ 2 * hMinus +
    weightedMassOperatorMinus planckMinusSquared relativeMass hPlus hMinus

/-- The diagonal TT graviton has the massless dispersion `ω²=k²`. -/
theorem diagonal_tensor_dispersion
    (planckPlusSquared planckMinusSquared relativeMass waveNumber h : ℝ) :
    tensorFourierOperatorPlus planckPlusSquared relativeMass waveNumber h h =
        waveNumber ^ 2 * h ∧
      tensorFourierOperatorMinus planckMinusSquared relativeMass waveNumber h h =
        waveNumber ^ 2 * h := by
  constructor <;>
    simp [tensorFourierOperatorPlus, tensorFourierOperatorMinus,
      weightedMassOperatorPlus, weightedMassOperatorMinus]

/-- The weighted relative TT graviton has dispersion
`ω²=k²+m²(1/M₊²+1/M₋²)`. -/
theorem weighted_relative_tensor_dispersion
    (planckPlusSquared planckMinusSquared relativeMass waveNumber h : ℝ)
    (hPlus : planckPlusSquared ≠ 0)
    (hMinus : planckMinusSquared ≠ 0) :
    tensorFourierOperatorPlus planckPlusSquared relativeMass waveNumber
        (planckMinusSquared * h) (-planckPlusSquared * h) =
      (waveNumber ^ 2 + weightedRelativeEigenvalue
        planckPlusSquared planckMinusSquared relativeMass) *
          (planckMinusSquared * h) ∧
    tensorFourierOperatorMinus planckMinusSquared relativeMass waveNumber
        (planckMinusSquared * h) (-planckPlusSquared * h) =
      (waveNumber ^ 2 + weightedRelativeEigenvalue
        planckPlusSquared planckMinusSquared relativeMass) *
          (-planckPlusSquared * h) := by
  have hWeighted := unequal_kinetic_weighted_relative_mode
    planckPlusSquared planckMinusSquared relativeMass h hPlus hMinus
  constructor
  · unfold tensorFourierOperatorPlus
    rw [hWeighted.1]
    ring
  · unfold tensorFourierOperatorMinus
    rw [hWeighted.2]
    ring

/-- Positive Einstein-Hilbert weights and positive P interaction mass give a
strictly positive massive TT frequency for every Fourier wave number. -/
theorem weighted_relative_tensor_frequency_positive
    (planckPlusSquared planckMinusSquared relativeMass waveNumber : ℝ)
    (hPlanckPlus : 0 < planckPlusSquared)
    (hPlanckMinus : 0 < planckMinusSquared)
    (hMass : 0 < relativeMass) :
    0 < waveNumber ^ 2 + weightedRelativeEigenvalue
      planckPlusSquared planckMinusSquared relativeMass := by
  exact add_pos_of_nonneg_of_pos (sq_nonneg waveNumber)
    (weighted_relative_eigenvalue_positive
      planckPlusSquared planckMinusSquared relativeMass
      hPlanckPlus hPlanckMinus hMass)

end
end JanusPTensorFourierConstraintReducedBridge
end JanusFormal
