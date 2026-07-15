import JanusFormal.Branches.JanusSuperfluidAnalogue.Gates.P0EFTJanusSF02SF03Bogoliubov

namespace JanusFormal
namespace P0EFTJanusSF04Scattering

set_option autoImplicit false

noncomputable section

def reflectionFlux (leftImpedance rightImpedance : ℝ) : ℝ :=
  ((rightImpedance - leftImpedance) /
    (rightImpedance + leftImpedance)) ^ 2

def transmissionFlux (leftImpedance rightImpedance : ℝ) : ℝ :=
  4 * leftImpedance * rightImpedance /
    (rightImpedance + leftImpedance) ^ 2

theorem acoustic_step_conserves_flux
    (leftImpedance rightImpedance : ℝ)
    (hDenominator : rightImpedance + leftImpedance ≠ 0) :
    reflectionFlux leftImpedance rightImpedance +
      transmissionFlux leftImpedance rightImpedance = 1 := by
  unfold reflectionFlux transmissionFlux
  field_simp
  ring

theorem matched_impedance_has_no_reflection
    (impedance : ℝ) :
    reflectionFlux impedance impedance = 0 := by
  simp [reflectionFlux]

end
end P0EFTJanusSF04Scattering
end JanusFormal
