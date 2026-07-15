import Mathlib

namespace JanusFormal
namespace P0EFTJanusHelicityZeroScalarSector

set_option autoImplicit false

noncomputable def relativeKinetic (plusKinetic minusKinetic : ℝ) : ℝ :=
  plusKinetic * minusKinetic / (plusKinetic + minusKinetic)

noncomputable def helicityZeroKinetic (plusKinetic minusKinetic : ℝ) : ℝ :=
  3 * relativeKinetic plusKinetic minusKinetic

noncomputable def fpMassSquared
    (plusKinetic minusKinetic interactionMass : ℝ) : ℝ :=
  interactionMass * (plusKinetic + minusKinetic) /
    (plusKinetic * minusKinetic)

theorem helicityZeroKinetic_positive
    (plusKinetic minusKinetic : ℝ)
    (hPlus : 0 < plusKinetic) (hMinus : 0 < minusKinetic) :
    0 < helicityZeroKinetic plusKinetic minusKinetic := by
  unfold helicityZeroKinetic relativeKinetic
  positivity

theorem fpMassSquared_positive
    (plusKinetic minusKinetic interactionMass : ℝ)
    (hPlus : 0 < plusKinetic) (hMinus : 0 < minusKinetic)
    (hMass : 0 < interactionMass) :
    0 < fpMassSquared plusKinetic minusKinetic interactionMass := by
  unfold fpMassSquared
  positivity

theorem scalar_frequency_positive
    (waveNumberSquared massSquared : ℝ)
    (hWave : 0 ≤ waveNumberSquared) (hMass : 0 < massSquared) :
    0 < waveNumberSquared + massSquared := by
  linarith

end P0EFTJanusHelicityZeroScalarSector
end JanusFormal
