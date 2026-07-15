import Mathlib

namespace JanusFormal
namespace P0EFTJanusCosmologicalHiguchiGate

set_option autoImplicit false

def higuchiGap (effectiveMassSquared hubbleSquared : ℝ) : ℝ :=
  effectiveMassSquared - 2 * hubbleSquared

noncomputable def bimetricHiguchiGap
    (massSquared beta1 beta2 beta3 plusHubble minusHubble
      plusKinetic minusKinetic : ℝ) : ℝ :=
  (massSquared / 2) *
      (beta1 * minusHubble ^ 2 + 2 * beta2 * plusHubble * minusHubble +
        beta3 * plusHubble ^ 2) *
      (plusHubble ^ 2 / plusKinetic + minusHubble ^ 2 / minusKinetic) -
    2 * minusHubble ^ 3 * plusHubble ^ 3

theorem bimetric_gap_exchange_symmetric
    (massSquared beta1 beta2 beta3 plusHubble minusHubble
      plusKinetic minusKinetic : ℝ) :
    bimetricHiguchiGap massSquared beta1 beta2 beta3
        plusHubble minusHubble plusKinetic minusKinetic =
      bimetricHiguchiGap massSquared beta3 beta2 beta1
        minusHubble plusHubble minusKinetic plusKinetic := by
  unfold bimetricHiguchiGap
  ring

theorem positive_higuchi_gap_implies_positive_mass
    (effectiveMassSquared hubbleSquared : ℝ)
    (hHubble : 0 ≤ hubbleSquared)
    (hGap : 0 < higuchiGap effectiveMassSquared hubbleSquared) :
    0 < effectiveMassSquared := by
  unfold higuchiGap at hGap
  linarith

theorem strong_coupling_surface_has_zero_gap
    (effectiveMassSquared hubbleSquared : ℝ)
    (hSurface : effectiveMassSquared = 2 * hubbleSquared) :
    higuchiGap effectiveMassSquared hubbleSquared = 0 := by
  unfold higuchiGap
  linarith

theorem uniform_gap_keeps_trajectory_off_surface
    (gap : ℝ → ℝ) (epsilon : ℝ)
    (hEpsilon : 0 < epsilon)
    (hUniform : ∀ t, epsilon ≤ gap t) :
    ∀ t, gap t ≠ 0 := by
  intro t hZero
  have := hUniform t
  rw [hZero] at this
  linarith

end P0EFTJanusCosmologicalHiguchiGate
end JanusFormal
