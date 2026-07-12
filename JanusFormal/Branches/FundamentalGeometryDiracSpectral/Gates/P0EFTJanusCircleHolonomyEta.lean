import Mathlib

namespace JanusFormal
namespace P0EFTJanusCircleHolonomyEta

set_option autoImplicit false

/--
Eta contribution of the chiral monopole zero-mode tower on a circle with
fractional holonomy `a`, in the fundamental domain `0 < a < 1`.
-/
def zeroModeEta (diracIndex : ℤ) (holonomy : ℝ) : ℝ :=
  (diracIndex : ℝ) * (1 - 2 * holonomy)

/-- PT maps the circle holonomy to its complementary representative. -/
def ptHolonomy (holonomy : ℝ) : ℝ :=
  1 - holonomy

/-- The zero-mode eta invariant is PT odd. -/
theorem eta_is_pt_odd
    (diracIndex : ℤ) (holonomy : ℝ) :
    zeroModeEta diracIndex (ptHolonomy holonomy) =
      -zeroModeEta diracIndex holonomy := by
  unfold zeroModeEta ptHolonomy
  ring

/-- Half holonomy gives vanishing eta. -/
@[simp] theorem eta_vanishes_at_half_holonomy
    (diracIndex : ℤ) :
    zeroModeEta diracIndex (1 / 2) = 0 := by
  unfold zeroModeEta
  norm_num

/-- Zeta-regularized magnitude of the one-dimensional zero-mode determinant. -/
noncomputable def determinantAmplitude (holonomy : ℝ) : ℝ :=
  2 * Real.sin (Real.pi * holonomy)

/-- The determinant amplitude at half holonomy is exactly two. -/
@[simp] theorem determinant_amplitude_at_half :
    determinantAmplitude (1 / 2) = 2 := by
  unfold determinantAmplitude
  have hArg : Real.pi * (1 / 2 : ℝ) = Real.pi / 2 := by ring
  rw [hArg, Real.sin_pi_div_two]
  norm_num

/-- No real holonomy has larger determinant amplitude than the half-holonomy value. -/
theorem determinant_amplitude_le_half
    (holonomy : ℝ) :
    determinantAmplitude holonomy ≤ determinantAmplitude (1 / 2) := by
  rw [determinant_amplitude_at_half]
  unfold determinantAmplitude
  have hSin : Real.sin (Real.pi * holonomy) ≤ 1 :=
    Real.sin_le_one _
  nlinarith

/-- Half holonomy is simultaneously PT fixed and eta neutral. -/
theorem half_holonomy_is_pt_fixed :
    ptHolonomy (1 / 2) = (1 / 2 : ℝ) := by
  unfold ptHolonomy
  norm_num

/--
For a primitive monopole index, the determinant selects a PT-symmetric,
eta-neutral candidate vacuum.  Proving uniqueness of the quantum vacuum requires
the full determinant, local counterterms and the nonzero-mode contribution.
-/
structure HolonomyVacuumStatus where
  primitiveDiracIndexDerived : Prop
  zeroModeDeterminantComputed : Prop
  nonzeroModePairingProved : Prop
  localCountertermsFixed : Prop
  halfHolonomyGloballyMinimizesEffectiveAction : Prop
  etaNeutralityDerived : Prop
  ptInvariantVacuumDerived : Prop


def holonomyVacuumClosed (s : HolonomyVacuumStatus) : Prop :=
  s.primitiveDiracIndexDerived /\
  s.zeroModeDeterminantComputed /\
  s.nonzeroModePairingProved /\
  s.localCountertermsFixed /\
  s.halfHolonomyGloballyMinimizesEffectiveAction /\
  s.etaNeutralityDerived /\
  s.ptInvariantVacuumDerived

end P0EFTJanusCircleHolonomyEta
end JanusFormal
