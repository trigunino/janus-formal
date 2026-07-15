import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleHeatSemigroupOperator
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Strong continuity of the circle heat semigroup

The diagonal circle heat operators form a strongly continuous contraction
semigroup on the full Fourier Hilbert space.  The proof is an explicit
dominated-convergence argument: every coordinate difference tends to zero,
while its square is bounded by four times the square of the corresponding
state coefficient.

The real-time extension of a single Fourier orbit is also differentiated.
Its derivative is the expected negative squared Dirac eigenvalue, giving the
spectral generator on the dense Fourier basis.  This remains a result for the
one-dimensional diagonal circle model; no full Janus Dirac heat kernel or
functional-calculus identification is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusCircleHeatSemigroupStrongContinuity

set_option autoImplicit false

noncomputable section

open Filter Topology
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleUnboundedDiracDomain
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusCircleHeatSemigroupOperator
open scoped ENNReal lp

/-- Each diagonal heat multiplier depends continuously on nonnegative time. -/
theorem circleHeatMultiplier_continuous
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    Continuous (fun time : HeatSemigroupTime =>
      circleHeatMultiplier time fold twist mode) := by
  unfold circleHeatMultiplier
  fun_prop

/-- Squared coordinate difference between two heat times. -/
def circleHeatCoordinateDifferenceSquare
    (time base : HeatSemigroupTime) (fold : Fold) (twist : CircleTwist)
    (state : CircleHilbert) (mode : ℤ) : ℝ :=
  ‖circleHeatMultiplier time fold twist mode * state mode -
      circleHeatMultiplier base fold twist mode * state mode‖ ^ 2

theorem circleHeatCoordinateDifferenceSquare_tendsto
    (base : HeatSemigroupTime) (fold : Fold) (twist : CircleTwist)
    (state : CircleHilbert) (mode : ℤ) :
    Tendsto
      (fun time : HeatSemigroupTime =>
        circleHeatCoordinateDifferenceSquare time base fold twist state mode)
      (nhds base) (nhds 0) := by
  have hMultiplier :
      Tendsto
        (fun time : HeatSemigroupTime =>
          circleHeatMultiplier time fold twist mode)
        (nhds base)
        (nhds (circleHeatMultiplier base fold twist mode)) :=
    (circleHeatMultiplier_continuous fold twist mode).continuousAt
  have hDifference :
      Tendsto
        (fun time : HeatSemigroupTime =>
          circleHeatMultiplier time fold twist mode * state mode -
            circleHeatMultiplier base fold twist mode * state mode)
        (nhds base) (nhds 0) := by
    simpa using
      (hMultiplier.mul_const (state mode)).sub_const
        (circleHeatMultiplier base fold twist mode * state mode)
  simpa [circleHeatCoordinateDifferenceSquare] using
    (tendsto_norm.comp hDifference).pow 2

/-- Uniform summable coordinate domination used for strong continuity. -/
theorem circleHeatCoordinateDifferenceSquare_le
    (time base : HeatSemigroupTime) (fold : Fold) (twist : CircleTwist)
    (state : CircleHilbert) (mode : ℤ) :
    circleHeatCoordinateDifferenceSquare time base fold twist state mode ≤
      4 * ‖state mode‖ ^ 2 := by
  rw [circleHeatCoordinateDifferenceSquare]
  have hDifference :
      ‖circleHeatMultiplier time fold twist mode * state mode -
          circleHeatMultiplier base fold twist mode * state mode‖ ≤
        2 * ‖state mode‖ := by
    calc
      _ ≤ ‖circleHeatMultiplier time fold twist mode * state mode‖ +
          ‖circleHeatMultiplier base fold twist mode * state mode‖ :=
        norm_sub_le _ _
      _ = ‖circleHeatMultiplier time fold twist mode‖ * ‖state mode‖ +
          ‖circleHeatMultiplier base fold twist mode‖ * ‖state mode‖ := by
        rw [norm_mul, norm_mul]
      _ ≤ 2 * ‖state mode‖ := by
        nlinarith [circleHeatMultiplier_norm_le_one time fold twist mode,
          circleHeatMultiplier_norm_le_one base fold twist mode,
          norm_nonneg (circleHeatMultiplier time fold twist mode),
          norm_nonneg (circleHeatMultiplier base fold twist mode),
          norm_nonneg (state mode)]
  calc
    _ ≤ (2 * ‖state mode‖) ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _)
        (mul_nonneg (by norm_num) (norm_nonneg _))).2 hDifference
    _ = 4 * ‖state mode‖ ^ 2 := by ring

theorem circleHeatCoordinateBound_summable (state : CircleHilbert) :
    Summable (fun mode : ℤ => 4 * ‖state mode‖ ^ 2) := by
  have hState := (lp.memℓp state).summable
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)
  simpa [Real.rpow_two] using hState.mul_left 4

/-- The diagonal heat semigroup is strongly continuous at every nonnegative
time on every vector of the full circle Hilbert space. -/
theorem circleHeatSemigroup_stronglyContinuous
    (fold : Fold) (twist : CircleTwist) (state : CircleHilbert) :
    Continuous (fun time : HeatSemigroupTime =>
      circleHeatSemigroup time fold twist state) := by
  rw [continuous_iff_continuousAt]
  intro base
  apply tendsto_iff_norm_sub_tendsto_zero.2
  have hTsum :
      Tendsto
        (fun time : HeatSemigroupTime =>
          ∑' mode : ℤ,
            circleHeatCoordinateDifferenceSquare time base fold twist state mode)
        (nhds base) (nhds 0) := by
    have hDominated := tendsto_tsum_of_dominated_convergence
      (circleHeatCoordinateBound_summable state)
      (fun mode =>
        circleHeatCoordinateDifferenceSquare_tendsto
          base fold twist state mode)
      (Eventually.of_forall (fun time mode => by
        have hNonnegative :
            0 ≤ circleHeatCoordinateDifferenceSquare
              time base fold twist state mode := by
          unfold circleHeatCoordinateDifferenceSquare
          positivity
        simpa [Real.norm_eq_abs, abs_of_nonneg hNonnegative] using
          circleHeatCoordinateDifferenceSquare_le
            time base fold twist state mode))
    simpa using hDominated
  have hRoot := hTsum.rpow_const_nhds_zero
    (by norm_num : 0 < (1 / 2 : ℝ))
  apply hRoot.congr'
  filter_upwards [] with time
  rw [lp.norm_eq_tsum_rpow
    (by norm_num : 0 < (2 : ℝ≥0∞).toReal)]
  simp only [ENNReal.toReal_ofNat, Real.rpow_two]
  congr 2

/-- In particular the heat semigroup converges strongly to the identity at
time zero. -/
theorem circleHeatSemigroup_tendsto_zero
    (fold : Fold) (twist : CircleTwist) (state : CircleHilbert) :
    Tendsto (fun time : HeatSemigroupTime =>
      circleHeatSemigroup time fold twist state)
      (nhds zeroHeatSemigroupTime) (nhds state) := by
  have hContinuousAt :
      Tendsto (fun time : HeatSemigroupTime =>
        circleHeatSemigroup time fold twist state)
        (nhds zeroHeatSemigroupTime)
        (nhds (circleHeatSemigroup zeroHeatSemigroupTime fold twist state)) :=
    (circleHeatSemigroup_stronglyContinuous fold twist state).continuousAt
  simpa [circleHeatSemigroup_zero] using hContinuousAt

/-- Real-time extension of one diagonal Fourier orbit.  Only its restriction
to nonnegative times is used by the bounded semigroup. -/
def circleHeatBasisOrbitReal
    (time : ℝ) (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    CircleHilbert :=
  Real.exp (-time * circleOperatorSquaredEigenvalue fold twist mode) •
    circleFourierBasis mode

theorem circleHeatBasisOrbitReal_of_nonnegative
    (time : HeatSemigroupTime) (fold : Fold) (twist : CircleTwist)
    (mode : ℤ) :
    circleHeatBasisOrbitReal time.1 fold twist mode =
      circleHeatSemigroup time fold twist (circleFourierBasis mode) := by
  rw [circleHeatSemigroup_on_basis]
  ext other
  simp [circleHeatBasisOrbitReal, circleHeatMultiplier]

/-- Spectral generator on a Fourier basis vector: the derivative is
`-D²` times that vector. -/
theorem circleHeatBasisOrbitReal_hasDerivAt
    (time : ℝ) (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    HasDerivAt (fun parameter : ℝ =>
      circleHeatBasisOrbitReal parameter fold twist mode)
      ((-circleOperatorSquaredEigenvalue fold twist mode *
          Real.exp (-time *
            circleOperatorSquaredEigenvalue fold twist mode)) •
        circleFourierBasis mode)
      time := by
  have hExponent :
      HasDerivAt
        (fun parameter : ℝ =>
          -parameter * circleOperatorSquaredEigenvalue fold twist mode)
        (-circleOperatorSquaredEigenvalue fold twist mode) time := by
    simpa using (hasDerivAt_id (x := time)).neg.mul_const
      (circleOperatorSquaredEigenvalue fold twist mode)
  have hScalar :=
    (Real.hasDerivAt_exp
      (-time * circleOperatorSquaredEigenvalue fold twist mode)).comp
      time hExponent
  simpa [circleHeatBasisOrbitReal, mul_comm, mul_left_comm, mul_assoc] using
    hScalar.smul_const (circleFourierBasis mode)

theorem circleHeatBasisOrbitReal_hasDerivAt_zero
    (fold : Fold) (twist : CircleTwist) (mode : ℤ) :
    HasDerivAt (fun parameter : ℝ =>
      circleHeatBasisOrbitReal parameter fold twist mode)
      ((-circleOperatorSquaredEigenvalue fold twist mode) •
        circleFourierBasis mode)
      0 := by
  simpa using circleHeatBasisOrbitReal_hasDerivAt
    0 fold twist mode

end

end P0EFTJanusCircleHeatSemigroupStrongContinuity
end JanusFormal
