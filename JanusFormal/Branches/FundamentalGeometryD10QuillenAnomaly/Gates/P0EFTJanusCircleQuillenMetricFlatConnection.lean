import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusCircleDeterminantTopologicalBundle

/-!
# A clutching-compatible Hermitian metric and flat connection on the circle determinant line

This gate equips the actual topological determinant-line family of the
normalized bounded circle Dirac operator with explicit geometric data.  The
large-gauge endpoint transition is a constant complex multiplier `lambda` in
the Fourier frame.  A positive exponential weight interpolates its norm, so
the endpoint transition is an isometry.  The associated constant connection
is flat and its closed-loop holonomy is the unit phase `lambda / |lambda|`.

This is an explicit circle model in a chosen Fourier trivialization.  It is not
identified with the analytic Quillen/Bismut--Freed connection of a general
unbounded Fredholm family; no local family-index curvature formula is claimed.
-/

namespace JanusFormal
namespace P0EFTJanusCircleQuillenMetricFlatConnection

set_option autoImplicit false

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleBoundedTransformSpectralFlow
open P0EFTJanusCircleDeterminantLineFamily
open P0EFTJanusCircleDeterminantTopologicalBundle
open P0EFTJanusCircleHolonomyEta
open scoped ComplexConjugate

/-! ## The exact clutching multiplier -/

/-- Constant multiplier of the exact large-gauge transition in Fourier
coordinates. -/
def circleDeterminantClutchingMultiplier (fold : Fold) : ℂ :=
  circleLargeGaugeFrameCoordinateTransition fold 1

theorem circleLargeGaugeFrameCoordinateTransition_apply
    (fold : Fold) (scalar : ℂ) :
    circleLargeGaugeFrameCoordinateTransition fold scalar =
      scalar * circleDeterminantClutchingMultiplier fold := by
  change circleLargeGaugeFrameCoordinateTransition fold scalar =
    scalar • circleLargeGaugeFrameCoordinateTransition fold 1
  simpa using
    (circleLargeGaugeFrameCoordinateTransition fold).map_smul scalar (1 : ℂ)

theorem circleDeterminantClutchingMultiplier_ne_zero (fold : Fold) :
    circleDeterminantClutchingMultiplier fold ≠ 0 := by
  intro hZero
  have hEqual :
      circleLargeGaugeFrameCoordinateTransition fold 1 =
        circleLargeGaugeFrameCoordinateTransition fold 0 := by
    rw [circleDeterminantClutchingMultiplier] at hZero
    exact hZero.trans
      (map_zero (circleLargeGaugeFrameCoordinateTransition fold)).symm
  exact one_ne_zero
    ((circleLargeGaugeFrameCoordinateTransition fold).injective hEqual)

theorem circleDeterminantClutchingMultiplier_norm_pos (fold : Fold) :
    0 < ‖circleDeterminantClutchingMultiplier fold‖ :=
  norm_pos_iff.mpr (circleDeterminantClutchingMultiplier_ne_zero fold)

/-! ## Clutching-compatible Hermitian metric -/

/-- Real connection coefficient `log |lambda|`. -/
def circleQuillenConnectionCoefficient (fold : Fold) : ℝ :=
  Real.log ‖circleDeterminantClutchingMultiplier fold‖

/-- Positive metric weight in the Fourier frame at holonomy `a`. -/
def circleQuillenMetricWeight (fold : Fold) (holonomy : ℝ) : ℝ :=
  Real.exp (2 * holonomy * circleQuillenConnectionCoefficient fold)

theorem circleQuillenMetricWeight_pos (fold : Fold) (holonomy : ℝ) :
    0 < circleQuillenMetricWeight fold holonomy :=
  Real.exp_pos _

@[simp] theorem circleQuillenMetricWeight_zero (fold : Fold) :
    circleQuillenMetricWeight fold 0 = 1 := by
  simp [circleQuillenMetricWeight]

theorem circleQuillenMetricWeight_one (fold : Fold) :
    circleQuillenMetricWeight fold 1 =
      Complex.normSq (circleDeterminantClutchingMultiplier fold) := by
  let normLambda := ‖circleDeterminantClutchingMultiplier fold‖
  have hNorm : 0 < normLambda :=
    circleDeterminantClutchingMultiplier_norm_pos fold
  calc
    circleQuillenMetricWeight fold 1 =
        Real.exp (Real.log normLambda + Real.log normLambda) := by
      simp only [circleQuillenMetricWeight,
        circleQuillenConnectionCoefficient]
      congr 1
      ring
    _ = Real.exp (Real.log normLambda) *
        Real.exp (Real.log normLambda) := by rw [Real.exp_add]
    _ = normLambda * normLambda := by simp [Real.exp_log hNorm]
    _ = Complex.normSq (circleDeterminantClutchingMultiplier fold) := by
      rw [Complex.normSq_eq_norm_sq]
      ring

/-- Fourier coordinate of an element of an actual determinant fiber. -/
def circleDeterminantCoordinate
    (fold : Fold) (twist : CircleTwist)
    (value : CircleDeterminantFiber fold twist) : ℂ :=
  (circleDeterminantFrameEquiv fold twist).symm value

/-- Explicit Hermitian pairing on the actual determinant fiber. -/
def circleQuillenHermitianMetric
    (fold : Fold) (twist : CircleTwist)
    (first second : CircleDeterminantFiber fold twist) : ℂ :=
  (circleQuillenMetricWeight fold twist.value : ℂ) *
    conj (circleDeterminantCoordinate fold twist first) *
      circleDeterminantCoordinate fold twist second

/-- Squared norm associated with the explicit Hermitian metric. -/
def circleQuillenNormSq
    (fold : Fold) (twist : CircleTwist)
    (value : CircleDeterminantFiber fold twist) : ℝ :=
  circleQuillenMetricWeight fold twist.value *
    Complex.normSq (circleDeterminantCoordinate fold twist value)

theorem circleQuillenHermitianMetric_conj_symm
    (fold : Fold) (twist : CircleTwist)
    (first second : CircleDeterminantFiber fold twist) :
    conj (circleQuillenHermitianMetric fold twist first second) =
      circleQuillenHermitianMetric fold twist second first := by
  simp [circleQuillenHermitianMetric]
  ring

theorem circleQuillenHermitianMetric_add_right
    (fold : Fold) (twist : CircleTwist)
    (first second third : CircleDeterminantFiber fold twist) :
    circleQuillenHermitianMetric fold twist first (second + third) =
      circleQuillenHermitianMetric fold twist first second +
        circleQuillenHermitianMetric fold twist first third := by
  simp [circleQuillenHermitianMetric, circleDeterminantCoordinate]
  ring

theorem circleQuillenHermitianMetric_smul_right
    (fold : Fold) (twist : CircleTwist) (scalar : ℂ)
    (first second : CircleDeterminantFiber fold twist) :
    circleQuillenHermitianMetric fold twist first (scalar • second) =
      scalar * circleQuillenHermitianMetric fold twist first second := by
  simp [circleQuillenHermitianMetric, circleDeterminantCoordinate]
  ring

theorem circleQuillenNormSq_nonnegative
    (fold : Fold) (twist : CircleTwist)
    (value : CircleDeterminantFiber fold twist) :
    0 ≤ circleQuillenNormSq fold twist value := by
  exact mul_nonneg (circleQuillenMetricWeight_pos fold twist.value).le
    (Complex.normSq_nonneg _)

theorem circleQuillenNormSq_eq_zero_iff
    (fold : Fold) (twist : CircleTwist)
    (value : CircleDeterminantFiber fold twist) :
    circleQuillenNormSq fold twist value = 0 ↔ value = 0 := by
  rw [circleQuillenNormSq, mul_eq_zero]
  simp only [(circleQuillenMetricWeight_pos fold twist.value).ne', false_or,
    Complex.normSq_eq_zero]
  constructor
  · intro hCoordinate
    apply (circleDeterminantFrameEquiv fold twist).symm.injective
    simpa [circleDeterminantCoordinate] using hCoordinate
  · intro hValue
    subst value
    simp [circleDeterminantCoordinate]

/-! ## Endpoint isometry and the regularized section -/

theorem circleLargeGaugeDeterminantTransition_coordinate
    (fold : Fold)
    (value : CircleDeterminantFiber fold unitCircleTwist) :
    circleDeterminantCoordinate fold periodicTwist
        (circleLargeGaugeDeterminantTransition fold value) =
      circleLargeGaugeFrameCoordinateTransition fold
        (circleDeterminantCoordinate fold unitCircleTwist value) := by
  simp [circleDeterminantCoordinate,
    circleLargeGaugeFrameCoordinateTransition]

/-- The exact large-gauge endpoint clutching preserves the interpolated
Hermitian norm. -/
theorem circleLargeGaugeDeterminantTransition_isometry
    (fold : Fold)
    (value : CircleDeterminantFiber fold unitCircleTwist) :
    circleQuillenNormSq fold periodicTwist
        (circleLargeGaugeDeterminantTransition fold value) =
      circleQuillenNormSq fold unitCircleTwist value := by
  rw [circleQuillenNormSq, circleQuillenNormSq,
    circleLargeGaugeDeterminantTransition_coordinate,
    circleLargeGaugeFrameCoordinateTransition_apply,
    Complex.normSq_mul]
  change circleQuillenMetricWeight fold 0 *
      (Complex.normSq (circleDeterminantCoordinate fold unitCircleTwist value) *
        Complex.normSq (circleDeterminantClutchingMultiplier fold)) =
    circleQuillenMetricWeight fold 1 *
      Complex.normSq (circleDeterminantCoordinate fold unitCircleTwist value)
  rw [circleQuillenMetricWeight_zero, circleQuillenMetricWeight_one]
  ring

@[simp] theorem circleRegularizedDeterminantSection_coordinate
    (fold : Fold) (twist : CircleTwist) :
    circleDeterminantCoordinate fold twist
        (circleRegularizedDeterminantSection fold twist) =
      circleRegularizedDeterminantCoordinate twist := by
  simp [circleDeterminantCoordinate, circleRegularizedDeterminantSection]

theorem circleRegularizedDeterminantSection_quillenNormSq
    (fold : Fold) (twist : CircleTwist) :
    circleQuillenNormSq fold twist
        (circleRegularizedDeterminantSection fold twist) =
      circleQuillenMetricWeight fold twist.value *
        (determinantAmplitude twist.value) ^ 2 := by
  rw [circleQuillenNormSq,
    circleRegularizedDeterminantSection_coordinate,
    circleRegularizedDeterminantCoordinate, Complex.normSq_ofReal]
  ring

theorem circleRegularizedDeterminantSection_quillenNormSq_pos_of_interior
    (fold : Fold) (twist : CircleTwist)
    (hPositive : 0 < twist.value) (hLess : twist.value < 1) :
    0 < circleQuillenNormSq fold twist
      (circleRegularizedDeterminantSection fold twist) := by
  rw [circleRegularizedDeterminantSection_quillenNormSq]
  apply mul_pos (circleQuillenMetricWeight_pos fold twist.value)
  apply sq_pos_of_pos
  unfold determinantAmplitude
  exact mul_pos (by norm_num) <|
    Real.sin_pos_of_pos_of_lt_pi
      (mul_pos Real.pi_pos hPositive)
      (by nlinarith [Real.pi_pos])

/-! ## Metric-compatible flat connection in Fourier coordinates -/

/-- Connection applied to a first jet `(value, derivative)` in the Fourier
coordinate. -/
def circleQuillenConnectionAt
    (fold : Fold) (value derivative : ℂ) : ℂ :=
  derivative + (circleQuillenConnectionCoefficient fold : ℂ) * value

/-- Leibniz rule for the explicit first-jet connection. -/
theorem circleQuillenConnectionAt_leibniz
    (fold : Fold) (scalar scalarDerivative value derivative : ℂ) :
    circleQuillenConnectionAt fold (scalar * value)
        (scalarDerivative * value + scalar * derivative) =
      scalarDerivative * value +
        scalar * circleQuillenConnectionAt fold value derivative := by
  simp [circleQuillenConnectionAt]
  ring

/-- Hermitian pairing in a fixed Fourier coordinate. -/
def circleQuillenCoordinateMetric
    (fold : Fold) (holonomy : ℝ) (first second : ℂ) : ℂ :=
  (circleQuillenMetricWeight fold holonomy : ℂ) * conj first * second

/-- First variation of the explicit coordinate metric. -/
def circleQuillenCoordinateMetricFirstVariation
    (fold : Fold) (holonomy : ℝ)
    (first firstDerivative second secondDerivative : ℂ) : ℂ :=
  ((2 * circleQuillenConnectionCoefficient fold *
      circleQuillenMetricWeight fold holonomy : ℝ) : ℂ) * conj first * second +
    (circleQuillenMetricWeight fold holonomy : ℂ) * conj firstDerivative * second +
    (circleQuillenMetricWeight fold holonomy : ℂ) * conj first * secondDerivative

/-- Metric compatibility of the connection, expressed on first jets. -/
theorem circleQuillenConnection_metric_compatible
    (fold : Fold) (holonomy : ℝ)
    (first firstDerivative second secondDerivative : ℂ) :
    circleQuillenCoordinateMetricFirstVariation fold holonomy
        first firstDerivative second secondDerivative =
      circleQuillenCoordinateMetric fold holonomy
          (circleQuillenConnectionAt fold first firstDerivative) second +
        circleQuillenCoordinateMetric fold holonomy first
          (circleQuillenConnectionAt fold second secondDerivative) := by
  simp [circleQuillenCoordinateMetricFirstVariation,
    circleQuillenCoordinateMetric, circleQuillenConnectionAt]
  ring

/-- Constant connection one-form on the one-dimensional holonomy interval. -/
def circleQuillenConnectionOneForm (fold : Fold) (direction : ℝ) : ℂ :=
  (direction * circleQuillenConnectionCoefficient fold : ℝ)

/-- Curvature of the constant rank-one connection.  The derivative term is
zero and the scalar commutator is displayed explicitly. -/
def circleQuillenConnectionCurvature
    (fold : Fold) (firstDirection secondDirection : ℝ) : ℂ :=
  circleQuillenConnectionOneForm fold firstDirection *
      circleQuillenConnectionOneForm fold secondDirection -
    circleQuillenConnectionOneForm fold secondDirection *
      circleQuillenConnectionOneForm fold firstDirection

@[simp] theorem circleQuillenConnectionCurvature_zero
    (fold : Fold) (firstDirection secondDirection : ℝ) :
    circleQuillenConnectionCurvature fold firstDirection secondDirection = 0 := by
  unfold circleQuillenConnectionCurvature
  ring

theorem circleQuillenConnection_is_flat (fold : Fold) :
    circleQuillenConnectionCurvature fold = fun _ _ => 0 := by
  funext firstDirection secondDirection
  exact circleQuillenConnectionCurvature_zero fold firstDirection secondDirection

/-! ## Parallel transport and closed-loop holonomy -/

/-- Positive parallel-transport scale from `first` to `second`. -/
def circleQuillenParallelTransportScale
    (fold : Fold) (first second : ℝ) : ℝ :=
  Real.exp (circleQuillenConnectionCoefficient fold * (first - second))

theorem circleQuillenParallelTransportScale_pos
    (fold : Fold) (first second : ℝ) :
    0 < circleQuillenParallelTransportScale fold first second :=
  Real.exp_pos _

@[simp] theorem circleQuillenParallelTransportScale_self
    (fold : Fold) (holonomy : ℝ) :
    circleQuillenParallelTransportScale fold holonomy holonomy = 1 := by
  simp [circleQuillenParallelTransportScale]

theorem circleQuillenParallelTransportScale_trans
    (fold : Fold) (first second third : ℝ) :
    circleQuillenParallelTransportScale fold second third *
        circleQuillenParallelTransportScale fold first second =
      circleQuillenParallelTransportScale fold first third := by
  unfold circleQuillenParallelTransportScale
  rw [← Real.exp_add]
  congr 1
  ring

/-- Parallel transport in the Fourier coordinate. -/
def circleQuillenParallelTransport
    (fold : Fold) (first second : ℝ) (value : ℂ) : ℂ :=
  (circleQuillenParallelTransportScale fold first second : ℂ) * value

@[simp] theorem circleQuillenParallelTransport_self
    (fold : Fold) (holonomy : ℝ) (value : ℂ) :
    circleQuillenParallelTransport fold holonomy holonomy value = value := by
  simp [circleQuillenParallelTransport]

theorem circleQuillenParallelTransport_trans
    (fold : Fold) (first second third : ℝ) (value : ℂ) :
    circleQuillenParallelTransport fold second third
        (circleQuillenParallelTransport fold first second value) =
      circleQuillenParallelTransport fold first third value := by
  rw [circleQuillenParallelTransport, circleQuillenParallelTransport,
    circleQuillenParallelTransport, ← mul_assoc, ← Complex.ofReal_mul,
    circleQuillenParallelTransportScale_trans]

/-- Squared Hermitian norm in one Fourier coordinate. -/
def circleQuillenCoordinateNormSq
    (fold : Fold) (holonomy : ℝ) (value : ℂ) : ℝ :=
  circleQuillenMetricWeight fold holonomy * Complex.normSq value

theorem circleQuillenMetricWeight_transport_scale
    (fold : Fold) (first second : ℝ) :
    circleQuillenMetricWeight fold second *
        (circleQuillenParallelTransportScale fold first second) ^ 2 =
      circleQuillenMetricWeight fold first := by
  let coefficient := circleQuillenConnectionCoefficient fold
  let exponent := coefficient * (first - second)
  calc
    circleQuillenMetricWeight fold second *
        (circleQuillenParallelTransportScale fold first second) ^ 2 =
      Real.exp (2 * second * coefficient) *
        (Real.exp exponent * Real.exp exponent) := by
          simp [circleQuillenMetricWeight,
            circleQuillenParallelTransportScale, coefficient, exponent, pow_two]
    _ = Real.exp (2 * second * coefficient) *
        Real.exp (exponent + exponent) := by rw [Real.exp_add]
    _ = Real.exp (2 * second * coefficient + exponent + exponent) := by
      rw [← Real.exp_add]
      congr 1
      ring
    _ = Real.exp (2 * first * coefficient) := by
      congr 1
      dsimp [exponent]
      ring
    _ = circleQuillenMetricWeight fold first := by
      rfl

/-- Parallel transport is an isometry for the interpolated Hermitian metric. -/
theorem circleQuillenParallelTransport_isometry
    (fold : Fold) (first second : ℝ) (value : ℂ) :
    circleQuillenCoordinateNormSq fold second
        (circleQuillenParallelTransport fold first second value) =
      circleQuillenCoordinateNormSq fold first value := by
  rw [circleQuillenCoordinateNormSq, circleQuillenCoordinateNormSq,
    circleQuillenParallelTransport, Complex.normSq_mul,
    Complex.normSq_ofReal]
  calc
    circleQuillenMetricWeight fold second *
        (circleQuillenParallelTransportScale fold first second *
          circleQuillenParallelTransportScale fold first second *
            Complex.normSq value) =
      (circleQuillenMetricWeight fold second *
        (circleQuillenParallelTransportScale fold first second) ^ 2) *
          Complex.normSq value := by ring
    _ = circleQuillenMetricWeight fold first * Complex.normSq value := by
      rw [circleQuillenMetricWeight_transport_scale]

theorem circleQuillenParallelTransportScale_zero_one (fold : Fold) :
    circleQuillenParallelTransportScale fold 0 1 =
      ‖circleDeterminantClutchingMultiplier fold‖⁻¹ := by
  rw [circleQuillenParallelTransportScale,
    circleQuillenConnectionCoefficient]
  have hNorm := circleDeterminantClutchingMultiplier_norm_pos fold
  rw [show Real.log ‖circleDeterminantClutchingMultiplier fold‖ * (0 - 1) =
      -Real.log ‖circleDeterminantClutchingMultiplier fold‖ by ring,
    Real.exp_neg, Real.exp_log hNorm]

/-- Closed-loop holonomy: parallel transport across `[0,1]`, followed by the
exact large-gauge clutching transition. -/
def circleQuillenClosedHolonomy (fold : Fold) : ℂ :=
  circleDeterminantClutchingMultiplier fold /
    (‖circleDeterminantClutchingMultiplier fold‖ : ℂ)

theorem circleQuillenClosedHolonomy_ne_zero (fold : Fold) :
    circleQuillenClosedHolonomy fold ≠ 0 := by
  apply div_ne_zero (circleDeterminantClutchingMultiplier_ne_zero fold)
  exact_mod_cast (circleDeterminantClutchingMultiplier_norm_pos fold).ne'

theorem circleQuillenClosedHolonomy_norm_one (fold : Fold) :
    ‖circleQuillenClosedHolonomy fold‖ = 1 := by
  rw [circleQuillenClosedHolonomy, norm_div, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos
      (circleDeterminantClutchingMultiplier_norm_pos fold),
    div_self (circleDeterminantClutchingMultiplier_norm_pos fold).ne']

theorem circleQuillen_transport_then_clutching
    (fold : Fold) (value : ℂ) :
    circleLargeGaugeFrameCoordinateTransition fold
        (circleQuillenParallelTransport fold 0 1 value) =
      circleQuillenClosedHolonomy fold * value := by
  rw [circleLargeGaugeFrameCoordinateTransition_apply,
    circleQuillenParallelTransport,
    circleQuillenParallelTransportScale_zero_one]
  simp [circleQuillenClosedHolonomy, div_eq_mul_inv]
  ring

/-! ## The regularized section and the connection -/

/-- Ordinary derivative of the regularized determinant coordinate
`2 sin (pi a)`. -/
def circleRegularizedDeterminantCoordinateDerivative (holonomy : ℝ) : ℝ :=
  2 * Real.pi * Real.cos (Real.pi * holonomy)

theorem circleRegularizedDeterminantCoordinate_hasDerivAt
    (holonomy : ℝ) :
    HasDerivAt determinantAmplitude
      (circleRegularizedDeterminantCoordinateDerivative holonomy) holonomy := by
  change HasDerivAt (fun x : ℝ => 2 * Real.sin (Real.pi * x))
    (2 * Real.pi * Real.cos (Real.pi * holonomy)) holonomy
  have hInner : HasDerivAt (fun x : ℝ => Real.pi * x) Real.pi holonomy := by
    simpa using (hasDerivAt_id holonomy).const_mul Real.pi
  have hSin := (Real.hasDerivAt_sin (Real.pi * holonomy)).comp holonomy hInner
  have hFinal : HasDerivAt (fun x : ℝ => 2 * Real.sin (Real.pi * x))
      (2 * (Real.cos (Real.pi * holonomy) * Real.pi)) holonomy := by
    simpa only [Function.comp_apply] using hSin.const_mul 2
  convert hFinal using 1
  ring

/-- Covariant derivative of the regularized section in the Fourier frame. -/
def circleRegularizedDeterminantCovariantDerivative
    (fold : Fold) (holonomy : ℝ) : ℂ :=
  circleQuillenConnectionAt fold
    (determinantAmplitude holonomy : ℂ)
    (circleRegularizedDeterminantCoordinateDerivative holonomy : ℂ)

theorem circleRegularizedDeterminantCovariantDerivative_formula
    (fold : Fold) (holonomy : ℝ) :
    circleRegularizedDeterminantCovariantDerivative fold holonomy =
      (circleRegularizedDeterminantCoordinateDerivative holonomy : ℂ) +
        (circleQuillenConnectionCoefficient fold : ℂ) *
          (determinantAmplitude holonomy : ℂ) := by
  rfl

@[simp] theorem circleRegularizedDeterminantCovariantDerivative_zero
    (fold : Fold) :
    circleRegularizedDeterminantCovariantDerivative fold 0 =
      (2 * Real.pi : ℝ) := by
  simp [circleRegularizedDeterminantCovariantDerivative,
    circleRegularizedDeterminantCoordinateDerivative,
    circleQuillenConnectionAt, determinantAmplitude]

theorem circleRegularizedDeterminantCovariantDerivative_half
    (fold : Fold) :
    circleRegularizedDeterminantCovariantDerivative fold (1 / 2) =
      (2 * circleQuillenConnectionCoefficient fold : ℝ) := by
  have hDerivative :
      circleRegularizedDeterminantCoordinateDerivative (1 / 2) = 0 := by
    rw [circleRegularizedDeterminantCoordinateDerivative,
      show Real.pi * (1 / 2 : ℝ) = Real.pi / 2 by ring,
      Real.cos_pi_div_two]
    ring
  rw [circleRegularizedDeterminantCovariantDerivative,
    circleQuillenConnectionAt, hDerivative, determinant_amplitude_at_half]
  push_cast
  ring

end

end P0EFTJanusCircleQuillenMetricFlatConnection
end JanusFormal
