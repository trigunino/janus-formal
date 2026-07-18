import JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly.Gates.P0EFTJanusCircleQuillenMetricFlatConnection

/-!
# Exact zeros and simple crossings of the circle determinant section

In the closed fundamental holonomy interval, the regularized determinant
section vanishes exactly at the two endpoint representatives.  Both zeros are
simple in the Fourier coordinate.  The nonvanishing of the crossing tangent is
preserved by the existing clutching map and by the chosen flat parallel
transport.  No identification with a global Quillen/Bismut--Freed connection
is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusCircleDeterminantSectionCrossings

set_option autoImplicit false

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleBoundedTransformSpectralFlow
open P0EFTJanusCircleDeterminantLineFamily
open P0EFTJanusCircleDeterminantTopologicalBundle
open P0EFTJanusCircleQuillenMetricFlatConnection
open P0EFTJanusCircleHolonomyEta

/-- The regularized determinant section has no zeros other than the two
endpoint representatives of the fundamental interval. -/
theorem circleRegularizedDeterminantSection_eq_zero_iff
    (fold : Fold) (twist : CircleTwist) :
    circleRegularizedDeterminantSection fold twist = 0 ↔
      twist.value = 0 ∨ twist.value = 1 := by
  constructor
  · intro hZero
    by_cases hValueZero : twist.value = 0
    · exact Or.inl hValueZero
    · by_cases hValueOne : twist.value = 1
      · exact Or.inr hValueOne
      · exfalso
        have hPositive : 0 < twist.value :=
          lt_of_le_of_ne twist.nonnegative (Ne.symm hValueZero)
        have hLess : twist.value < 1 :=
          lt_of_le_of_ne twist.le_one hValueOne
        exact (circleRegularizedDeterminantSection_ne_zero_of_interior
          fold twist hPositive hLess) hZero
  · intro hEndpoint
    rcases hEndpoint with hZero | hOne
    · have hTwist : twist = periodicTwist :=
        circleTwist_value_injective (by simpa [periodicTwist] using hZero)
      subst twist
      exact circleRegularizedDeterminantSection_periodic fold
    · have hTwist : twist = unitCircleTwist :=
        circleTwist_value_injective (by simpa [unitCircleTwist] using hOne)
      subst twist
      exact circleRegularizedDeterminantSection_unit fold

@[simp] theorem circleRegularizedDeterminantCoordinateDerivative_zero :
    circleRegularizedDeterminantCoordinateDerivative 0 = 2 * Real.pi := by
  simp [circleRegularizedDeterminantCoordinateDerivative]

@[simp] theorem circleRegularizedDeterminantCoordinateDerivative_one :
    circleRegularizedDeterminantCoordinateDerivative 1 = -2 * Real.pi := by
  simp [circleRegularizedDeterminantCoordinateDerivative]

theorem circleRegularizedDeterminantCoordinateDerivative_zero_ne :
    circleRegularizedDeterminantCoordinateDerivative 0 ≠ 0 := by
  rw [circleRegularizedDeterminantCoordinateDerivative_zero]
  positivity

theorem circleRegularizedDeterminantCoordinateDerivative_one_ne :
    circleRegularizedDeterminantCoordinateDerivative 1 ≠ 0 := by
  rw [circleRegularizedDeterminantCoordinateDerivative_one]
  positivity

/-- Both endpoint zeros are simple in the explicit Fourier coordinate. -/
theorem circleRegularizedDeterminantCoordinate_simple_endpoint_crossings :
    circleRegularizedDeterminantCoordinateDerivative 0 ≠ 0 ∧
      circleRegularizedDeterminantCoordinateDerivative 1 ≠ 0 :=
  ⟨circleRegularizedDeterminantCoordinateDerivative_zero_ne,
    circleRegularizedDeterminantCoordinateDerivative_one_ne⟩

theorem circleRegularizedDeterminantCovariantDerivative_one
    (fold : Fold) :
    circleRegularizedDeterminantCovariantDerivative fold 1 =
      (-2 * Real.pi : Real) := by
  rw [circleRegularizedDeterminantCovariantDerivative_formula,
    circleRegularizedDeterminantCoordinateDerivative_one]
  simp [determinantAmplitude]

theorem circleRegularizedDeterminantCovariantDerivative_one_ne
    (fold : Fold) :
    circleRegularizedDeterminantCovariantDerivative fold 1 ≠ 0 := by
  rw [circleRegularizedDeterminantCovariantDerivative_one]
  apply Complex.ofReal_ne_zero.mpr
  rw [← circleRegularizedDeterminantCoordinateDerivative_one]
  exact circleRegularizedDeterminantCoordinateDerivative_one_ne

/-- The chosen connection sees simple crossings at both endpoints because its
zeroth-order term vanishes with the section. -/
theorem circleRegularizedDeterminantCovariantDerivative_endpoint_ne_zero
    (fold : Fold) :
    circleRegularizedDeterminantCovariantDerivative fold 0 ≠ 0 ∧
      circleRegularizedDeterminantCovariantDerivative fold 1 ≠ 0 := by
  constructor
  · rw [circleRegularizedDeterminantCovariantDerivative_zero]
    apply Complex.ofReal_ne_zero.mpr
    rw [← circleRegularizedDeterminantCoordinateDerivative_zero]
    exact circleRegularizedDeterminantCoordinateDerivative_zero_ne
  · exact circleRegularizedDeterminantCovariantDerivative_one_ne fold

theorem circleLargeGaugeFrameCoordinateTransition_eq_zero_iff
    (fold : Fold) (value : ℂ) :
    circleLargeGaugeFrameCoordinateTransition fold value = 0 ↔ value = 0 := by
  rw [circleLargeGaugeFrameCoordinateTransition_apply, mul_eq_zero]
  simp [circleDeterminantClutchingMultiplier_ne_zero fold]

theorem circleQuillenParallelTransport_eq_zero_iff
    (fold : Fold) (first second : Real) (value : ℂ) :
    circleQuillenParallelTransport fold first second value = 0 ↔ value = 0 := by
  rw [circleQuillenParallelTransport, mul_eq_zero]
  simp [(circleQuillenParallelTransportScale_pos fold first second).ne']

/-- Clutching preserves the nonzero crossing tangent and hence its simple
multiplicity. -/
theorem circleEndpointCrossing_clutching_ne_zero (fold : Fold) :
    circleLargeGaugeFrameCoordinateTransition fold
      (circleRegularizedDeterminantCoordinateDerivative 1 : ℂ) ≠ 0 := by
  rw [ne_eq, circleLargeGaugeFrameCoordinateTransition_eq_zero_iff]
  exact_mod_cast circleRegularizedDeterminantCoordinateDerivative_one_ne

/-- Parallel transport preserves the nonzero crossing tangent and hence its
simple multiplicity. -/
theorem circleEndpointCrossing_parallelTransport_ne_zero (fold : Fold) :
    circleQuillenParallelTransport fold 0 1
      (circleRegularizedDeterminantCoordinateDerivative 0 : ℂ) ≠ 0 := by
  rw [ne_eq, circleQuillenParallelTransport_eq_zero_iff]
  exact_mod_cast circleRegularizedDeterminantCoordinateDerivative_zero_ne

/-- Transport followed by clutching still preserves the simple crossing. -/
theorem circleEndpointCrossing_transport_then_clutching_ne_zero (fold : Fold) :
    circleLargeGaugeFrameCoordinateTransition fold
      (circleQuillenParallelTransport fold 0 1
        (circleRegularizedDeterminantCoordinateDerivative 0 : ℂ)) ≠ 0 := by
  rw [ne_eq, circleLargeGaugeFrameCoordinateTransition_eq_zero_iff,
    circleQuillenParallelTransport_eq_zero_iff]
  exact_mod_cast circleRegularizedDeterminantCoordinateDerivative_zero_ne

end
end P0EFTJanusCircleDeterminantSectionCrossings
end JanusFormal
