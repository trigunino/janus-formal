import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleHeatSemigroupCompactness
import JanusFormal.Branches.FundamentalGeometryD7SpectralTheory.Gates.P0EFTJanusHeatRemainderConvergence

/-!
# Program P / D7 circle heat-regulator bridge

The quarter-twisted Program-P circle operator realizes, after the geometric
rescaling by `2 * pi / circlePeriod`, both D7 normal-root towers.  The negative
root is represented by the PT fold with the Fourier index reversed.

Consequently each fixed sphere-level block of the D7 separated heat operator
is a compact operator on the genuine Program-P circle Hilbert space and has
exactly the D7 separated Gaussian eigenvalue on every Fourier basis vector.
The final theorem combines this operator result with D7's explicit quadratic
cutoff-remainder obligation; it does not claim that obligation is proved here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD7CircleHeatRegulatorBridge

set_option autoImplicit false

noncomputable section

open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusGlobalSeparatedDiracModel
open P0EFTJanusRenormalizedSpectralDeterminant
open P0EFTJanusD2HeatCountertermBridge
open P0EFTJanusHeatRemainderConvergence
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleUnboundedDiracDomain
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusCircleHeatSemigroupOperator
open P0EFTJanusCircleHeatSemigroupCompactness

/-- The normal `Z4` root is the quarter-twisted circle spectrum. -/
def quarterTwist : CircleTwist where
  value := 1 / 4
  nonnegative := by norm_num
  le_one := by norm_num

/-- Conversion from the dimensionless Program-P circle operator to the D7
operator on a circle of geometric period `circlePeriod`. -/
def d7CircleScale (data : ProductThroatSpectralData) : ℝ :=
  2 * Real.pi / data.circlePeriod

theorem d7CircleScale_pos (data : ProductThroatSpectralData) :
    0 < d7CircleScale data := by
  exact div_pos (mul_pos (by norm_num) Real.pi_pos)
    data.circlePeriodPositive

/-- The two D7 roots use the two PT-related Program-P folds. -/
def programPFold : NormalRootChoice → Fold
  | .positiveQuarter => .positive
  | .negativeQuarter => .pt

/-- Reindexing needed for the negative-quarter tower. -/
def programPMode : NormalRootChoice → ℤ → ℤ
  | .positiveQuarter, mode => mode
  | .negativeQuarter, mode => -mode

/-- Exact first-order spectral identification, including the geometric scale. -/
theorem d7_circleEigenvalue_eq_scaled_programP
    (data : ProductThroatSpectralData)
    (choice : NormalRootChoice) (mode : ℤ) :
    circleEigenvalue data choice mode =
      d7CircleScale data *
        diracEigenvalue (programPFold choice) quarterTwist
          (programPMode choice mode) := by
  cases choice <;>
    simp [circleEigenvalue, d7CircleScale, programPFold, programPMode,
      quarterTwist, normalRootModeNumerator, diracEigenvalue,
      Fold.spectralSign, baseEigenvalue] <;>
    field_simp [ne_of_gt data.circlePeriodPositive] <;>
    ring

/-- D7 heat time expressed in the dimensionless Program-P normalization. -/
def programPHeatTime
    (data : ProductThroatSpectralData) (time : HeatTime) : HeatTime :=
  ⟨time.1 * d7CircleScale data ^ 2,
    mul_pos time.2 (sq_pos_of_pos (d7CircleScale_pos data))⟩

/-- The D7 Gaussian weight of one circle mode. -/
def d7CircleHeatWeight
    (data : ProductThroatSpectralData) (time : HeatTime)
    (choice : NormalRootChoice) (mode : ℤ) : ℝ :=
  Real.exp (-time.1 * circleEigenvalue data choice mode ^ 2)

/-- The Program-P circle heat multiplier is exactly the D7 normal-root
Gaussian after time rescaling and PT reindexing. -/
theorem programP_heatWeight_eq_d7_circleHeatWeight
    (data : ProductThroatSpectralData) (time : HeatTime)
    (choice : NormalRootChoice) (mode : ℤ) :
    heatWeight (programPHeatTime data time) (programPFold choice)
        quarterTwist (programPMode choice mode) =
      d7CircleHeatWeight data time choice mode := by
  rw [d7CircleHeatWeight, heatWeight,
    d7_circleEigenvalue_eq_scaled_programP]
  simp only [programPHeatTime, eigenvalueSq]
  congr 1
  ring

/-- The genuine Program-P operator realizing one D7 circle root tower. -/
def d7CircleHeatOperator
    (data : ProductThroatSpectralData) (time : HeatTime)
    (choice : NormalRootChoice) : CircleHilbert →L[ℂ] CircleHilbert :=
  circleHeatSemigroup (heatTimeToSemigroupTime (programPHeatTime data time))
    (programPFold choice) quarterTwist

theorem d7CircleHeatOperator_isCompact
    (data : ProductThroatSpectralData) (time : HeatTime)
    (choice : NormalRootChoice) :
    IsCompactOperator (d7CircleHeatOperator data time choice) := by
  exact circleHeatSemigroup_isCompact (programPHeatTime data time)
    (programPFold choice) quarterTwist

/-- One fixed sphere-level block of the separated D7 heat operator. -/
def d7SeparatedLevelHeatOperator
    (data : ProductThroatSpectralData) (time : HeatTime)
    (level : ℕ) (choice : NormalRootChoice) :
    CircleHilbert →L[ℂ] CircleHilbert :=
  (Real.exp (-time.1 * sphereEigenvalueSquared data level) : ℂ) •
    d7CircleHeatOperator data time choice

theorem d7SeparatedLevelHeatOperator_isCompact
    (data : ProductThroatSpectralData) (time : HeatTime)
    (level : ℕ) (choice : NormalRootChoice) :
    IsCompactOperator
      (d7SeparatedLevelHeatOperator data time level choice) := by
  unfold d7SeparatedLevelHeatOperator
  exact (d7CircleHeatOperator_isCompact data time choice).smul
    (Real.exp (-time.1 * sphereEigenvalueSquared data level) : ℂ)

/-- The full separated D7 heat weight for one mode. -/
def d7SeparatedModeHeatWeight
    (data : ProductThroatSpectralData) (time : HeatTime)
    (level : ℕ) (choice : NormalRootChoice) (mode : ℤ) : ℝ :=
  Real.exp (-time.1 * productDiracEigenvalueSquared data
    { sphereLevel := level, circleMode := mode, rootChoice := choice })

/-- Exact action of the compact level block on every reindexed Fourier mode. -/
theorem d7SeparatedLevelHeatOperator_on_basis
    (data : ProductThroatSpectralData) (time : HeatTime)
    (level : ℕ) (choice : NormalRootChoice) (mode : ℤ) :
    d7SeparatedLevelHeatOperator data time level choice
        (circleFourierBasis (programPMode choice mode)) =
      (d7SeparatedModeHeatWeight data time level choice mode : ℂ) •
        circleFourierBasis (programPMode choice mode) := by
  change
    (Real.exp (-time.1 * sphereEigenvalueSquared data level) : ℂ) •
      d7CircleHeatOperator data time choice
        (circleFourierBasis (programPMode choice mode)) = _
  rw [d7CircleHeatOperator, circleHeatSemigroup_on_basis]
  rw [circleHeatMultiplier_of_heatTime_eq_operatorHeatWeight]
  rw [circleOperatorHeatWeight_eq_heatWeight,
    programP_heatWeight_eq_d7_circleHeatWeight]
  simp only [d7SeparatedModeHeatWeight, d7CircleHeatWeight,
    productDiracEigenvalueSquared]
  rw [smul_smul]
  have hCoefficient :
      (Real.exp (-time.1 * sphereEigenvalueSquared data level) : ℂ) *
          (Real.exp (-time.1 * circleEigenvalue data choice mode ^ 2) : ℂ) =
        (Real.exp (-time.1 *
          (sphereEigenvalueSquared data level +
            circleEigenvalue data choice mode ^ 2)) : ℂ) := by
    norm_cast
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hCoefficient]

/-- Program-P supplies compact fixed-level heat blocks unconditionally.  If
D7's explicit quadratic shell estimate is also proved, the same spectral data
has a closed renormalized determinant with a fixed local subtraction scheme. -/
theorem circle_compactness_and_quadratic_remainder_close_d7_regulator
    {data : ProductThroatSpectralData}
    {coefficients : HeatCountertermCoefficients}
    (bound : HeatRemainderQuadraticBound data coefficients) :
    (∀ time : HeatTime, ∀ level : ℕ, ∀ choice : NormalRootChoice,
      IsCompactOperator
        (d7SeparatedLevelHeatOperator data time level choice)) ∧
      RenormalizedDeterminantClosureCertificate data := by
  exact ⟨fun time level choice =>
    d7SeparatedLevelHeatOperator_isCompact data time level choice,
    quadratic_heat_bound_closes_d2_determinant bound⟩

end

end P0EFTJanusProgramPD7CircleHeatRegulatorBridge
end JanusFormal
