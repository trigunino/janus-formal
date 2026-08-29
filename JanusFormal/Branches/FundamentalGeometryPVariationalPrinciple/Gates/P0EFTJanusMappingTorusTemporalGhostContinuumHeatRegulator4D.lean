import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleHeatNuclearTraceClass
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCircleHeatSemigroupCompactness
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusInfiniteTemporalH1ZeroModeCohomology4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteModeCommonPhysicalGhostHeatRegulator4D

/-!
# Continuum heat regulator for the temporal gauge ghost

The completed, spatially constant temporal ghost already has an exact Fourier
derivative and `H1` coefficient Hilbert space.  Rescaling the existing
periodic-circle heat operator by `(2*pi/T)^2` therefore gives its genuine heat
operator.  This gate records the exact derivative spectrum, compactness,
nuclear decomposition, PT cancellation, and the previously proved zero-mode
cohomology.

This is one concrete ghost block, not the full diffeomorphism/U(1) ghost
complex and not the complete common regulator.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusTemporalGhostContinuumHeatRegulator4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusCircleDiracHeatFunctionalBridge
open P0EFTJanusCircleHeatSemigroupOperator
open P0EFTJanusCircleHeatSemigroupCompactness
open P0EFTJanusCircleHeatNuclearTraceClass
open P0EFTJanusFiniteModeCommonPhysicalGhostHeatRegulator4D
open P0EFTJanusMappingTorusFiniteTemporalFourierGaugeGhostCohomology4D
open P0EFTJanusMappingTorusInfiniteTemporalFourierSobolevBridge4D
open P0EFTJanusMappingTorusInfiniteTemporalH1ZeroModeCohomology4D

variable (period : Real) [hPeriodPos : Fact (0 < period)]

/-- Conversion from the unit-circle squared spectrum to the physical temporal
derivative spectrum. -/
def temporalGhostHeatScale : Real :=
  (2 * Real.pi / period) ^ 2

theorem temporalGhostHeatScale_pos :
    0 < temporalGhostHeatScale period := by
  unfold temporalGhostHeatScale
  exact sq_pos_of_pos
    (div_pos (mul_pos (by norm_num) Real.pi_pos) hPeriodPos.out)

/-- Positive circle heat time corresponding to physical regulator time. -/
def temporalGhostCircleHeatTime (time : HeatTime) : HeatTime :=
  ⟨time.1 * temporalGhostHeatScale period,
    mul_pos time.2 (temporalGhostHeatScale_pos period)⟩

/-- The actual temporal Fourier derivative spectrum is the rescaled periodic
circle spectrum. -/
theorem temporalGhostDerivativeSpectrum_eq_scaled_circle
    (mode : Int) :
    Complex.normSq (temporalFourierDerivativeMultiplier period mode) =
      temporalGhostHeatScale period *
        circleOperatorSquaredEigenvalue .positive periodicTwist mode := by
  have hPeriod : period ≠ 0 := ne_of_gt hPeriodPos.out
  rw [temporalFourierDerivativeMultiplier, Complex.normSq_div]
  simp only [Complex.normSq_mul, Complex.normSq_ofReal, Complex.normSq_I,
    Complex.normSq_intCast, mul_one]
  rw [circleOperatorSquaredEigenvalue_eq_eigenvalueSq]
  simp only [eigenvalueSq, diracEigenvalue, Fold.positive_spectralSign,
    one_mul, baseEigenvalue, periodicTwist, add_zero]
  unfold temporalGhostHeatScale
  field_simp
  norm_num [Complex.normSq]
  ring

/-- Genuine bounded heat operator on the completed temporal `H1` ghost
coordinates. -/
def temporalGhostHeatOperator (time : HeatTime) :
    TemporalH1CoefficientHilbert period →L[Complex]
      TemporalH1CoefficientHilbert period :=
  circleHeatSemigroup
    (heatTimeToSemigroupTime (temporalGhostCircleHeatTime period time))
    .positive periodicTwist

@[simp]
theorem temporalGhostHeatOperator_apply
    (time : HeatTime) (state : TemporalH1CoefficientHilbert period)
    (mode : Int) :
    temporalGhostHeatOperator period time state mode =
      (Real.exp
        (-time.1 *
          Complex.normSq
            (temporalFourierDerivativeMultiplier period mode)) : Complex) *
        state mode := by
  rw [temporalGhostHeatOperator, circleHeatSemigroup_apply]
  unfold circleHeatMultiplier temporalGhostCircleHeatTime
    heatTimeToSemigroupTime
  rw [temporalGhostDerivativeSpectrum_eq_scaled_circle period mode]
  congr 2
  ring_nf

theorem temporalGhostHeatOperator_norm_apply_le
    (time : HeatTime) (state : TemporalH1CoefficientHilbert period) :
    ‖temporalGhostHeatOperator period time state‖ ≤ ‖state‖ :=
  circleHeatSemigroup_norm_apply_le
    (heatTimeToSemigroupTime (temporalGhostCircleHeatTime period time))
    .positive periodicTwist state

/-- At every positive physical time, the temporal ghost heat operator is
compact. -/
theorem temporalGhostHeatOperator_isCompact (time : HeatTime) :
    IsCompactOperator (temporalGhostHeatOperator period time) :=
  circleHeatSemigroup_isCompact
    (temporalGhostCircleHeatTime period time) .positive periodicTwist

/-- The temporal ghost heat operator inherits the explicit rank-one nuclear
decomposition of the circle heat operator. -/
def temporalGhostHeatNuclearCertificate (time : HeatTime) :
    CircleHeatNuclearCertificate
      (temporalGhostCircleHeatTime period time) .positive periodicTwist :=
  circleHeatNuclearCertificate
    (temporalGhostCircleHeatTime period time) .positive periodicTwist

/-- Statistics- and multiplicity-weighted PT-paired continuum chiral trace. -/
def temporalGhostSignedPairedChiralTrace
    (time : HeatTime) (multiplicity : Nat) : Real :=
  (multiplicity : Real) * statisticsSign .ghost *
    pairedRegulatedChiralTrace
      (temporalGhostCircleHeatTime period time) periodicTwist

theorem temporalGhostSignedPairedChiralTrace_eq_zero
    (time : HeatTime) (multiplicity : Nat) :
    temporalGhostSignedPairedChiralTrace period time multiplicity = 0 := by
  rw [temporalGhostSignedPairedChiralTrace,
    pairedRegulatedChiralTrace_eq_zero]
  ring

/-- The same signed PT cancellation is exact at every symmetric cutoff. -/
theorem temporalGhostSignedCutoffChiralTrace_eq_zero
    (cutoff : Nat) (time : HeatTime) (multiplicity : Nat) :
    (multiplicity : Real) * statisticsSign .ghost *
        (cutoffChiralHeatTrace cutoff
            (temporalGhostCircleHeatTime period time) .positive periodicTwist +
          cutoffChiralHeatTrace cutoff
            (temporalGhostCircleHeatTime period time) .pt periodicTwist) =
      0 := by
  rw [cutoffChiralHeatTrace_positive_add_pt_eq_zero]
  ring

/-- Certificate for the completed spatially constant temporal ghost block. -/
structure TemporalGhostContinuumHeatRegulatorCertificate4D
    (time : HeatTime) : Prop where
  derivative_spectrum :
    ∀ mode : Int,
      Complex.normSq (temporalFourierDerivativeMultiplier period mode) =
        temporalGhostHeatScale period *
          circleOperatorSquaredEigenvalue .positive periodicTwist mode
  compact :
    IsCompactOperator (temporalGhostHeatOperator period time)
  nuclear :
    Nonempty
      (CircleHeatNuclearCertificate
        (temporalGhostCircleHeatTime period time) .positive periodicTwist)
  zero_mode_exact :
    LinearMap.ker
        (temporalH1DerivativeCoefficientOperator period).toLinearMap =
      LinearMap.range
        (temporalH1ZeroModeCoefficientOperator period).toLinearMap
  signed_pt_trace_zero :
    ∀ multiplicity : Nat,
      temporalGhostSignedPairedChiralTrace period time multiplicity = 0
  signed_cutoff_zero :
    ∀ cutoff multiplicity : Nat,
      (multiplicity : Real) * statisticsSign .ghost *
          (cutoffChiralHeatTrace cutoff
              (temporalGhostCircleHeatTime period time) .positive
              periodicTwist +
            cutoffChiralHeatTrace cutoff
              (temporalGhostCircleHeatTime period time) .pt periodicTwist) =
        0

def temporalGhostContinuumHeatRegulatorCertificate4D
    (time : HeatTime) :
    TemporalGhostContinuumHeatRegulatorCertificate4D period time where
  derivative_spectrum :=
    temporalGhostDerivativeSpectrum_eq_scaled_circle period
  compact := temporalGhostHeatOperator_isCompact period time
  nuclear := ⟨temporalGhostHeatNuclearCertificate period time⟩
  zero_mode_exact :=
    temporalH1DerivativeCoefficient_kernel_eq_zeroMode_range period
  signed_pt_trace_zero :=
    temporalGhostSignedPairedChiralTrace_eq_zero period time
  signed_cutoff_zero :=
    fun cutoff multiplicity =>
      temporalGhostSignedCutoffChiralTrace_eq_zero
        period cutoff time multiplicity

end

end P0EFTJanusMappingTorusTemporalGhostContinuumHeatRegulator4D
end JanusFormal
