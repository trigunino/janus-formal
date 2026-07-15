import Mathlib

namespace JanusFormal.P0EFTJanusQuadraticBosonicNoGhost

set_option autoImplicit false

/-- Reduced physical quadratic coefficients after gauge and LL constraints.
This does not assume that the reduction itself has already been derived. -/
structure ReducedQuadraticBosonicData where
  scalarWaveCoefficient : ℝ
  transverseGaugeCoefficient : ℝ
  scalarMassSquared : ℝ
  scalarWaveCoefficientPositive : 0 < scalarWaveCoefficient
  transverseGaugeCoefficientPositive : 0 < transverseGaugeCoefficient
  scalarMassSquaredNonnegative : 0 ≤ scalarMassSquared

def quadraticEnergy
    (s : ReducedQuadraticBosonicData)
    (scalarMode transverseGaugeMode : ℝ) : ℝ :=
  s.scalarWaveCoefficient * scalarMode ^ 2 +
    s.transverseGaugeCoefficient * transverseGaugeMode ^ 2 +
    s.scalarMassSquared * scalarMode ^ 2

theorem quadratic_energy_nonnegative
    (s : ReducedQuadraticBosonicData)
    (scalarMode transverseGaugeMode : ℝ) :
    0 ≤ quadraticEnergy s scalarMode transverseGaugeMode := by
  unfold quadraticEnergy
  exact add_nonneg
    (add_nonneg
      (mul_nonneg (le_of_lt s.scalarWaveCoefficientPositive)
        (sq_nonneg scalarMode))
      (mul_nonneg (le_of_lt s.transverseGaugeCoefficientPositive)
        (sq_nonneg transverseGaugeMode)))
    (mul_nonneg s.scalarMassSquaredNonnegative (sq_nonneg scalarMode))

/-- Positive kinetic residues imply that zero quadratic energy contains no
nontrivial scalar or transverse gauge mode. -/
theorem quadratic_energy_zero_iff_modes_zero
    (s : ReducedQuadraticBosonicData)
    (scalarMode transverseGaugeMode : ℝ) :
    quadraticEnergy s scalarMode transverseGaugeMode = 0 ↔
      scalarMode = 0 ∧ transverseGaugeMode = 0 := by
  constructor
  · intro hEnergy
    have hScalarTerm :
        0 ≤ s.scalarMassSquared * scalarMode ^ 2 :=
      mul_nonneg s.scalarMassSquaredNonnegative (sq_nonneg scalarMode)
    have hScalarWave :
        0 ≤ s.scalarWaveCoefficient * scalarMode ^ 2 :=
      mul_nonneg (le_of_lt s.scalarWaveCoefficientPositive)
        (sq_nonneg scalarMode)
    have hGaugeWave :
        0 ≤ s.transverseGaugeCoefficient * transverseGaugeMode ^ 2 := by
      exact mul_nonneg (le_of_lt s.transverseGaugeCoefficientPositive)
        (sq_nonneg transverseGaugeMode)
    have hScalarSquare : scalarMode ^ 2 = 0 := by
      unfold quadraticEnergy at hEnergy
      nlinarith [sq_nonneg scalarMode, sq_nonneg transverseGaugeMode,
        s.scalarWaveCoefficientPositive]
    have hGaugeSquare : transverseGaugeMode ^ 2 = 0 := by
      unfold quadraticEnergy at hEnergy
      nlinarith [sq_nonneg scalarMode, sq_nonneg transverseGaugeMode,
        s.transverseGaugeCoefficientPositive]
    exact ⟨sq_eq_zero_iff.mp hScalarSquare, sq_eq_zero_iff.mp hGaugeSquare⟩
  · rintro ⟨rfl, rfl⟩
    norm_num [quadraticEnergy]

/-- Honest frontier: a bosonic residue proof is weaker than BRST/unitarity
closure of the full constrained quantum theory. -/
structure NoGhostClosureStatus where
  llDiracConstraintReductionDerived : Prop
  gaugeFixedQuadraticOperatorDerived : Prop
  scalarResiduePositive : Prop
  transverseGaugeResiduePositive : Prop
  faddeevPopovSectorUnitary : Prop
  reflectionPositivityOrLorentzianUnitarityProved : Prop

def noGhostClosure (s : NoGhostClosureStatus) : Prop :=
  s.llDiracConstraintReductionDerived ∧
  s.gaugeFixedQuadraticOperatorDerived ∧
  s.scalarResiduePositive ∧
  s.transverseGaugeResiduePositive ∧
  s.faddeevPopovSectorUnitary ∧
  s.reflectionPositivityOrLorentzianUnitarityProved

end JanusFormal.P0EFTJanusQuadraticBosonicNoGhost
