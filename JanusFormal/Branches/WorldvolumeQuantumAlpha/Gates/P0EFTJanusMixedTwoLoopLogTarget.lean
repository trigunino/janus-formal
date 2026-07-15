import Mathlib
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusMixedGaugeScalarLoopOrder

namespace JanusFormal.P0EFTJanusMixedTwoLoopLogTarget

set_option autoImplicit false

open P0EFTJanusMixedGaugeScalarLoopOrder

/-- The minimal genuinely mixed member has one scalar line, two loops and
superficial degree four. -/
theorem minimal_mixed_graph_data :
    (unboundedMixedFamily 1).scalarInternalLines = 1 ∧
    (unboundedMixedFamily 1).loops = 2 ∧
    (unboundedMixedFamily 1).superficialDegree = 4 := by
  norm_num [unboundedMixedFamily]

/-- Two linear background vertices contribute `v^-6`, while two UV Maxwell
propagators contribute `v^4`; the net prefactor is `v^-2`.  The logarithmic
term selected by degree four is therefore proportional to
`v^-2 * m_CS^4 = kappa^4 v^6`. -/
theorem mixed_log_has_sextic_background_shape
    (v kappa topologicalMass : ℝ)
    (hV : v ≠ 0)
    (hMass : topologicalMass = kappa * v ^ 2) :
    v⁻¹ ^ 2 * topologicalMass ^ 4 = kappa ^ 4 * v ^ 6 := by
  rw [hMass]
  field_simp

/-- A degree-four polynomial in a gauge mass (dimension one) and a scalar
mass-squared (dimension two) has exactly these three exponent pairs. -/
theorem degree_four_mass_monomial_basis
    (gaugeMassPower scalarMassSquaredPower : ℕ)
    (hDegree : gaugeMassPower + 2 * scalarMassSquaredPower = 4) :
    (gaugeMassPower = 4 ∧ scalarMassSquaredPower = 0) ∨
    (gaugeMassPower = 2 ∧ scalarMassSquaredPower = 1) ∨
    (gaugeMassPower = 0 ∧ scalarMassSquaredPower = 2) := by
  omega

theorem mixed_gauge_scalar_mass_log_is_sextic
    (v kappa lambda6 gaugeMass scalarMassSquared : ℝ)
    (hV : v ≠ 0)
    (hGauge : gaugeMass = kappa * v ^ 2)
    (hScalar : scalarMassSquared = lambda6 * v ^ 4) :
    v⁻¹ ^ 2 * gaugeMass ^ 2 * scalarMassSquared =
      kappa ^ 2 * lambda6 * v ^ 6 := by
  rw [hGauge, hScalar]
  field_simp

theorem scalar_mass_squared_log_is_sextic
    (v lambda6 scalarMassSquared : ℝ)
    (hV : v ≠ 0)
    (hScalar : scalarMassSquared = lambda6 * v ^ 4) :
    v⁻¹ ^ 2 * scalarMassSquared ^ 2 = lambda6 ^ 2 * v ^ 6 := by
  rw [hScalar]
  field_simp

/-- Conditional coefficient obtained from the transverse MCS numerator,
sunset remainder `m_eta^4/4`, two gauge Wick contractions, and the universal
3D sunset pole `1/(64*pi^2)`. -/
theorem conditional_mixed_ms_beta_coefficient :
    4 * (6 * (25 / (256 * Real.pi ^ 2))) =
      75 / (32 * Real.pi ^ 2) := by
  ring

/-- Adding the independently normalized pure-scalar coefficient gives the
conditional non-LL two-loop coefficient. -/
theorem conditional_non_ll_ms_beta_coefficient :
    25 / (2 * Real.pi ^ 2) + 75 / (32 * Real.pi ^ 2) =
      475 / (32 * Real.pi ^ 2) := by
  ring

structure MixedTwoLoopResidueStatus where
  tensorNumeratorReduced : Prop
  gaugeParameterCancellationProved : Prop
  powerSubdivergencesSubtracted : Prop
  fourthMassOrderLogResidueComputed : Prop
  regulatorCrossCheckCompleted : Prop

def mixedTwoLoopResidueClosed (s : MixedTwoLoopResidueStatus) : Prop :=
  s.tensorNumeratorReduced ∧
  s.gaugeParameterCancellationProved ∧
  s.powerSubdivergencesSubtracted ∧
  s.fourthMassOrderLogResidueComputed ∧
  s.regulatorCrossCheckCompleted

end JanusFormal.P0EFTJanusMixedTwoLoopLogTarget
