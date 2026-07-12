import Mathlib
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusCondensateToAlphaMap

namespace JanusFormal
namespace P0EFTJanusMaxwellChernSimonsChargeNormalization

set_option autoImplicit false

open P0EFTJanusCondensateToAlphaMap

/--
A compact Maxwell--Chern--Simons normalization on the `2+1` dimensional LL
world-volume.

The scalar composite `sigma` has mass dimension one.  With Maxwell coefficient
`1/(4 sigma)` and Chern--Simons level magnitude `K`, the topological mass obeys

`2*pi*m_CS = K*sigma`.

The candidate identification `q_LL = m_CS^2` then has exactly the mass dimension
two required by the primitive LL law `16*q_LL^2*A^4 = 1`.
-/
structure MaxwellChernSimonsLLScale where
  levelMagnitude : ℝ
  condensateMass : ℝ
  topologicalMass : ℝ
  chargeUnit : ℝ
  alphaSquaredLength : ℝ
  levelMagnitudePositive : 0 < levelMagnitude
  condensateMassPositive : 0 < condensateMass
  topologicalMassPositive : 0 < topologicalMass
  alphaSquaredLengthPositive : 0 < alphaSquaredLength
  topologicalMassLaw :
    2 * Real.pi * topologicalMass =
      levelMagnitude * condensateMass
  chargeFromTopologicalMass :
    chargeUnit = topologicalMass ^ 2
  primitiveFluxRadiusLaw :
    16 * chargeUnit ^ 2 * alphaSquaredLength ^ 4 = 1

/-- Reuse the generic positive condensate/charge theorem with unit amplitude. -/
def asTopologicalMassChargeAlpha
    (s : MaxwellChernSimonsLLScale) : CondensateChargeAlpha :=
  { condensateMass := s.topologicalMass
    chargeAmplitude := 1
    chargeUnit := s.chargeUnit
    alphaSquaredLength := s.alphaSquaredLength
    condensateMassPositive := s.topologicalMassPositive
    chargeAmplitudePositive := by norm_num
    alphaSquaredLengthPositive := s.alphaSquaredLengthPositive
    chargeFromCondensate := by
      simpa using s.chargeFromTopologicalMass
    primitiveFluxRadiusLaw := s.primitiveFluxRadiusLaw }

/-- Primitive LL flux gives `2*m_CS*A = 1`. -/
theorem topological_mass_alpha_law
    (s : MaxwellChernSimonsLLScale) :
    2 * s.topologicalMass * s.alphaSquaredLength = 1 := by
  exact unit_amplitude_condensate_alpha_law
    (asTopologicalMassChargeAlpha s) rfl

/--
The Chern--Simons level fixes the formerly free charge amplitude:

`K * sigma * A = pi`.
-/
theorem level_condensate_alpha_law
    (s : MaxwellChernSimonsLLScale) :
    s.levelMagnitude * s.condensateMass *
        s.alphaSquaredLength = Real.pi := by
  calc
    s.levelMagnitude * s.condensateMass *
        s.alphaSquaredLength =
      (2 * Real.pi * s.topologicalMass) *
        s.alphaSquaredLength := by
          rw [s.topologicalMassLaw]
    _ = Real.pi *
        (2 * s.topologicalMass * s.alphaSquaredLength) := by ring
    _ = Real.pi := by
      rw [topological_mass_alpha_law s]
      ring

/-- A primitive unit level gives the particularly simple law `sigma*A = pi`. -/
theorem unit_level_condensate_alpha_law
    (s : MaxwellChernSimonsLLScale)
    (hUnit : s.levelMagnitude = 1) :
    s.condensateMass * s.alphaSquaredLength = Real.pi := by
  have hLaw := level_condensate_alpha_law s
  rw [hUnit] at hLaw
  norm_num at hLaw ⊢
  exact hLaw

/--
The integer level must come from the compact gauge bundle and parity-anomaly
condition; the identification of `q_LL` with the squared topological mass is a
physical normalization theorem to be checked in the full world-volume action.
-/
structure MCSNormalizationStatus where
  compactU1BundleDerived : Prop
  integerChernSimonsLevelDerived : Prop
  scalarDressedMaxwellCoefficientDerived : Prop
  topologicalPoleMassComputed : Prop
  llChargeEqualsPoleMassSquaredDerived : Prop
  parityAnomalyConsistent : Prop
  primitiveLevelOrSectorSelected : Prop
  noObservedScaleImported : Prop


def mcsNormalizationClosed (s : MCSNormalizationStatus) : Prop :=
  s.compactU1BundleDerived /\
  s.integerChernSimonsLevelDerived /\
  s.scalarDressedMaxwellCoefficientDerived /\
  s.topologicalPoleMassComputed /\
  s.llChargeEqualsPoleMassSquaredDerived /\
  s.parityAnomalyConsistent /\
  s.primitiveLevelOrSectorSelected /\
  s.noObservedScaleImported

end P0EFTJanusMaxwellChernSimonsChargeNormalization
end JanusFormal
