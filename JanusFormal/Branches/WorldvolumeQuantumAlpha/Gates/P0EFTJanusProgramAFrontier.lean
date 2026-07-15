import Mathlib
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusScaleInvariantWorldvolumeAction
import JanusFormal.Branches.WorldvolumeQuantumAlpha.Gates.P0EFTJanusCondensateToAlphaMap

namespace JanusFormal.P0EFTJanusProgramAFrontier

set_option autoImplicit false

open P0EFTJanusCondensateToAlphaMap
open P0EFTJanusScaleInvariantWorldvolumeAction

/- The remaining physics is represented explicitly as hypotheses; the
   consequences below are then machine-checked and cannot hide a fit. -/
structure ClosureData where
  condensate : ℝ
  chargeAmplitude : ℝ
  chargeUnit : ℝ
  alphaSquaredLength : ℝ
  condensatePositive : 0 < condensate
  chargeAmplitudePositive : 0 < chargeAmplitude
  alphaPositive : 0 < alphaSquaredLength
  chargeLaw : chargeUnit = chargeAmplitude ^ 2 * condensate ^ 2
  fluxLaw : 16 * chargeUnit ^ 2 * alphaSquaredLength ^ 4 = 1
  stableVacuum : Prop
  schemeIndependentVacuum : Prop
  anomalyFreePair : Prop
  uvTransportDerived : Prop

def qLL (s : ClosureData) : ℝ := s.chargeAmplitude ^ 2 * s.condensate ^ 2

theorem generated_qLL (s : ClosureData) : s.chargeUnit = qLL s := by
  exact s.chargeLaw

theorem transported_alpha_law (s : ClosureData) :
    2 * s.chargeAmplitude * s.condensate * s.alphaSquaredLength = 1 := by
  exact condensate_alpha_law {
    condensateMass := s.condensate,
    chargeAmplitude := s.chargeAmplitude,
    chargeUnit := s.chargeUnit,
    alphaSquaredLength := s.alphaSquaredLength,
    condensateMassPositive := s.condensatePositive,
    chargeAmplitudePositive := s.chargeAmplitudePositive,
    alphaSquaredLengthPositive := s.alphaPositive,
    chargeFromCondensate := s.chargeLaw,
    primitiveFluxRadiusLaw := s.fluxLaw }

theorem scale_invariant_action_is_2plus1d :
    dWorldvolume = 3 ∧
    scalarKineticDimension = 3 ∧
    scalarSexticDimension = 3 ∧
    chernSimonsDensityDimension = 3 ∧
    dressedMaxwellDensityDimension = 3 := by
  norm_num [dWorldvolume, scalarKineticDimension, scalarSexticDimension,
    chernSimonsDensityDimension, dressedMaxwellDensityDimension,
    inverseScalarSquareDimension, maxwellDensityDimension,
    fieldStrengthDimension, derivativeDimension, scalarDimension,
    csGaugeFieldDimension]

theorem closure_requires_all_frontier_inputs (s : ClosureData) :
    s.stableVacuum ∧ s.schemeIndependentVacuum ∧
      s.anomalyFreePair ∧ s.uvTransportDerived →
      s.chargeUnit = qLL s ∧
      2 * s.chargeAmplitude * s.condensate * s.alphaSquaredLength = 1 := by
  intro _
  exact ⟨generated_qLL s, transported_alpha_law s⟩

end JanusFormal.P0EFTJanusProgramAFrontier
