import JanusFormal.Branches.JanusGravitationalWaves.Gates.P0EFTJanusGWStabilityCausalityGate

namespace JanusFormal
namespace P0EFTJanusGWOscillationGate

set_option autoImplicit false

/-- Orthogonal two-mode mixing written without assuming a trigonometric
parameterization. -/
def toPropagationModes (c s visible hidden : ℝ) : ℝ × ℝ :=
  (c * visible + s * hidden, -s * visible + c * hidden)

def fromPropagationModes (c s diagonal relative : ℝ) : ℝ × ℝ :=
  (c * diagonal - s * relative, s * diagonal + c * relative)

theorem mixing_round_trip
    (c s visible hidden : ℝ) (hUnit : c ^ 2 + s ^ 2 = 1) :
    fromPropagationModes c s
      (toPropagationModes c s visible hidden).1
      (toPropagationModes c s visible hidden).2 = (visible, hidden) := by
  apply Prod.ext
  · simp only [toPropagationModes, fromPropagationModes]
    calc
      c * (c * visible + s * hidden) - s * (-s * visible + c * hidden) =
          (c ^ 2 + s ^ 2) * visible := by ring
      _ = visible := by rw [hUnit]; ring
  · simp only [toPropagationModes, fromPropagationModes]
    calc
      s * (c * visible + s * hidden) + c * (-s * visible + c * hidden) =
          (c ^ 2 + s ^ 2) * hidden := by ring
      _ = hidden := by rw [hUnit]; ring

/-- Generic two-mode conversion probability. `mixingWeight` contains the
source/detector projection and `phaseFactor` the propagation phase. -/
def conversionProbability (mixingWeight phaseFactor : ℝ) : ℝ :=
  mixingWeight * phaseFactor

theorem conversion_probability_is_bounded
    (mixingWeight phaseFactor : ℝ)
    (hMixLow : 0 ≤ mixingWeight) (hMixHigh : mixingWeight ≤ 1)
    (hPhaseLow : 0 ≤ phaseFactor) (hPhaseHigh : phaseFactor ≤ 1) :
    0 ≤ conversionProbability mixingWeight phaseFactor ∧
      conversionProbability mixingWeight phaseFactor ≤ 1 := by
  constructor
  · exact mul_nonneg hMixLow hPhaseLow
  · calc
      mixingWeight * phaseFactor ≤ mixingWeight * 1 :=
        mul_le_mul_of_nonneg_left hPhaseHigh hMixLow
      _ = mixingWeight := by ring
      _ ≤ 1 := hMixHigh

theorem zero_mixing_has_no_conversion (phaseFactor : ℝ) :
    conversionProbability 0 phaseFactor = 0 := by
  simp [conversionProbability]

theorem degenerate_phase_has_no_conversion (mixingWeight : ℝ) :
    conversionProbability mixingWeight 0 = 0 := by
  simp [conversionProbability]

/-- P is needed to turn the generic mixing weight into the physical Janus
source and detector projections. -/
structure GW03Status where
  orthogonalMixingAlgebraDerived : Prop
  probabilityBoundsDerived : Prop
  zeroMixingLimitDerived : Prop
  degeneratePhaseLimitDerived : Prop
  mixingAngleDerivedFromP : Prop
  phaseHistoryDerivedFromP : Prop

def genericGW03Closed (s : GW03Status) : Prop :=
  s.orthogonalMixingAlgebraDerived ∧
  s.probabilityBoundsDerived ∧
  s.zeroMixingLimitDerived ∧
  s.degeneratePhaseLimitDerived

def physicalGW03Closed (s : GW03Status) : Prop :=
  genericGW03Closed s ∧ s.mixingAngleDerivedFromP ∧ s.phaseHistoryDerivedFromP

end P0EFTJanusGWOscillationGate
end JanusFormal
