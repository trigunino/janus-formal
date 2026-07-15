import JanusFormal.Branches.JanusSuperfluidAnalogue.Gates.P0EFTJanusSF01InteractionStability

namespace JanusFormal
namespace P0EFTJanusSF02SF03Bogoliubov

set_option autoImplicit false

/-- Bogoliubov frequency squared for one common/relative channel. -/
def bogoliubovFrequencySquared
    (epsilon density coupling : ℝ) : ℝ :=
  epsilon * (epsilon + 2 * density * coupling)

theorem stable_channel_has_nonnegative_frequency
    (epsilon density coupling : ℝ)
    (hEpsilon : 0 ≤ epsilon)
    (hDensity : 0 ≤ density)
    (hCoupling : 0 ≤ coupling) :
    0 ≤ bogoliubovFrequencySquared epsilon density coupling := by
  unfold bogoliubovFrequencySquared
  positivity

theorem negative_relative_coupling_has_long_wave_instability
    (density relativeCoupling : ℝ)
    (hDensity : 0 < density)
    (hCoupling : relativeCoupling < 0) :
    bogoliubovFrequencySquared
      (-density * relativeCoupling) density relativeCoupling < 0 := by
  unfold bogoliubovFrequencySquared
  nlinarith [mul_pos hDensity (neg_pos.mpr hCoupling)]

structure AnalogueDictionary where
  commonModeMapped : Prop
  relativeModeMapped : Prop
  interfaceMapped : Prop
  acousticMetricMapped : Prop
  gravitationalFieldEquationMapped : Prop
  microscopicJanusOriginDerived : Prop

def kinematicAnalogyReady (s : AnalogueDictionary) : Prop :=
  s.commonModeMapped ∧ s.relativeModeMapped ∧
  s.interfaceMapped ∧ s.acousticMetricMapped

def fundamentalEquivalenceReady (s : AnalogueDictionary) : Prop :=
  kinematicAnalogyReady s ∧
  s.gravitationalFieldEquationMapped ∧
  s.microscopicJanusOriginDerived

end P0EFTJanusSF02SF03Bogoliubov
end JanusFormal
