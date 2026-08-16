import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Integrable exponential majorants on a long-time half-line

A positive spectral decay rate produces the standard long-time envelope

```text
C exp (-c t).
```

This file records the two facts consumed by dominated heat differentiation:

* the envelope is integrable on every half-line `(T₀, +∞)` when `0 < c`;
* its integral is the explicit positive tail `C exp (-c T₀) / c`.

The theorem does not manufacture the spectral estimate itself.  In particular,
a two-sided norm gap `c ‖x‖ ≤ ‖H x‖` is not silently treated as positivity of
`H`; one must still prove the genuine positive heat-decay estimate for the
chosen reference generator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D

set_option autoImplicit false
noncomputable section

open MeasureTheory Set

/-- Standard scalar long-time exponential envelope. -/
def longTimeExponentialBound
    (scale rate time : Real) : Real :=
  scale * Real.exp (-rate * time)

/-- The unscaled exponential tail is integrable on every long-time half-line
for a positive decay rate. -/
theorem integrableOn_longTimeExponentialCore
    {rate : Real} (hRate : 0 < rate) (start : Real) :
    IntegrableOn (fun time : Real => Real.exp (-rate * time))
      (Set.Ioi start) := by
  simpa only [neg_mul] using
    (integrableOn_exp_mul_Ioi (a := -rate) (by linarith) start)

/-- Multiplying by an arbitrary finite scalar preserves integrability. -/
theorem integrableOn_longTimeExponentialBound
    (scale : Real) {rate : Real} (hRate : 0 < rate) (start : Real) :
    IntegrableOn (longTimeExponentialBound scale rate) (Set.Ioi start) := by
  have hCore := integrableOn_longTimeExponentialCore hRate start
  change Integrable (fun time : Real => scale * Real.exp (-rate * time))
    (volume.restrict (Set.Ioi start))
  exact hCore.const_mul scale

/-- Exact integral of the unscaled exponential tail. -/
theorem integral_longTimeExponentialCore
    {rate : Real} (hRate : 0 < rate) (start : Real) :
    (∫ time : Real in Set.Ioi start, Real.exp (-rate * time)) =
      Real.exp (-rate * start) / rate := by
  have hIntegral := integral_exp_mul_Ioi (a := -rate) (by linarith) start
  simpa only [neg_mul, neg_div_neg_eq] using hIntegral

/-- Exact integral of the scaled exponential envelope. -/
theorem integral_longTimeExponentialBound
    (scale : Real) {rate : Real} (hRate : 0 < rate) (start : Real) :
    (∫ time : Real in Set.Ioi start,
      longTimeExponentialBound scale rate time) =
      scale * (Real.exp (-rate * start) / rate) := by
  unfold longTimeExponentialBound
  rw [integral_const_mul]
  exact congrArg (scale * ·)
    (integral_longTimeExponentialCore hRate start)

/-- Public long-time exponential-integrability checkpoint. -/
theorem long_time_exponential_dominating_function_gate
    (scale rate start : Real) (hRate : 0 < rate) :
    IntegrableOn (longTimeExponentialBound scale rate) (Set.Ioi start) ∧
    (∫ time : Real in Set.Ioi start,
      longTimeExponentialBound scale rate time) =
      scale * (Real.exp (-rate * start) / rate) :=
  ⟨integrableOn_longTimeExponentialBound scale hRate start,
    integral_longTimeExponentialBound scale hRate start⟩

end
end P0EFTJanusProgramPLongTimeExponentialDominatingFunction4D
end JanusFormal
