import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinCandidateSchwarz4D

/-!
# Mellin Schwarz symmetry from the unnormalized integral

Complex Gamma already satisfies the standard conjugation identity.  It should
not be repeated as a field of every reference zeta packet.

This file proves the normalized orientation

```text
Gamma(s) = conj (Gamma(conj s))
```

from Mathlib's `Complex.Gamma_conj`.  Consequently a real heat trace needs to
supply only

```text
I(s) = conj (I(conj s))
```

for its unnormalized Mellin integral.  The Gamma-normalized candidate symmetry
is then generated automatically.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatMellinIntegralSchwarz4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeHeatMellinCandidateSchwarz4D

/-- Gamma conjugation in the orientation consumed by the relative Mellin
candidate. -/
theorem complexGamma_schwarz (spectral : Complex) :
    Complex.Gamma spectral =
      Complex.conj (Complex.Gamma (Complex.conj spectral)) := by
  first
  | simpa using Complex.Gamma_conj (Complex.conj spectral)
  | simpa using (Complex.Gamma_conj (Complex.conj spectral)).symm

/-- The only heat-dependent conjugation statement: Schwarz symmetry of the
unnormalized Mellin integral. -/
structure RelativeHeatMellinIntegralSchwarzData
    (heatTrace : HeatTime → Real) where
  mellinIntegral_schwarz : ∀ spectral : Complex,
    relativeHeatMellinIntegral heatTrace spectral =
      Complex.conj
        (relativeHeatMellinIntegral heatTrace (Complex.conj spectral))

namespace RelativeHeatMellinIntegralSchwarzData

/-- Add the canonical Gamma identity and recover the preceding candidate
packet. -/
def toCandidateSchwarz
    {heatTrace : HeatTime → Real}
    (data : RelativeHeatMellinIntegralSchwarzData heatTrace) :
    RelativeHeatMellinCandidateSchwarzData heatTrace where
  gamma_schwarz := complexGamma_schwarz
  mellinIntegral_schwarz := data.mellinIntegral_schwarz

/-- Gamma-normalized candidate symmetry from the unnormalized Mellin integral
alone. -/
theorem candidate_schwarz
    {heatTrace : HeatTime → Real}
    (data : RelativeHeatMellinIntegralSchwarzData heatTrace)
    (spectral : Complex) :
    relativeHeatMellinZetaCandidate heatTrace spectral =
      Complex.conj
        (relativeHeatMellinZetaCandidate heatTrace
          (Complex.conj spectral)) :=
  data.toCandidateSchwarz.candidate_schwarz spectral

/-- Public unnormalized Mellin Schwarz checkpoint. -/
theorem relative_heat_mellin_integral_schwarz_gate
    (heatTrace : HeatTime → Real)
    (data : RelativeHeatMellinIntegralSchwarzData heatTrace) :
    (∀ spectral : Complex,
      relativeHeatMellinIntegral heatTrace spectral =
        Complex.conj
          (relativeHeatMellinIntegral heatTrace
            (Complex.conj spectral))) ∧
    (∀ spectral : Complex,
      relativeHeatMellinZetaCandidate heatTrace spectral =
        Complex.conj
          (relativeHeatMellinZetaCandidate heatTrace
            (Complex.conj spectral))) :=
  ⟨data.mellinIntegral_schwarz, data.candidate_schwarz⟩

end RelativeHeatMellinIntegralSchwarzData

end
end P0EFTJanusProgramPRelativeHeatMellinIntegralSchwarz4D
end JanusFormal
