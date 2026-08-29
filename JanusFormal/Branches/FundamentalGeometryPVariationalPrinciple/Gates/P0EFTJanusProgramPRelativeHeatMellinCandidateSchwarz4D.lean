import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

/-!
# Schwarz symmetry of the Gamma-normalized Mellin candidate

The reflected-continuation packet needs

```text
M(s) = conj (M(conj s))
```

for the Gamma-normalized Mellin candidate.  This identity has two independent
analytic sources:

```text
Gamma(s) = conj (Gamma(conj s)),
I(s)     = conj (I(conj s)),
```

where `I` is the unnormalized Mellin heat integral.  This file records exactly
those low-level statements and derives the normalized symmetry by conjugation
of inverse and multiplication.

Thus the Schwarz continuation layer no longer requires the final normalized
candidate equality as an independent field.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatMellinCandidateSchwarz4D

set_option autoImplicit false
noncomputable section

open scoped ComplexConjugate
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

/-- Gamma and unnormalized Mellin-integral conjugation data for one real heat
trace. -/
structure RelativeHeatMellinCandidateSchwarzData
    (heatTrace : HeatTime → Real) where
  gamma_schwarz : ∀ spectral : Complex,
    Complex.Gamma spectral =
      conj (Complex.Gamma (conj spectral))
  mellinIntegral_schwarz : ∀ spectral : Complex,
    relativeHeatMellinIntegral heatTrace spectral =
      conj
        (relativeHeatMellinIntegral heatTrace (conj spectral))

namespace RelativeHeatMellinCandidateSchwarzData

/-- The Gamma-normalized Mellin candidate inherits Schwarz symmetry. -/
theorem candidate_schwarz
    {heatTrace : HeatTime → Real}
    (data : RelativeHeatMellinCandidateSchwarzData heatTrace)
    (spectral : Complex) :
    relativeHeatMellinZetaCandidate heatTrace spectral =
      conj
        (relativeHeatMellinZetaCandidate heatTrace
          (conj spectral)) := by
  calc
    relativeHeatMellinZetaCandidate heatTrace spectral =
        (conj (Complex.Gamma (conj spectral)))⁻¹ *
          conj
            (relativeHeatMellinIntegral heatTrace
              (conj spectral)) := by
      rw [relativeHeatMellinZetaCandidate,
        data.gamma_schwarz spectral,
        data.mellinIntegral_schwarz spectral]
    _ = conj
        ((Complex.Gamma (conj spectral))⁻¹ *
          relativeHeatMellinIntegral heatTrace
            (conj spectral)) := by
      simp
    _ = conj
        (relativeHeatMellinZetaCandidate heatTrace
          (conj spectral)) := by
      rfl

/-- Public normalized Mellin Schwarz checkpoint. -/
theorem relative_heat_mellin_candidate_schwarz_gate
    (heatTrace : HeatTime → Real)
    (data : RelativeHeatMellinCandidateSchwarzData heatTrace) :
    ∀ spectral : Complex,
      relativeHeatMellinZetaCandidate heatTrace spectral =
        conj
          (relativeHeatMellinZetaCandidate heatTrace
            (conj spectral)) :=
  data.candidate_schwarz

end RelativeHeatMellinCandidateSchwarzData

end
end P0EFTJanusProgramPRelativeHeatMellinCandidateSchwarz4D
end JanusFormal
