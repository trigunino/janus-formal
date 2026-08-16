import Mathlib.Analysis.Normed.Module.Basic

/-!
# Short- and long-time Duhamel boundary identities from limits

The preceding boundary-matching packet accepts the exact identities

```text
C - D_short = G H' + B,
D_long       = B.
```

This file replaces each equality by the limiting statement from which it is
normally proved.

At short time, cutoff counterterms and cutoff integrals converge separately,
while their renormalized remainder converges to the logarithmic derivative
operator.  Uniqueness of limits yields the first boundary identity.

At long time, finite-cutoff integration satisfies an exact primitive identity

```text
partialIntegral(R) + terminalPrimitive(R) = B.
```

The partial integral converges to `D_long` and the terminal primitive tends to
zero.  Again uniqueness of limits yields `D_long = B`.

The cutoff type and filter are abstract so that the same theorem applies to
continuous cutoffs, sequences or geometry-specific exhaustion parameters.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPReferenceNuclearDuhamelBoundaryLimits4D

set_option autoImplicit false
noncomputable section

open Filter Topology

variable {Cutoff E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Short-time renormalized limit producing the logarithmic derivative plus the
matching operator. -/
structure ReferenceNuclearDuhamelShortTimeBoundaryLimitData
    (cutoffFilter : Filter Cutoff) [NeBot cutoffFilter]
    (countertermOperator integratedOperator logarithmicDerivativeOperator
      matchingOperator : E) where
  cutoffCounterterm : Cutoff → E
  cutoffIntegral : Cutoff → E
  cutoffCounterterm_tendsto :
    Tendsto cutoffCounterterm cutoffFilter (𝓝 countertermOperator)
  cutoffIntegral_tendsto :
    Tendsto cutoffIntegral cutoffFilter (𝓝 integratedOperator)
  renormalizedRemainder_tendsto :
    Tendsto
      (fun cutoff =>
        (cutoffCounterterm cutoff - cutoffIntegral cutoff) - matchingOperator)
      cutoffFilter (𝓝 logarithmicDerivativeOperator)

namespace ReferenceNuclearDuhamelShortTimeBoundaryLimitData

/-- Uniqueness of the short-time renormalized limit gives
`C - D_short = G H' + B`. -/
theorem boundaryIdentity
    {cutoffFilter : Filter Cutoff} [NeBot cutoffFilter]
    {countertermOperator integratedOperator logarithmicDerivativeOperator
      matchingOperator : E}
    (data : ReferenceNuclearDuhamelShortTimeBoundaryLimitData cutoffFilter
      countertermOperator integratedOperator logarithmicDerivativeOperator
        matchingOperator) :
    countertermOperator - integratedOperator =
      logarithmicDerivativeOperator + matchingOperator := by
  have hAlgebraic :
      Tendsto
        (fun cutoff =>
          (data.cutoffCounterterm cutoff - data.cutoffIntegral cutoff) -
            matchingOperator)
        cutoffFilter
        (𝓝 ((countertermOperator - integratedOperator) - matchingOperator)) :=
    (data.cutoffCounterterm_tendsto.sub data.cutoffIntegral_tendsto).sub
      tendsto_const_nhds
  have hLimit :
      (countertermOperator - integratedOperator) - matchingOperator =
        logarithmicDerivativeOperator :=
    tendsto_nhds_unique hAlgebraic data.renormalizedRemainder_tendsto
  calc
    countertermOperator - integratedOperator =
        ((countertermOperator - integratedOperator) - matchingOperator) +
          matchingOperator := by abel
    _ = logarithmicDerivativeOperator + matchingOperator := by
      rw [hLimit]

/-- Public short-time boundary-limit checkpoint. -/
theorem reference_nuclear_duhamel_short_time_boundary_limit_gate
    (cutoffFilter : Filter Cutoff) [NeBot cutoffFilter]
    (countertermOperator integratedOperator logarithmicDerivativeOperator
      matchingOperator : E)
    (data : ReferenceNuclearDuhamelShortTimeBoundaryLimitData cutoffFilter
      countertermOperator integratedOperator logarithmicDerivativeOperator
        matchingOperator) :
    countertermOperator - integratedOperator =
      logarithmicDerivativeOperator + matchingOperator :=
  data.boundaryIdentity

end ReferenceNuclearDuhamelShortTimeBoundaryLimitData

/-- Long-time primitive and decay data. -/
structure ReferenceNuclearDuhamelLongTimeBoundaryLimitData
    (cutoffFilter : Filter Cutoff) [NeBot cutoffFilter]
    (integratedOperator matchingOperator : E) where
  partialIntegral : Cutoff → E
  terminalPrimitive : Cutoff → E
  partialIntegral_tendsto :
    Tendsto partialIntegral cutoffFilter (𝓝 integratedOperator)
  terminalPrimitive_tendsto_zero :
    Tendsto terminalPrimitive cutoffFilter (𝓝 0)
  finiteBoundaryIdentity : ∀ cutoff,
    partialIntegral cutoff + terminalPrimitive cutoff = matchingOperator

namespace ReferenceNuclearDuhamelLongTimeBoundaryLimitData

/-- The terminal primitive vanishes, hence the full long-time integral equals
the matching operator. -/
theorem boundaryIdentity
    {cutoffFilter : Filter Cutoff} [NeBot cutoffFilter]
    {integratedOperator matchingOperator : E}
    (data : ReferenceNuclearDuhamelLongTimeBoundaryLimitData cutoffFilter
      integratedOperator matchingOperator) :
    integratedOperator = matchingOperator := by
  have hSum :
      Tendsto
        (fun cutoff =>
          data.partialIntegral cutoff + data.terminalPrimitive cutoff)
        cutoffFilter (𝓝 (integratedOperator + 0)) :=
    data.partialIntegral_tendsto.add data.terminalPrimitive_tendsto_zero
  have hMatchingToLimit :
      Tendsto (fun _ : Cutoff => matchingOperator) cutoffFilter
        (𝓝 (integratedOperator + 0)) := by
    convert hSum using 1
    funext cutoff
    exact (data.finiteBoundaryIdentity cutoff).symm
  have hConstant :
      Tendsto (fun _ : Cutoff => matchingOperator) cutoffFilter
        (𝓝 matchingOperator) :=
    tendsto_const_nhds
  have hLimit : integratedOperator + 0 = matchingOperator :=
    tendsto_nhds_unique hMatchingToLimit hConstant
  simpa using hLimit

/-- Public long-time boundary-limit checkpoint. -/
theorem reference_nuclear_duhamel_long_time_boundary_limit_gate
    (cutoffFilter : Filter Cutoff) [NeBot cutoffFilter]
    (integratedOperator matchingOperator : E)
    (data : ReferenceNuclearDuhamelLongTimeBoundaryLimitData cutoffFilter
      integratedOperator matchingOperator) :
    integratedOperator = matchingOperator :=
  data.boundaryIdentity

end ReferenceNuclearDuhamelLongTimeBoundaryLimitData

end
end P0EFTJanusProgramPReferenceNuclearDuhamelBoundaryLimits4D
end JanusFormal
