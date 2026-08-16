import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Topology.Instances.Complex
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaRealAxisReality4D

/-!
# Schwarz reflection for a relative heat Mellin continuation

Reality of the zeta derivative was reduced to a real-axis germ near zero.  This
file derives that germ from the analytic continuation itself.

For a real heat trace, the Gamma-normalized Mellin candidate satisfies the
Schwarz symmetry

```text
M(conj s) = conj (M(s)).
```

Equivalently,

```text
M(s) = conj (M(conj s)).
```

on the convergence half-plane.  The continued zeta function and its reflected
function

```text
s ↦ conj (zeta (conj s))
```

are assumed analytic on one common open preconnected domain containing zero and
a point of that half-plane.  Their equality near the seed follows from the
Mellin formula, and the analytic identity principle propagates it through the
whole domain.  On the real axis this is precisely `zeta x = conj (zeta x)`, so
the imaginary part vanishes near zero.

The regularized derivative is therefore real without being supplied as a
separate scalar fact.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatMellinZetaSchwarzReflection4D

set_option autoImplicit false
noncomputable section

open scoped ComplexConjugate
open Filter Set Topology
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeHeatMellinZetaRealAxisReality4D

/-- Schwarz reflection of a complex function. -/
def schwarzReflect (function : Complex → Complex) (spectral : Complex) : Complex :=
  conj (function (conj spectral))

/-- Analytic Schwarz-reflection data joining the Mellin half-plane to zero. -/
structure RelativeHeatMellinZetaSchwarzReflectionData
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart) where
  domain : Set Complex
  isOpen_domain : IsOpen domain
  isPreconnected_domain : IsPreconnected domain
  zero_mem_domain : (0 : Complex) ∈ domain
  seed : Complex
  seed_mem_domain : seed ∈ domain
  seed_mem_mellinHalfPlane : continuation.convergenceAbscissa < seed.re
  zeta_analytic : AnalyticOnNhd Complex continuation.zeta domain
  reflected_analytic :
    AnalyticOnNhd Complex (schwarzReflect continuation.zeta) domain
  mellinCandidate_schwarz : ∀ spectral,
    continuation.convergenceAbscissa < spectral.re →
      relativeHeatMellinZetaCandidate heatTrace spectral =
        conj
          (relativeHeatMellinZetaCandidate heatTrace
            (conj spectral))

namespace RelativeHeatMellinZetaSchwarzReflectionData

/-- The Mellin convergence half-plane is open. -/
theorem isOpen_mellinHalfPlane
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (_data : RelativeHeatMellinZetaSchwarzReflectionData continuation) :
    IsOpen {spectral : Complex |
      continuation.convergenceAbscissa < spectral.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- In the Mellin half-plane the continued zeta function already equals its
Schwarz reflection. -/
theorem zeta_eq_schwarz_of_mellin
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (data : RelativeHeatMellinZetaSchwarzReflectionData continuation)
    (spectral : Complex)
    (hSpectral : continuation.convergenceAbscissa < spectral.re) :
    continuation.zeta spectral = schwarzReflect continuation.zeta spectral := by
  have hConjugate :
      continuation.convergenceAbscissa < (conj spectral).re := by
    simpa using hSpectral
  calc
    continuation.zeta spectral =
        relativeHeatMellinZetaCandidate heatTrace spectral :=
      continuation.zeta_eq_mellin spectral hSpectral
    _ = conj
        (relativeHeatMellinZetaCandidate heatTrace
          (conj spectral)) :=
      data.mellinCandidate_schwarz spectral hSpectral
    _ = conj (continuation.zeta (conj spectral)) := by
      rw [← continuation.zeta_eq_mellin (conj spectral) hConjugate]
    _ = schwarzReflect continuation.zeta spectral := rfl

/-- Equality with the reflected function holds on a neighborhood of the seed. -/
theorem eventuallyEq_zeta_reflection_at_seed
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (data : RelativeHeatMellinZetaSchwarzReflectionData continuation) :
    continuation.zeta =ᶠ[𝓝 data.seed]
      schwarzReflect continuation.zeta := by
  have hNeighborhood :
      {spectral : Complex |
        continuation.convergenceAbscissa < spectral.re} ∈ 𝓝 data.seed :=
    data.isOpen_mellinHalfPlane.mem_nhds data.seed_mem_mellinHalfPlane
  filter_upwards [hNeighborhood] with spectral hSpectral
  exact data.zeta_eq_schwarz_of_mellin spectral hSpectral

/-- Analytic identity principle propagates Schwarz symmetry through the common
domain. -/
theorem zeta_eqOn_schwarz_domain
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (data : RelativeHeatMellinZetaSchwarzReflectionData continuation) :
    Set.EqOn continuation.zeta (schwarzReflect continuation.zeta) data.domain :=
  data.zeta_analytic.eqOn_of_preconnected_of_eventuallyEq
    data.reflected_analytic data.isPreconnected_domain data.seed_mem_domain
      data.eventuallyEq_zeta_reflection_at_seed

/-- The real axis lies in the comparison domain near zero. -/
theorem eventually_realAxis_mem_domain
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (data : RelativeHeatMellinZetaSchwarzReflectionData continuation) :
    ∀ᶠ spectral : Real in 𝓝 0, (spectral : Complex) ∈ data.domain := by
  have hDomain : data.domain ∈ 𝓝 (0 : Complex) :=
    data.isOpen_domain.mem_nhds data.zero_mem_domain
  have hOfReal :
      Tendsto (fun spectral : Real => (spectral : Complex))
        (𝓝 0) (𝓝 (0 : Complex)) := by
    change ContinuousAt Complex.ofReal 0
    exact Complex.continuous_ofReal.continuousAt
  exact hOfReal hDomain

/-- Schwarz symmetry forces reality on the real axis inside the domain. -/
theorem zeta_im_eq_zero_of_real_mem_domain
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (data : RelativeHeatMellinZetaSchwarzReflectionData continuation)
    (spectral : Real) (hSpectral : (spectral : Complex) ∈ data.domain) :
    (continuation.zeta (spectral : Complex)).im = 0 := by
  have hReflection := data.zeta_eqOn_schwarz_domain hSpectral
  have hFixed :
      continuation.zeta (spectral : Complex) =
        conj (continuation.zeta (spectral : Complex)) := by
    simpa [schwarzReflect] using hReflection
  have hImaginary := congrArg Complex.im hFixed
  simp only [Complex.conj_im] at hImaginary
  linarith

/-- The continued zeta function has a real-axis germ at zero. -/
def toRealAxisReality
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (data : RelativeHeatMellinZetaSchwarzReflectionData continuation) :
    RelativeHeatMellinZetaRealAxisRealityData continuation where
  eventually_im_zero := by
    filter_upwards [data.eventually_realAxis_mem_domain] with spectral hSpectral
    exact data.zeta_im_eq_zero_of_real_mem_domain spectral hSpectral

/-- Reality of the regularized derivative is a consequence of Schwarz
reflection. -/
theorem derivativeAtZero_im_eq_zero
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (data : RelativeHeatMellinZetaSchwarzReflectionData continuation) :
    continuation.derivativeAtZero.im = 0 :=
  data.toRealAxisReality.derivativeAtZero_im_eq_zero

/-- Public Schwarz-reflection checkpoint. -/
theorem relative_heat_mellin_zeta_schwarz_reflection_gate
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart)
    (data : RelativeHeatMellinZetaSchwarzReflectionData continuation) :
    Set.EqOn continuation.zeta (schwarzReflect continuation.zeta) data.domain ∧
    (∀ᶠ spectral : Real in 𝓝 0,
      (continuation.zeta (spectral : Complex)).im = 0) ∧
    continuation.derivativeAtZero.im = 0 :=
  ⟨data.zeta_eqOn_schwarz_domain,
    data.toRealAxisReality.eventually_im_zero,
    data.derivativeAtZero_im_eq_zero⟩

end RelativeHeatMellinZetaSchwarzReflectionData

end
end P0EFTJanusProgramPRelativeHeatMellinZetaSchwarzReflection4D
end JanusFormal
