import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinIntegralSchwarz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaGeneratedSchwarzReflection4D

/-!
# Zeta Schwarz reflection from the unnormalized Mellin integral

The generated Schwarz packet still stored both Gamma and Mellin-integral
conjugation.  Gamma conjugation is canonical, so this frontend keeps only the
heat-dependent statement

```text
I(s) = conj (I(conj s)).
```

It inserts the library Gamma identity, derives the normalized candidate
symmetry, applies analytic uniqueness and obtains reality of `zeta'(0)`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatMellinZetaIntegralSchwarzReflection4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinIntegralSchwarz4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeHeatMellinZetaGeneratedSchwarzReflection4D
open P0EFTJanusProgramPRelativeHeatMellinZetaSchwarzReflection4D

/-- Analytic continuation data whose only heat-dependent Schwarz input is the
unnormalized Mellin-integral conjugation. -/
structure RelativeHeatMellinZetaIntegralSchwarzReflectionData
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
  mellinIntegralSchwarz :
    RelativeHeatMellinIntegralSchwarzData heatTrace

namespace RelativeHeatMellinZetaIntegralSchwarzReflectionData

/-- Insert canonical Gamma conjugation and recover the generated reflection
packet. -/
def toGeneratedSchwarzReflection
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (data : RelativeHeatMellinZetaIntegralSchwarzReflectionData continuation) :
    RelativeHeatMellinZetaGeneratedSchwarzReflectionData continuation where
  domain := data.domain
  isOpen_domain := data.isOpen_domain
  isPreconnected_domain := data.isPreconnected_domain
  zero_mem_domain := data.zero_mem_domain
  seed := data.seed
  seed_mem_domain := data.seed_mem_domain
  seed_mem_mellinHalfPlane := data.seed_mem_mellinHalfPlane
  zeta_analytic := data.zeta_analytic
  reflected_analytic := data.reflected_analytic
  mellinSchwarz := data.mellinIntegralSchwarz.toCandidateSchwarz

/-- Reality of the regularized derivative is generated from the unnormalized
Mellin integral. -/
theorem derivativeAtZero_im_eq_zero
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (data : RelativeHeatMellinZetaIntegralSchwarzReflectionData continuation) :
    continuation.derivativeAtZero.im = 0 :=
  data.toGeneratedSchwarzReflection.derivativeAtZero_im_eq_zero

/-- Public integral-Schwarz continuation checkpoint. -/
theorem relative_heat_mellin_zeta_integral_schwarz_reflection_gate
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart)
    (data : RelativeHeatMellinZetaIntegralSchwarzReflectionData continuation) :
    (∀ spectral : Complex,
      relativeHeatMellinIntegral heatTrace spectral =
        Complex.conj
          (relativeHeatMellinIntegral heatTrace
            (Complex.conj spectral))) ∧
    Set.EqOn continuation.zeta
      (schwarzReflect continuation.zeta) data.domain ∧
    continuation.derivativeAtZero.im = 0 :=
  ⟨data.mellinIntegralSchwarz.mellinIntegral_schwarz,
    data.toGeneratedSchwarzReflection.toSchwarzReflection.
      zeta_eqOn_schwarz_domain,
    data.derivativeAtZero_im_eq_zero⟩

end RelativeHeatMellinZetaIntegralSchwarzReflectionData

end
end P0EFTJanusProgramPRelativeHeatMellinZetaIntegralSchwarzReflection4D
end JanusFormal
