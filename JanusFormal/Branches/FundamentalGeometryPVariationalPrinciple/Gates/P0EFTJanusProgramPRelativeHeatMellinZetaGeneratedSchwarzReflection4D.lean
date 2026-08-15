import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinCandidateSchwarz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaSchwarzReflection4D

/-!
# Schwarz continuation generated from Gamma and Mellin-integral symmetry

The analytic Schwarz-reflection packet previously accepted the normalized
candidate equality `M(s) = conj (M(conj s))`.  The preceding layer derives that
equality from conjugation of the Gamma function and of the unnormalized Mellin
integral.

This file replaces the normalized field by a
`RelativeHeatMellinCandidateSchwarzData` and then reuses the identity-principle
construction.  Reality of the regularized derivative is therefore generated
from the two primitive conjugation statements.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatMellinZetaGeneratedSchwarzReflection4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinCandidateSchwarz4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeHeatMellinZetaSchwarzReflection4D

/-- Analytic continuation data with Schwarz symmetry generated at the
unnormalized Mellin level. -/
structure RelativeHeatMellinZetaGeneratedSchwarzReflectionData
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
    AnalyticOnNhd Complex
      (schwarzReflect continuation.zeta) domain
  mellinSchwarz : RelativeHeatMellinCandidateSchwarzData heatTrace

namespace RelativeHeatMellinZetaGeneratedSchwarzReflectionData

/-- Convert primitive Gamma/integral symmetry to the normalized reflection
packet. -/
def toSchwarzReflection
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (data : RelativeHeatMellinZetaGeneratedSchwarzReflectionData continuation) :
    RelativeHeatMellinZetaSchwarzReflectionData continuation where
  domain := data.domain
  isOpen_domain := data.isOpen_domain
  isPreconnected_domain := data.isPreconnected_domain
  zero_mem_domain := data.zero_mem_domain
  seed := data.seed
  seed_mem_domain := data.seed_mem_domain
  seed_mem_mellinHalfPlane := data.seed_mem_mellinHalfPlane
  zeta_analytic := data.zeta_analytic
  reflected_analytic := data.reflected_analytic
  mellinCandidate_schwarz := fun spectral _ =>
    data.mellinSchwarz.candidate_schwarz spectral

/-- Reality of the regularized derivative follows from primitive Mellin
conjugation. -/
theorem derivativeAtZero_im_eq_zero
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (data : RelativeHeatMellinZetaGeneratedSchwarzReflectionData continuation) :
    continuation.derivativeAtZero.im = 0 :=
  data.toSchwarzReflection.derivativeAtZero_im_eq_zero

/-- Public generated Schwarz-reflection checkpoint. -/
theorem relative_heat_mellin_zeta_generated_schwarz_reflection_gate
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart)
    (data : RelativeHeatMellinZetaGeneratedSchwarzReflectionData continuation) :
    (∀ spectral : Complex,
      relativeHeatMellinZetaCandidate heatTrace spectral =
        Complex.conj
          (relativeHeatMellinZetaCandidate heatTrace
            (Complex.conj spectral))) ∧
    Set.EqOn continuation.zeta
      (schwarzReflect continuation.zeta) data.domain ∧
    continuation.derivativeAtZero.im = 0 :=
  ⟨data.mellinSchwarz.candidate_schwarz,
    data.toSchwarzReflection.zeta_eqOn_schwarz_domain,
    data.derivativeAtZero_im_eq_zero⟩

end RelativeHeatMellinZetaGeneratedSchwarzReflectionData

end
end P0EFTJanusProgramPRelativeHeatMellinZetaGeneratedSchwarzReflection4D
end JanusFormal
