import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinKernelSchwarz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaIntegralSchwarzReflection4D

/-!
# Zeta Schwarz reflection from pointwise Mellin-kernel symmetry

The integral-Schwarz continuation packet accepted conjugation of the complete
unnormalized Mellin integral.  This frontend lowers the reference-dependent
input one level further.

Pointwise kernel conjugation is proved universally for every real heat trace.
The only stored statement is compatibility of complex conjugation with the
Bochner integral of the conjugated kernel.  From it the implementation derives

```text
I(s) = conj (I(conj s)),
M(s) = conj (M(conj s)),
Im (zeta'(0)) = 0.
```
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatMellinZetaKernelSchwarzReflection4D

set_option autoImplicit false
noncomputable section

open Set
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinKernelSchwarz4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeHeatMellinZetaIntegralSchwarzReflection4D
open P0EFTJanusProgramPRelativeHeatMellinZetaSchwarzReflection4D

/-- Analytic continuation data whose only Mellin conjugation field is the
map-integral compatibility of the pointwise Schwarz kernel. -/
structure RelativeHeatMellinZetaKernelSchwarzReflectionData
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
  mellinKernelSchwarz : RelativeHeatMellinKernelSchwarzData heatTrace

namespace RelativeHeatMellinZetaKernelSchwarzReflectionData

/-- Recover the integral-level Schwarz continuation packet. -/
def toIntegralSchwarzReflection
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (data : RelativeHeatMellinZetaKernelSchwarzReflectionData continuation) :
    RelativeHeatMellinZetaIntegralSchwarzReflectionData continuation where
  domain := data.domain
  isOpen_domain := data.isOpen_domain
  isPreconnected_domain := data.isPreconnected_domain
  zero_mem_domain := data.zero_mem_domain
  seed := data.seed
  seed_mem_domain := data.seed_mem_domain
  seed_mem_mellinHalfPlane := data.seed_mem_mellinHalfPlane
  zeta_analytic := data.zeta_analytic
  reflected_analytic := data.reflected_analytic
  mellinIntegralSchwarz := data.mellinKernelSchwarz.toMellinIntegralSchwarz

/-- Reality of the regularized derivative from pointwise kernel symmetry and
map-integral compatibility. -/
theorem derivativeAtZero_im_eq_zero
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (data : RelativeHeatMellinZetaKernelSchwarzReflectionData continuation) :
    continuation.derivativeAtZero.im = 0 :=
  data.toIntegralSchwarzReflection.derivativeAtZero_im_eq_zero

/-- Public kernel-Schwarz continuation checkpoint. -/
theorem relative_heat_mellin_zeta_kernel_schwarz_reflection_gate
    {heatTrace : P0EFTJanusCircleDiracHeatTraceCancellation.HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart)
    (data : RelativeHeatMellinZetaKernelSchwarzReflectionData continuation) :
    (∀ spectral time,
      relativeHeatMellinKernel heatTrace spectral time =
        Complex.conj
          (relativeHeatMellinKernel heatTrace
            (Complex.conj spectral) time)) ∧
    (∀ spectral,
      relativeHeatMellinIntegral heatTrace spectral =
        Complex.conj
          (relativeHeatMellinIntegral heatTrace
            (Complex.conj spectral))) ∧
    Set.EqOn continuation.zeta
      (schwarzReflect continuation.zeta) data.domain ∧
    continuation.derivativeAtZero.im = 0 :=
  ⟨relativeHeatMellinKernel_schwarz heatTrace,
    data.mellinKernelSchwarz.mellinIntegral_schwarz,
    data.toIntegralSchwarzReflection.toGeneratedSchwarzReflection.
      toSchwarzReflection.zeta_eqOn_schwarz_domain,
    data.derivativeAtZero_im_eq_zero⟩

end RelativeHeatMellinZetaKernelSchwarzReflectionData

end
end P0EFTJanusProgramPRelativeHeatMellinZetaKernelSchwarzReflection4D
end JanusFormal
