import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinIntegralSchwarz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinKernelSchwarz4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaRealAxisReality4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaSchwarzReflection4D

/-!
# Canonical Schwarz reflection from Mellin integrability

No per-reference conjugation equality is needed in the Mellin half-plane.
The continuation packet already provides integrability there.  Complex
conjugation is a continuous real-linear isometry, so it commutes with the
Bochner integral of the conjugate Mellin kernel.  Pointwise kernel conjugation
and the library Gamma identity then prove

```text
M(s) = conj (M(conj s))
```

throughout the certified convergence half-plane.

This is exactly the seed equality required by the analytic identity principle.
Accordingly this file keeps only the common analytic domain and analyticity of
the zeta function and its Schwarz reflection.  Mellin symmetry, the real-axis
germ and reality of `zeta'(0)` are all derived.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatMellinZetaCanonicalSchwarzReflection4D

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Set Topology
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeHeatMellinIntegralSchwarz4D
open P0EFTJanusProgramPRelativeHeatMellinKernelSchwarz4D
open P0EFTJanusProgramPRelativeHeatMellinZetaRealAxisReality4D
open P0EFTJanusProgramPRelativeHeatMellinZetaSchwarzReflection4D

/-- Complex conjugation as a real-linear map. -/
def complexConjugationLinearMap : Complex →ₗ[Real] Complex where
  toFun := Complex.conj
  map_add' := by
    intro first second
    simp
  map_smul' := by
    intro scalar value
    simp

/-- Complex conjugation as a real continuous linear map. -/
def complexConjugationCLM : Complex →L[Real] Complex :=
  complexConjugationLinearMap.mkContinuous 1 (by
    intro value
    simp [complexConjugationLinearMap])

@[simp]
theorem complexConjugationCLM_apply (value : Complex) :
    complexConjugationCLM value = Complex.conj value :=
  rfl

/-- Conjugation commutes with the Bochner integral of an integrable complex
function. -/
theorem integral_complexConjugation
    {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {function : α → Complex}
    (hIntegrable : Integrable function μ) :
    (∫ point, Complex.conj (function point) ∂μ) =
      Complex.conj (∫ point, function point ∂μ) := by
  first
  | simpa [complexConjugationCLM] using
      (complexConjugationCLM.integral_comp_comm hIntegrable).symm
  | simpa [complexConjugationCLM] using
      (complexConjugationCLM.integral_comp_comm hIntegrable)
  | simpa [complexConjugationCLM] using
      (ContinuousLinearMap.integral_comp_comm complexConjugationCLM
        hIntegrable).symm
  | simpa [complexConjugationCLM] using
      (ContinuousLinearMap.integral_comp_comm complexConjugationCLM
        hIntegrable)

/-- Canonical Schwarz symmetry of the unnormalized Mellin integral in the
certified convergence half-plane. -/
theorem mellinIntegral_schwarz_of_convergent
    {heatTrace : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart)
    (spectral : Complex)
    (hSpectral : continuation.convergenceAbscissa < spectral.re) :
    relativeHeatMellinIntegral heatTrace spectral =
      Complex.conj
        (relativeHeatMellinIntegral heatTrace (Complex.conj spectral)) := by
  have hConjugate :
      continuation.convergenceAbscissa < (Complex.conj spectral).re := by
    simpa using hSpectral
  have hIntegrable : IntegrableOn
      (relativeHeatMellinKernel heatTrace (Complex.conj spectral))
      (Set.Ioi (0 : Real)) :=
    continuation.mellin_integrable (Complex.conj spectral) hConjugate
  calc
    relativeHeatMellinIntegral heatTrace spectral =
        ∫ time in Set.Ioi (0 : Real),
          relativeHeatMellinKernel heatTrace spectral time := rfl
    _ = ∫ time in Set.Ioi (0 : Real),
        Complex.conj
          (relativeHeatMellinKernel heatTrace
            (Complex.conj spectral) time) := by
      apply integral_congr_ae
      filter_upwards [] with time
      exact relativeHeatMellinKernel_schwarz heatTrace spectral time
    _ = Complex.conj
        (∫ time in Set.Ioi (0 : Real),
          relativeHeatMellinKernel heatTrace
            (Complex.conj spectral) time) := by
      exact integral_complexConjugation hIntegrable
    _ = Complex.conj
        (relativeHeatMellinIntegral heatTrace (Complex.conj spectral)) := rfl

/-- Canonical Schwarz symmetry of the Gamma-normalized Mellin candidate in the
certified convergence half-plane. -/
theorem mellinCandidate_schwarz_of_convergent
    {heatTrace : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart)
    (spectral : Complex)
    (hSpectral : continuation.convergenceAbscissa < spectral.re) :
    relativeHeatMellinZetaCandidate heatTrace spectral =
      Complex.conj
        (relativeHeatMellinZetaCandidate heatTrace
          (Complex.conj spectral)) := by
  calc
    relativeHeatMellinZetaCandidate heatTrace spectral =
        (Complex.conj (Complex.Gamma (Complex.conj spectral)))⁻¹ *
          Complex.conj
            (relativeHeatMellinIntegral heatTrace
              (Complex.conj spectral)) := by
      rw [relativeHeatMellinZetaCandidate,
        complexGamma_schwarz spectral,
        continuation.mellinIntegral_schwarz_of_convergent spectral hSpectral]
    _ = Complex.conj
        ((Complex.Gamma (Complex.conj spectral))⁻¹ *
          relativeHeatMellinIntegral heatTrace
            (Complex.conj spectral)) := by
      simp
    _ = Complex.conj
        (relativeHeatMellinZetaCandidate heatTrace
          (Complex.conj spectral)) := rfl

/-- Analytic domain joining the canonical Mellin Schwarz identity to zero. -/
structure RelativeHeatMellinZetaCanonicalSchwarzReflectionData
    {heatTrace : HeatTime → Real}
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

namespace RelativeHeatMellinZetaCanonicalSchwarzReflectionData

/-- In the convergence half-plane the continuation equals its Schwarz
reflection without an additional field. -/
theorem zeta_eq_schwarz_of_mellin
    {heatTrace : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (_data : RelativeHeatMellinZetaCanonicalSchwarzReflectionData continuation)
    (spectral : Complex)
    (hSpectral : continuation.convergenceAbscissa < spectral.re) :
    continuation.zeta spectral = schwarzReflect continuation.zeta spectral := by
  have hConjugate :
      continuation.convergenceAbscissa < (Complex.conj spectral).re := by
    simpa using hSpectral
  calc
    continuation.zeta spectral =
        relativeHeatMellinZetaCandidate heatTrace spectral :=
      continuation.zeta_eq_mellin spectral hSpectral
    _ = Complex.conj
        (relativeHeatMellinZetaCandidate heatTrace
          (Complex.conj spectral)) :=
      continuation.mellinCandidate_schwarz_of_convergent spectral hSpectral
    _ = Complex.conj (continuation.zeta (Complex.conj spectral)) := by
      rw [← continuation.zeta_eq_mellin (Complex.conj spectral) hConjugate]
    _ = schwarzReflect continuation.zeta spectral := rfl

/-- The two analytic functions agree near the Mellin seed. -/
theorem eventuallyEq_zeta_reflection_at_seed
    {heatTrace : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (data : RelativeHeatMellinZetaCanonicalSchwarzReflectionData continuation) :
    continuation.zeta =ᶠ[𝓝 data.seed]
      schwarzReflect continuation.zeta := by
  have hOpen : IsOpen {spectral : Complex |
      continuation.convergenceAbscissa < spectral.re} :=
    isOpen_lt continuous_const Complex.continuous_re
  have hNeighborhood :
      {spectral : Complex |
        continuation.convergenceAbscissa < spectral.re} ∈ 𝓝 data.seed :=
    hOpen.mem_nhds data.seed_mem_mellinHalfPlane
  filter_upwards [hNeighborhood] with spectral hSpectral
  exact data.zeta_eq_schwarz_of_mellin spectral hSpectral

/-- Analytic uniqueness propagates canonical Schwarz symmetry through the
common domain. -/
theorem zeta_eqOn_schwarz_domain
    {heatTrace : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (data : RelativeHeatMellinZetaCanonicalSchwarzReflectionData continuation) :
    Set.EqOn continuation.zeta (schwarzReflect continuation.zeta) data.domain :=
  data.zeta_analytic.eqOn_of_preconnected_of_eventuallyEq
    data.reflected_analytic data.isPreconnected_domain data.seed_mem_domain
      data.eventuallyEq_zeta_reflection_at_seed

/-- The real axis belongs to the analytic domain near zero. -/
theorem eventually_realAxis_mem_domain
    {heatTrace : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (data : RelativeHeatMellinZetaCanonicalSchwarzReflectionData continuation) :
    ∀ᶠ spectral : Real in 𝓝 0, (spectral : Complex) ∈ data.domain := by
  have hDomain : data.domain ∈ 𝓝 (0 : Complex) :=
    data.isOpen_domain.mem_nhds data.zero_mem_domain
  have hOfReal :
      Tendsto (fun spectral : Real => (spectral : Complex))
        (𝓝 0) (𝓝 (0 : Complex)) := by
    simpa using continuous_ofReal.continuousAt
  exact hOfReal hDomain

/-- Canonical Schwarz symmetry gives a real-axis germ. -/
def toRealAxisReality
    {heatTrace : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (data : RelativeHeatMellinZetaCanonicalSchwarzReflectionData continuation) :
    RelativeHeatMellinZetaRealAxisRealityData continuation where
  eventually_im_zero := by
    filter_upwards [data.eventually_realAxis_mem_domain] with spectral hSpectral
    have hReflection := data.zeta_eqOn_schwarz_domain hSpectral
    have hFixed :
        continuation.zeta (spectral : Complex) =
          Complex.conj (continuation.zeta (spectral : Complex)) := by
      simpa [schwarzReflect] using hReflection
    have hImaginary := congrArg Complex.im hFixed
    simp only [Complex.conj_im] at hImaginary
    linarith

/-- Reality of the regularized derivative is completely canonical once the
reflected function is analytic on the common domain. -/
theorem derivativeAtZero_im_eq_zero
    {heatTrace : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    {continuation : RelativeHeatMellinZetaContinuationData finitePart}
    (data : RelativeHeatMellinZetaCanonicalSchwarzReflectionData continuation) :
    continuation.derivativeAtZero.im = 0 :=
  data.toRealAxisReality.derivativeAtZero_im_eq_zero

/-- Public canonical Schwarz-reflection checkpoint. -/
theorem relative_heat_mellin_zeta_canonical_schwarz_reflection_gate
    {heatTrace : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (continuation : RelativeHeatMellinZetaContinuationData finitePart)
    (data : RelativeHeatMellinZetaCanonicalSchwarzReflectionData continuation) :
    Set.EqOn continuation.zeta (schwarzReflect continuation.zeta) data.domain ∧
    continuation.derivativeAtZero.im = 0 :=
  ⟨data.zeta_eqOn_schwarz_domain,
    data.derivativeAtZero_im_eq_zero⟩

end RelativeHeatMellinZetaCanonicalSchwarzReflectionData

end
end P0EFTJanusProgramPRelativeHeatMellinZetaCanonicalSchwarzReflection4D
end JanusFormal
