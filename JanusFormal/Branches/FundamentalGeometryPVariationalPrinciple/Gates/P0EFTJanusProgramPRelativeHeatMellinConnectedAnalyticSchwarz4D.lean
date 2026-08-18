import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.Complex.CauchyIntegral
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinConnectedAnalyticContinuation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaCanonicalSchwarzReflection4D

/-!
# Schwarz reflection from a connected analytic Mellin continuation

On a conjugation-invariant analytic domain, analyticity of a zeta function
automatically gives analyticity of its Schwarz reflection.  This removes the
second analytic field from the canonical reflection packet.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatMellinConnectedAnalyticSchwarz4D

set_option autoImplicit false
noncomputable section

open Filter Set Topology
open scoped ComplexConjugate
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinConnectedAnalyticContinuation4D
open P0EFTJanusProgramPRelativeHeatMellinZetaCanonicalSchwarzReflection4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeHeatMellinZetaSchwarzReflection4D

/-- Schwarz reflection preserves analyticity on a conjugation-invariant
domain. -/
theorem schwarzReflect_analyticOnNhd
    {heatTrace : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (data : RelativeHeatMellinConnectedAnalyticContinuationData finitePart)
    (conj_mem_domain : ∀ spectral ∈ data.domain,
      conj spectral ∈ data.domain) :
    AnalyticOnNhd Complex (schwarzReflect data.continuation.zeta)
      data.domain := by
  intro spectral hSpectral
  rw [Complex.analyticAt_iff_eventually_differentiableAt]
  have hAnalytic := data.zeta_analytic
    (conj spectral) (conj_mem_domain spectral hSpectral)
  rw [Complex.analyticAt_iff_eventually_differentiableAt] at hAnalytic
  have hConj : Tendsto conj (𝓝 spectral) (𝓝 (conj spectral)) :=
    Complex.continuous_conj.continuousAt
  filter_upwards [hConj.eventually hAnalytic] with current hCurrent
  change DifferentiableAt Complex
    (conj ∘ data.continuation.zeta ∘ conj) current
  rw [differentiableAt_conj_conj_iff]
  exact hCurrent

/-- A connected analytic continuation on a conjugation-invariant domain
supplies the canonical Schwarz packet without a separate reflected-analytic
hypothesis. -/
def toCanonicalSchwarzReflection
    {heatTrace : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (data : RelativeHeatMellinConnectedAnalyticContinuationData finitePart)
    (conj_mem_domain : ∀ spectral ∈ data.domain,
      conj spectral ∈ data.domain) :
    RelativeHeatMellinZetaCanonicalSchwarzReflectionData
      data.continuation where
  domain := data.domain
  isOpen_domain := data.isOpen_domain
  isPreconnected_domain := data.isPreconnected_domain
  zero_mem_domain := data.zero_mem_domain
  seed := data.seed
  seed_mem_domain := data.seed_mem_domain
  seed_mem_mellinHalfPlane := data.seed_mem_mellinHalfPlane
  zeta_analytic := data.zeta_analytic
  reflected_analytic := schwarzReflect_analyticOnNhd data conj_mem_domain

/-- Public checkpoint: connected analyticity and conjugation invariance force
Schwarz symmetry through the domain and reality of the zeta derivative. -/
theorem relative_heat_mellin_connected_analytic_schwarz_gate
    {heatTrace : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (data : RelativeHeatMellinConnectedAnalyticContinuationData finitePart)
    (conj_mem_domain : ∀ spectral ∈ data.domain,
      conj spectral ∈ data.domain) :
    Set.EqOn data.continuation.zeta
        (schwarzReflect data.continuation.zeta) data.domain ∧
      data.continuation.derivativeAtZero.im = 0 := by
  let reflection := toCanonicalSchwarzReflection data conj_mem_domain
  exact ⟨reflection.zeta_eqOn_schwarz_domain,
    reflection.derivativeAtZero_im_eq_zero⟩

end
end P0EFTJanusProgramPRelativeHeatMellinConnectedAnalyticSchwarz4D
end JanusFormal
