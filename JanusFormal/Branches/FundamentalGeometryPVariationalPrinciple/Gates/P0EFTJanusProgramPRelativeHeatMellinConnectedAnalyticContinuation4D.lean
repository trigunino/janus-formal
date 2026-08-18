import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

/-!
# Connected analytic relative heat Mellin continuations

The basic continuation packet records the Mellin formula in a right half-plane
and a derivative at zero.  This stronger packet puts both regions in one open
preconnected analytic domain containing zero and a Mellin seed.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatMellinConnectedAnalyticContinuation4D

set_option autoImplicit false
noncomputable section

open Filter Set Topology
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

/-- A Mellin continuation analytically connected from its convergence
half-plane to the origin. -/
structure RelativeHeatMellinConnectedAnalyticContinuationData
    {heatTrace : HeatTime → Real}
    (finitePart : RelativeHeatFinitePartData heatTrace) where
  continuation : RelativeHeatMellinZetaContinuationData finitePart
  domain : Set Complex
  isOpen_domain : IsOpen domain
  isPreconnected_domain : IsPreconnected domain
  zero_mem_domain : (0 : Complex) ∈ domain
  seed : Complex
  seed_mem_domain : seed ∈ domain
  seed_mem_mellinHalfPlane : continuation.convergenceAbscissa < seed.re
  zeta_analytic : AnalyticOnNhd Complex continuation.zeta domain

namespace RelativeHeatMellinConnectedAnalyticContinuationData

theorem isOpen_mellinHalfPlane
    {heatTrace : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (data : RelativeHeatMellinConnectedAnalyticContinuationData finitePart) :
    IsOpen {spectral : Complex |
      data.continuation.convergenceAbscissa < spectral.re} :=
  isOpen_lt continuous_const Complex.continuous_re

/-- The certified continuation agrees with the Mellin transform on a full
neighborhood of its seed, not merely at one point. -/
theorem eventuallyEq_mellin_at_seed
    {heatTrace : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (data : RelativeHeatMellinConnectedAnalyticContinuationData finitePart) :
    data.continuation.zeta =ᶠ[𝓝 data.seed]
      relativeHeatMellinZetaCandidate heatTrace := by
  have hNeighborhood :
      {spectral : Complex |
        data.continuation.convergenceAbscissa < spectral.re} ∈ 𝓝 data.seed :=
    data.isOpen_mellinHalfPlane.mem_nhds data.seed_mem_mellinHalfPlane
  filter_upwards [hNeighborhood] with spectral hSpectral
  exact data.continuation.zeta_eq_mellin spectral hSpectral

/-- Public checkpoint for a continuation whose Mellin and zero germs belong
to one analytic component. -/
theorem relative_heat_mellin_connected_analytic_continuation_gate
    {heatTrace : HeatTime → Real}
    {finitePart : RelativeHeatFinitePartData heatTrace}
    (data : RelativeHeatMellinConnectedAnalyticContinuationData finitePart) :
    IsOpen data.domain ∧
      IsPreconnected data.domain ∧
      (0 : Complex) ∈ data.domain ∧
      data.seed ∈ data.domain ∧
      data.continuation.convergenceAbscissa < data.seed.re ∧
      AnalyticOnNhd Complex data.continuation.zeta data.domain ∧
      data.continuation.zeta =ᶠ[𝓝 data.seed]
        relativeHeatMellinZetaCandidate heatTrace ∧
      relativeHeatMellinZetaDeterminant data.continuation ≠ 0 ∧
      ‖relativeHeatMellinZetaDeterminant data.continuation‖ =
        relativeHeatFinitePartDeterminant finitePart := by
  exact ⟨data.isOpen_domain, data.isPreconnected_domain,
    data.zero_mem_domain, data.seed_mem_domain,
    data.seed_mem_mellinHalfPlane, data.zeta_analytic,
    data.eventuallyEq_mellin_at_seed,
    relativeHeatMellinZetaDeterminant_gate data.continuation⟩

end RelativeHeatMellinConnectedAnalyticContinuationData

end
end P0EFTJanusProgramPRelativeHeatMellinConnectedAnalyticContinuation4D
end JanusFormal
