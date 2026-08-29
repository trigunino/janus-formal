import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Calculus.FDeriv.Congr
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D

/-!
# Uniqueness of the relative heat Mellin continuation

`RelativeHeatMellinZetaContinuationData` records the Mellin formula in a right
half-plane and differentiability at zero.  By itself, those two local
statements do not connect the germ at zero to the Mellin half-plane.

This file adds the missing global analytic comparison.  Two continuations of
the same relative heat trace are required to be analytic on one common open
preconnected domain containing

* zero; and
* one seed point in the intersection of their Mellin half-planes.

Around that seed, both functions equal the same Gamma-normalized Mellin
transform.  The analytic identity principle therefore forces equality on the
whole common domain, in particular near zero.  Their derivatives at zero,
finite-part logarithms and complex zeta determinants are consequently equal.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeHeatMellinAnalyticContinuationUniqueness4D

set_option autoImplicit false
noncomputable section

open Filter Set Topology
open P0EFTJanusCircleDiracHeatTraceCancellation
open P0EFTJanusProgramPRelativeHeatFinitePartDeterminant4D
open P0EFTJanusProgramPRelativeHeatMellinZetaContinuation4D
open P0EFTJanusProgramPRelativeZetaComparison4D

/-- A common analytic domain joining the Mellin half-plane to the origin for
two continuations of the same heat trace. -/
structure RelativeHeatMellinAnalyticContinuationComparisonData
    {heatTrace : HeatTime → Real}
    {firstFinitePart secondFinitePart : RelativeHeatFinitePartData heatTrace}
    (first : RelativeHeatMellinZetaContinuationData firstFinitePart)
    (second : RelativeHeatMellinZetaContinuationData secondFinitePart) where
  domain : Set Complex
  isOpen_domain : IsOpen domain
  isPreconnected_domain : IsPreconnected domain
  zero_mem_domain : (0 : Complex) ∈ domain
  seed : Complex
  seed_mem_domain : seed ∈ domain
  seed_mem_commonMellinHalfPlane :
    max first.convergenceAbscissa second.convergenceAbscissa < seed.re
  first_analytic : AnalyticOnNhd Complex first.zeta domain
  second_analytic : AnalyticOnNhd Complex second.zeta domain

namespace RelativeHeatMellinAnalyticContinuationComparisonData

/-- The intersection of the two certified Mellin half-planes is open. -/
theorem isOpen_commonMellinHalfPlane
    {heatTrace : HeatTime → Real}
    {firstFinitePart secondFinitePart : RelativeHeatFinitePartData heatTrace}
    {first : RelativeHeatMellinZetaContinuationData firstFinitePart}
    {second : RelativeHeatMellinZetaContinuationData secondFinitePart}
    (data : RelativeHeatMellinAnalyticContinuationComparisonData first second) :
    IsOpen {spectral : Complex |
      max first.convergenceAbscissa second.convergenceAbscissa < spectral.re} := by
  exact isOpen_lt continuous_const Complex.continuous_re

/-- The two zeta functions coincide on a full neighborhood of the seed because
both are the same Mellin transform there. -/
theorem eventuallyEq_zeta_at_seed
    {heatTrace : HeatTime → Real}
    {firstFinitePart secondFinitePart : RelativeHeatFinitePartData heatTrace}
    {first : RelativeHeatMellinZetaContinuationData firstFinitePart}
    {second : RelativeHeatMellinZetaContinuationData secondFinitePart}
    (data : RelativeHeatMellinAnalyticContinuationComparisonData first second) :
    first.zeta =ᶠ[𝓝 data.seed] second.zeta := by
  have hNeighborhood :
      {spectral : Complex |
        max first.convergenceAbscissa second.convergenceAbscissa < spectral.re} ∈
        𝓝 data.seed :=
    data.isOpen_commonMellinHalfPlane.mem_nhds
      data.seed_mem_commonMellinHalfPlane
  filter_upwards [hNeighborhood] with spectral hSpectral
  have hFirst : first.convergenceAbscissa < spectral.re :=
    lt_of_le_of_lt (le_max_left _ _) hSpectral
  have hSecond : second.convergenceAbscissa < spectral.re :=
    lt_of_le_of_lt (le_max_right _ _) hSpectral
  calc
    first.zeta spectral = relativeHeatMellinZetaCandidate heatTrace spectral :=
      first.zeta_eq_mellin spectral hFirst
    _ = second.zeta spectral :=
      (second.zeta_eq_mellin spectral hSecond).symm

/-- Identity principle: both continuations coincide throughout the common
analytic domain. -/
theorem zeta_eqOn_domain
    {heatTrace : HeatTime → Real}
    {firstFinitePart secondFinitePart : RelativeHeatFinitePartData heatTrace}
    {first : RelativeHeatMellinZetaContinuationData firstFinitePart}
    {second : RelativeHeatMellinZetaContinuationData secondFinitePart}
    (data : RelativeHeatMellinAnalyticContinuationComparisonData first second) :
    Set.EqOn first.zeta second.zeta data.domain :=
  data.first_analytic.eqOn_of_preconnected_of_eventuallyEq
    data.second_analytic data.isPreconnected_domain data.seed_mem_domain
      data.eventuallyEq_zeta_at_seed

/-- Since zero belongs to the open comparison domain, the two zeta functions
coincide on a neighborhood of zero. -/
theorem eventuallyEq_zeta_at_zero
    {heatTrace : HeatTime → Real}
    {firstFinitePart secondFinitePart : RelativeHeatFinitePartData heatTrace}
    {first : RelativeHeatMellinZetaContinuationData firstFinitePart}
    {second : RelativeHeatMellinZetaContinuationData secondFinitePart}
    (data : RelativeHeatMellinAnalyticContinuationComparisonData first second) :
    first.zeta =ᶠ[𝓝 (0 : Complex)] second.zeta := by
  have hDomain : data.domain ∈ 𝓝 (0 : Complex) :=
    data.isOpen_domain.mem_nhds data.zero_mem_domain
  filter_upwards [hDomain] with spectral hSpectral
  exact data.zeta_eqOn_domain hSpectral

/-- The analytic continuations have the same derivative at zero. -/
theorem derivativeAtZero_eq
    {heatTrace : HeatTime → Real}
    {firstFinitePart secondFinitePart : RelativeHeatFinitePartData heatTrace}
    {first : RelativeHeatMellinZetaContinuationData firstFinitePart}
    {second : RelativeHeatMellinZetaContinuationData secondFinitePart}
    (data : RelativeHeatMellinAnalyticContinuationComparisonData first second) :
    first.derivativeAtZero = second.derivativeAtZero := by
  have hSecondAsFirst :
      HasDerivAt first.zeta second.derivativeAtZero 0 :=
    second.hasDerivAt_zero.congr_of_eventuallyEq
      data.eventuallyEq_zeta_at_zero
  exact first.hasDerivAt_zero.unique hSecondAsFirst

/-- The two finite-part logarithms are forced to agree. -/
theorem finitePartLogDeterminant_eq
    {heatTrace : HeatTime → Real}
    {firstFinitePart secondFinitePart : RelativeHeatFinitePartData heatTrace}
    {first : RelativeHeatMellinZetaContinuationData firstFinitePart}
    {second : RelativeHeatMellinZetaContinuationData secondFinitePart}
    (data : RelativeHeatMellinAnalyticContinuationComparisonData first second) :
    relativeHeatFinitePartLogDeterminant firstFinitePart =
      relativeHeatFinitePartLogDeterminant secondFinitePart := by
  calc
    relativeHeatFinitePartLogDeterminant firstFinitePart =
        -first.derivativeAtZero.re := first.finitePart_realPart
    _ = -second.derivativeAtZero.re := by
      rw [data.derivativeAtZero_eq]
    _ = relativeHeatFinitePartLogDeterminant secondFinitePart :=
      second.finitePart_realPart.symm

/-- The complex zeta determinants are independent of the chosen analytic
continuation. -/
theorem zetaDeterminant_eq
    {heatTrace : HeatTime → Real}
    {firstFinitePart secondFinitePart : RelativeHeatFinitePartData heatTrace}
    {first : RelativeHeatMellinZetaContinuationData firstFinitePart}
    {second : RelativeHeatMellinZetaContinuationData secondFinitePart}
    (data : RelativeHeatMellinAnalyticContinuationComparisonData first second) :
    relativeHeatMellinZetaDeterminant first =
      relativeHeatMellinZetaDeterminant second := by
  unfold relativeHeatMellinZetaDeterminant relativeZetaDeterminant
  rw [data.derivativeAtZero_eq]

/-- Public analytic-continuation uniqueness checkpoint. -/
theorem relative_heat_mellin_analytic_continuation_uniqueness_gate
    {heatTrace : HeatTime → Real}
    {firstFinitePart secondFinitePart : RelativeHeatFinitePartData heatTrace}
    (first : RelativeHeatMellinZetaContinuationData firstFinitePart)
    (second : RelativeHeatMellinZetaContinuationData secondFinitePart)
    (data : RelativeHeatMellinAnalyticContinuationComparisonData first second) :
    Set.EqOn first.zeta second.zeta data.domain ∧
    first.derivativeAtZero = second.derivativeAtZero ∧
    relativeHeatFinitePartLogDeterminant firstFinitePart =
      relativeHeatFinitePartLogDeterminant secondFinitePart ∧
    relativeHeatMellinZetaDeterminant first =
      relativeHeatMellinZetaDeterminant second :=
  ⟨data.zeta_eqOn_domain,
    data.derivativeAtZero_eq,
    data.finitePartLogDeterminant_eq,
    data.zetaDeterminant_eq⟩

end RelativeHeatMellinAnalyticContinuationComparisonData

end
end P0EFTJanusProgramPRelativeHeatMellinAnalyticContinuationUniqueness4D
end JanusFormal
