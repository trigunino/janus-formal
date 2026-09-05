import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalDivergenceLocalStokesSeparation4D
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Separation of the holonomic density divergence on an open neighborhood

Only tests compactly supported inside the measured coordinate neighborhood
are required. Global Euclidean Stokes and the local fundamental lemma then
give pointwise vanishing on that neighborhood.
-/

namespace JanusFormal
namespace P0EFTJanusHolonomicLocalDivergenceOpenSeparation4D

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ContDiff
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceLocalFormula4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceLocalStokesSeparation4D

private abbrev Vector4 := Fin 4 → Real

/-- The unspecified normalization of `addHaar` does not affect zero integrals. -/
theorem integral_addHaar_eq_zero_of_volume_eq_zero
    (integrand : Vector4 → Real)
    (hIntegral : (∫ coordinate, integrand coordinate ∂volume) = 0) :
    (∫ coordinate, integrand coordinate ∂Measure.addHaar) = 0 := by
  rw [Measure.isAddLeftInvariant_eq_smul
    (Measure.addHaar : Measure Vector4) (volume : Measure Vector4),
    integral_smul_nnreal_measure, hIntegral, smul_zero]

/-- Tests supported inside an open set separate the weighted divergence there. -/
theorem holonomicLocalDensityDivergence_eq_zero_on_open_of_test_pairing
    (domain : Set Vector4) (hOpen : IsOpen domain)
    (density : Vector4 → Real) (field : Vector4 → Vector4)
    (hDensity : ContDiff Real ∞ density)
    (hDensityNe : ∀ coordinate, density coordinate ≠ 0)
    (hField : ContDiff Real ∞ field)
    (hWeak : ∀ test : Vector4 → Real,
      ContDiff Real ∞ test → HasCompactSupport test → tsupport test ⊆ domain →
        (∫ coordinate, test coordinate * density coordinate *
          holonomicLocalDensityDivergence density field coordinate ∂Measure.addHaar) = 0) :
    ∀ coordinate ∈ domain, holonomicLocalDensityDivergence density field coordinate = 0 := by
  let weightedResidual : Vector4 → Real := fun coordinate =>
    density coordinate * holonomicLocalDensityDivergence density field coordinate
  have hContinuous : Continuous weightedResidual :=
    hDensity.continuous.mul
      (holonomicLocalDensityDivergence_continuous density field hDensity hDensityNe hField)
  have hAE : ∀ᵐ coordinate ∂(Measure.addHaar : Measure Vector4),
      coordinate ∈ domain → weightedResidual coordinate = 0 := by
    apply hOpen.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (hContinuous.locallyIntegrable.locallyIntegrableOn domain)
    intro test hTest hCompact hSupport
    simpa only [weightedResidual, smul_eq_mul, mul_assoc] using
      hWeak test hTest hCompact hSupport
  have hRestricted : weightedResidual =ᵐ[(Measure.addHaar : Measure Vector4).restrict domain]
      (fun _ => 0) :=
    (ae_restrict_iff' hOpen.measurableSet).2 hAE
  have hEverywhere : EqOn weightedResidual (fun _ => 0) domain :=
    Measure.eqOn_open_of_ae_eq (μ := (Measure.addHaar : Measure Vector4)) hRestricted hOpen
      hContinuous.continuousOn continuous_const.continuousOn
  intro coordinate hCoordinate
  have hWeighted := hEverywhere hCoordinate
  change density coordinate * holonomicLocalDensityDivergence density field coordinate = 0
    at hWeighted
  exact (mul_eq_zero.mp hWeighted).resolve_left (hDensityNe coordinate)

/-- Vanishing local test advection implies pointwise zero density divergence
on the measured open neighborhood. -/
theorem holonomicLocalDensityDivergence_eq_zero_on_open_of_advection
    (domain : Set Vector4) (hOpen : IsOpen domain)
    (density : Vector4 → Real) (field : Vector4 → Vector4)
    (hDensity : ContDiff Real ∞ density)
    (hDensityNe : ∀ coordinate, density coordinate ≠ 0)
    (hField : ContDiff Real ∞ field)
    (hAdvection : ∀ test : Vector4 → Real,
      ContDiff Real ∞ test → HasCompactSupport test → tsupport test ⊆ domain →
        (∫ coordinate, density coordinate * fderiv Real test coordinate (field coordinate)
          ∂Measure.addHaar) = 0) :
    ∀ coordinate ∈ domain, holonomicLocalDensityDivergence density field coordinate = 0 := by
  apply holonomicLocalDensityDivergence_eq_zero_on_open_of_test_pairing
    domain hOpen density field hDensity hDensityNe hField
  intro test hTest hCompact hSupport
  rw [integral_test_mul_density_divergence_eq_neg_advection
    density field test hDensity hDensityNe hField hTest hCompact,
    hAdvection test hTest hCompact hSupport, neg_zero]

/-- The open separation theorem accepts the literal Lebesgue volume produced
by the canonical holonomic measure transport. -/
theorem holonomic_local_divergence_open_separation_gate
    (domain : Set Vector4) (hOpen : IsOpen domain)
    (density : Vector4 → Real) (field : Vector4 → Vector4)
    (hDensity : ContDiff Real ∞ density)
    (hDensityNe : ∀ coordinate, density coordinate ≠ 0)
    (hField : ContDiff Real ∞ field)
    (hAdvection : ∀ test : Vector4 → Real,
      ContDiff Real ∞ test → HasCompactSupport test → tsupport test ⊆ domain →
        (∫ coordinate, density coordinate * fderiv Real test coordinate (field coordinate)
          ∂volume) = 0) :
    ∀ coordinate ∈ domain, holonomicLocalDensityDivergence density field coordinate = 0 := by
  apply holonomicLocalDensityDivergence_eq_zero_on_open_of_advection
    domain hOpen density field hDensity hDensityNe hField
  intro test hTest hCompact hSupport
  exact integral_addHaar_eq_zero_of_volume_eq_zero _
    (hAdvection test hTest hCompact hSupport)

end
end P0EFTJanusHolonomicLocalDivergenceOpenSeparation4D
end JanusFormal
