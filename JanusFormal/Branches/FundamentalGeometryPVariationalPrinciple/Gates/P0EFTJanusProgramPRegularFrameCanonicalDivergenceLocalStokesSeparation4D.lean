import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEuclideanWeightedLocalFormalAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalDivergenceLocalFormula4D

/-!
# Local Stokes and test separation for the canonical density divergence

This gate discharges the purely Euclidean analytic part of the remaining
canonical-divergence obstruction.  For a smooth nowhere-zero density it proves
the exact compact-support Stokes identity, then upgrades weak vanishing against
all smooth compactly supported tests to pointwise vanishing.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameCanonicalDivergenceLocalStokesSeparation4D

set_option autoImplicit false
set_option maxHeartbeats 2400000

noncomputable section

open MeasureTheory
open scoped ContDiff BigOperators
open P0EFTJanusEuclideanWeightedLocalFormalAdjoint4D
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceLocalFormula4D

private abbrev Index4 := Fin 4
private abbrev Vector4 := Index4 → Real

/-- Multiplying the weighted divergence by its nonzero density recovers its
coordinate numerator exactly. -/
theorem density_mul_holonomicLocalDensityDivergence
    (density : Vector4 → Real)
    (field : Vector4 → Vector4)
    (coordinate : Vector4)
    (hDensityNe : density coordinate ≠ 0) :
    density coordinate *
        holonomicLocalDensityDivergence density field coordinate =
      ∑ derivative : Index4,
        fderiv Real
          (fun current => density current * field current derivative)
          coordinate (Pi.single derivative 1) := by
  unfold holonomicLocalDensityDivergence
  field_simp [hDensityNe]

/-- The density divergence of smooth data is continuous. -/
theorem holonomicLocalDensityDivergence_continuous
    (density : Vector4 → Real)
    (field : Vector4 → Vector4)
    (hDensity : ContDiff Real ∞ density)
    (hDensityNe : ∀ coordinate, density coordinate ≠ 0)
    (hField : ContDiff Real ∞ field) :
    Continuous (holonomicLocalDensityDivergence density field) := by
  unfold holonomicLocalDensityDivergence
  apply Continuous.div _ hDensity.continuous hDensityNe
  apply continuous_finsetSum
  intro derivative _hDerivative
  have hWeightedComponent : ContDiff Real ∞ (fun coordinate =>
      density coordinate * field coordinate derivative) :=
    hDensity.mul ((contDiff_apply Real Real derivative).comp hField)
  exact (hWeightedComponent.continuous_fderiv (by simp)).clm_apply
    continuous_const

/-- A covector applied to a vector is the sum of its four coordinate
components. -/
theorem fderiv_apply_eq_coordinate_sum
    (test : Vector4 → Real)
    (field : Vector4 → Vector4)
    (coordinate : Vector4) :
    fderiv Real test coordinate (field coordinate) =
      ∑ derivative : Index4,
        fderiv Real test coordinate (Pi.single derivative 1) *
          field coordinate derivative := by
  conv_lhs => rw [pi_eq_sum_univ' (field coordinate)]
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro derivative _hDerivative
  ring

/-- Exact local Stokes identity.  Compact support of the scalar test removes
the boundary term; no decay condition is imposed on the vector field. -/
theorem integral_test_mul_density_divergence_eq_neg_advection
    (density : Vector4 → Real)
    (field : Vector4 → Vector4)
    (test : Vector4 → Real)
    (hDensity : ContDiff Real ∞ density)
    (hDensityNe : ∀ coordinate, density coordinate ≠ 0)
    (hField : ContDiff Real ∞ field)
    (hTest : ContDiff Real ∞ test)
    (hTestCompact : HasCompactSupport test) :
    (∫ coordinate,
        test coordinate * density coordinate *
          holonomicLocalDensityDivergence density field coordinate
        ∂Measure.addHaar) =
      -∫ coordinate,
        density coordinate *
          fderiv Real test coordinate (field coordinate)
        ∂Measure.addHaar := by
  let weightedComponent : Index4 → Vector4 → Real := fun derivative coordinate =>
    density coordinate * field coordinate derivative
  have hWeightedComponent (derivative : Index4) :
      ContDiff Real ∞ (weightedComponent derivative) := by
    exact hDensity.mul ((contDiff_apply Real Real derivative).comp hField)
  have hDerivativeWeightedComponent (derivative : Index4) :
      Continuous (fun coordinate =>
        fderiv Real (weightedComponent derivative) coordinate
          (Pi.single derivative 1)) :=
    ((hWeightedComponent derivative).continuous_fderiv (by simp)).clm_apply
      continuous_const
  have hDerivativeTest (derivative : Index4) :
      Continuous (fun coordinate =>
        fderiv Real test coordinate (Pi.single derivative 1)) :=
    (hTest.continuous_fderiv (by simp)).clm_apply continuous_const
  have hLeftIntegrable (derivative : Index4) :
      Integrable (fun coordinate =>
        test coordinate *
          fderiv Real (weightedComponent derivative) coordinate
            (Pi.single derivative 1)) Measure.addHaar :=
    (hTest.continuous.mul (hDerivativeWeightedComponent derivative)
      ).integrable_of_hasCompactSupport hTestCompact.mul_right
  have hRightIntegrable (derivative : Index4) :
      Integrable (fun coordinate =>
        fderiv Real test coordinate (Pi.single derivative 1) *
          weightedComponent derivative coordinate) Measure.addHaar :=
    ((hDerivativeTest derivative).mul
      (hWeightedComponent derivative).continuous
      ).integrable_of_hasCompactSupport
        (hTestCompact.fderiv_apply Real (Pi.single derivative 1)).mul_right
  have hCoordinateStokes (derivative : Index4) :
      (∫ coordinate,
          test coordinate *
            fderiv Real (weightedComponent derivative) coordinate
              (Pi.single derivative 1) ∂Measure.addHaar) =
        -∫ coordinate,
          fderiv Real test coordinate (Pi.single derivative 1) *
            weightedComponent derivative coordinate ∂Measure.addHaar := by
    simpa only [one_mul] using
      (integral_weighted_fderiv_eq_formalAdjoint
        (E := Vector4) (Pi.single derivative 1)
        (weightedComponent derivative) test (fun _ => 1) (fun _ => 1)
        (hWeightedComponent derivative) hTest contDiff_const contDiff_const
        hTestCompact)
  calc
    (∫ coordinate,
        test coordinate * density coordinate *
          holonomicLocalDensityDivergence density field coordinate
        ∂Measure.addHaar) =
        ∫ coordinate, ∑ derivative : Index4,
          test coordinate *
            fderiv Real (weightedComponent derivative) coordinate
              (Pi.single derivative 1) ∂Measure.addHaar := by
      apply integral_congr_ae
      filter_upwards
      intro coordinate
      rw [← Finset.mul_sum]
      calc
        test coordinate * density coordinate *
            holonomicLocalDensityDivergence density field coordinate =
          test coordinate *
            (density coordinate *
              holonomicLocalDensityDivergence density field coordinate) := by
              ring
        _ = test coordinate *
            (∑ derivative : Index4,
              fderiv Real
                (fun current => density current * field current derivative)
                coordinate (Pi.single derivative 1)) := by
          rw [density_mul_holonomicLocalDensityDivergence density field coordinate
            (hDensityNe coordinate)]
    _ = ∑ derivative : Index4,
          ∫ coordinate,
            test coordinate *
              fderiv Real (weightedComponent derivative) coordinate
                (Pi.single derivative 1) ∂Measure.addHaar := by
      rw [integral_finsetSum]
      exact fun derivative _hDerivative => hLeftIntegrable derivative
    _ = ∑ derivative : Index4,
          -(∫ coordinate,
            fderiv Real test coordinate (Pi.single derivative 1) *
              weightedComponent derivative coordinate ∂Measure.addHaar) := by
      apply Finset.sum_congr rfl
      intro derivative _hDerivative
      exact hCoordinateStokes derivative
    _ = -(∫ coordinate, ∑ derivative : Index4,
          fderiv Real test coordinate (Pi.single derivative 1) *
            weightedComponent derivative coordinate ∂Measure.addHaar) := by
      rw [Finset.sum_neg_distrib]
      congr 1
      symm
      rw [integral_finsetSum]
      exact fun derivative _hDerivative => hRightIntegrable derivative
    _ = -∫ coordinate,
          density coordinate *
            fderiv Real test coordinate (field coordinate)
          ∂Measure.addHaar := by
      congr 1
      apply integral_congr_ae
      filter_upwards
      intro coordinate
      rw [fderiv_apply_eq_coordinate_sum test field coordinate,
        Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro derivative _hDerivative
      dsimp only [weightedComponent]
      ring

/-- Fundamental lemma for the weighted local divergence: weak vanishing
against every smooth compactly supported test implies pointwise vanishing. -/
theorem holonomicLocalDensityDivergence_eq_zero_of_test_pairing
    (density : Vector4 → Real)
    (field : Vector4 → Vector4)
    (hDensity : ContDiff Real ∞ density)
    (hDensityNe : ∀ coordinate, density coordinate ≠ 0)
    (hField : ContDiff Real ∞ field)
    (hWeak : ∀ test : Vector4 → Real,
      ContDiff Real ∞ test → HasCompactSupport test →
        (∫ coordinate,
          test coordinate * density coordinate *
            holonomicLocalDensityDivergence density field coordinate
          ∂Measure.addHaar) = 0) :
    ∀ coordinate,
      holonomicLocalDensityDivergence density field coordinate = 0 := by
  let weightedResidual : Vector4 → Real := fun coordinate =>
    density coordinate *
      holonomicLocalDensityDivergence density field coordinate
  have hResidualContinuous : Continuous weightedResidual :=
    hDensity.continuous.mul
      (holonomicLocalDensityDivergence_continuous density field hDensity
        hDensityNe hField)
  have hAE : ∀ᵐ coordinate ∂Measure.addHaar,
      weightedResidual coordinate = 0 := by
    apply ae_eq_zero_of_integral_contDiff_smul_eq_zero
      hResidualContinuous.locallyIntegrable
    intro test hTest hTestCompact
    simpa only [weightedResidual, smul_eq_mul, mul_assoc] using
      hWeak test hTest hTestCompact
  have hEverywhere : weightedResidual = 0 :=
    (Continuous.ae_eq_iff_eq Measure.addHaar hResidualContinuous
      continuous_const).mp hAE
  intro coordinate
  have hAtCoordinate := congrFun hEverywhere coordinate
  dsimp only [weightedResidual] at hAtCoordinate
  exact (mul_eq_zero.mp hAtCoordinate).resolve_left (hDensityNe coordinate)

/-- Gate marker: both analytic obligations for a concrete local metric-volume
chart are closed; only geometric transport of that density remains. -/
theorem regular_frame_canonical_divergence_local_stokes_separation_gate :
    (∀ (density : Vector4 → Real) (field : Vector4 → Vector4)
        (test : Vector4 → Real),
      ContDiff Real ∞ density →
      (∀ coordinate, density coordinate ≠ 0) →
      ContDiff Real ∞ field →
      ContDiff Real ∞ test →
      HasCompactSupport test →
      (∫ coordinate,
          test coordinate * density coordinate *
            holonomicLocalDensityDivergence density field coordinate
          ∂Measure.addHaar) =
        -∫ coordinate,
          density coordinate *
            fderiv Real test coordinate (field coordinate)
          ∂Measure.addHaar) ∧
    (∀ (density : Vector4 → Real) (field : Vector4 → Vector4),
      ContDiff Real ∞ density →
      (∀ coordinate, density coordinate ≠ 0) →
      ContDiff Real ∞ field →
      (∀ test : Vector4 → Real,
        ContDiff Real ∞ test → HasCompactSupport test →
          (∫ coordinate,
            test coordinate * density coordinate *
              holonomicLocalDensityDivergence density field coordinate
            ∂Measure.addHaar) = 0) →
      ∀ coordinate,
        holonomicLocalDensityDivergence density field coordinate = 0) := by
  constructor
  · exact integral_test_mul_density_divergence_eq_neg_advection
  · exact holonomicLocalDensityDivergence_eq_zero_of_test_pairing

end
end P0EFTJanusProgramPRegularFrameCanonicalDivergenceLocalStokesSeparation4D
end JanusFormal
