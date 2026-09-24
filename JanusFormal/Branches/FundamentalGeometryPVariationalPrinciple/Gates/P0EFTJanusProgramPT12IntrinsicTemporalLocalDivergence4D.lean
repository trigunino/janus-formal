import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameCanonicalDivergenceLocalFormula4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCanonicalStereographicCoordinateTransport4D
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! Exact temporal divergence in the intrinsic stereographic metric density.
Coordinates are time first. The identification of a quotient scalar's raised
gradient with this temporal current remains separate from this local calculation. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicTemporalLocalDivergence4D
set_option autoImplicit false
noncomputable section
open scoped BigOperators ContDiff
open P0EFTJanusProgramPRegularFrameCanonicalDivergenceLocalFormula4D
open P0EFTJanusCanonicalStereographicCoordinateTransport4D

private abbrev Vector4 := Fin 4 → Real
private abbrev Space3 := Fin 3 → Real

private def spatialCoordinates : Vector4 →L[Real] Space3 :=
  ContinuousLinearMap.pi fun index => ContinuousLinearMap.proj index.succ

private theorem spatialCoordinates_time :
    spatialCoordinates (Pi.single (0 : Fin 4) 1) = 0 := by
  ext index
  simp [spatialCoordinates]

private theorem spatialDensity_fderiv_time
    (density : Space3 → Real) (coordinate : Vector4)
    (hDensity : DifferentiableAt Real density (spatialCoordinates coordinate)) :
    fderiv Real (density ∘ spatialCoordinates) coordinate (Pi.single (0 : Fin 4) 1) = 0 := by
  rw [fderiv_comp coordinate hDensity spatialCoordinates.differentiableAt,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.comp_apply, spatialCoordinates_time, map_zero]

private theorem spatialDensity_timeVector_divergence
    (density : Space3 → Real) (coordinate : Vector4)
    (hDensity : DifferentiableAt Real density (spatialCoordinates coordinate)) :
    holonomicLocalDensityDivergence (density ∘ spatialCoordinates)
      (fun _ => Pi.single (0 : Fin 4) 1) coordinate = 0 := by
  unfold holonomicLocalDensityDivergence
  have hSum : (∑ index : Fin 4,
      fderiv Real (fun current => (density ∘ spatialCoordinates) current *
        (Pi.single (0 : Fin 4) 1 : Vector4) index) coordinate (Pi.single index 1)) = 0 := by
    apply Finset.sum_eq_zero
    intro index _
    by_cases hIndex : index = 0
    · subst index
      simpa only [Pi.single_eq_same, mul_one] using
        spatialDensity_fderiv_time density coordinate hDensity
    · simp [hIndex]
  rw [hSum, zero_div]

/-- Purely temporal current in any differentiable, nonzero spatial density. -/
theorem holonomicSpatialDensity_negativeTimeCurrent
    (density : Space3 → Real) (profile : Real → Real) (coordinate : Vector4)
    (hDensity : DifferentiableAt Real density (spatialCoordinates coordinate))
    (hNonzero : density (spatialCoordinates coordinate) ≠ 0)
    (hProfile : DifferentiableAt Real profile (coordinate 0)) :
    holonomicLocalDensityDivergence (density ∘ spatialCoordinates)
      (fun current => (-profile (current 0)) • Pi.single (0 : Fin 4) 1) coordinate =
      -deriv profile (coordinate 0) := by
  have hScalar : HasFDerivAt (fun current : Vector4 => -profile (current 0))
      (-(deriv profile (coordinate 0) • ContinuousLinearMap.proj (0 : Fin 4))) coordinate :=
    (hProfile.hasDerivAt.comp_hasFDerivAt coordinate
      (ContinuousLinearMap.proj (0 : Fin 4) : Vector4 →L[Real] Real).hasFDerivAt).neg
  rw [holonomicLocalDensityDivergence_smul (density ∘ spatialCoordinates)
    (fun current => -profile (current 0)) (fun _ => Pi.single (0 : Fin 4) 1) coordinate
    (hDensity.comp coordinate spatialCoordinates.differentiableAt) hNonzero
    hScalar.differentiableAt (differentiableAt_const _),
    spatialDensity_timeVector_divergence density coordinate hDensity, mul_zero, zero_add]
  have hApply := congrArg (fun derivative : Vector4 →L[Real] Real =>
    derivative (Pi.single (0 : Fin 4) 1)) hScalar.fderiv
  simpa using hApply

/-- The actual intrinsic stereographic Lorentz volume factor. -/
def intrinsicTemporalSpatialDensity (space : Space3) : Real :=
  (4 / ((∑ index : Fin 3, space index ^ 2) + 4)) ^ 3

/-- The same volume factor in time-first coordinates. -/
def intrinsicTemporalCoordinateDensity (coordinate : Vector4) : Real :=
  intrinsicTemporalSpatialDensity (fun index => coordinate index.succ)

theorem intrinsicTemporalSpatialDensity_pos (space : Space3) :
    0 < intrinsicTemporalSpatialDensity space := by
  unfold intrinsicTemporalSpatialDensity
  positivity

theorem intrinsicTemporalSpatialDensity_contDiff :
    ContDiff Real ∞ intrinsicTemporalSpatialDensity := by
  unfold intrinsicTemporalSpatialDensity
  have hDenominator : ContDiff Real ∞ (fun space : Space3 =>
      (∑ index : Fin 3, space index ^ 2) + 4) := by fun_prop
  exact (contDiff_const.div hDenominator (fun space => ne_of_gt
    (add_pos_of_nonneg_of_pos (Finset.sum_nonneg (fun index _ => sq_nonneg (space index)))
      (by norm_num)))).pow 3

/-- This factor is the determinant density of the existing intrinsic product metric. -/
theorem intrinsicTemporalSpatialDensity_eq_metricVolume
    (space : EuclideanSpace Real (Fin 3)) (time : Real) :
    intrinsicTemporalSpatialDensity (fun index => space index) =
      Real.sqrt |(stereographicAmbientLorentzMatrix (space, time)).det| := by
  rw [stereographicAmbientLorentzMatrix_volume, EuclideanSpace.real_norm_sq_eq]
  rfl

/-- Local temporal wave calculation, with no assumed operator agreement. -/
theorem intrinsicTemporalLocalDivergence_eq_negative_second_deriv
    (field : Real → Real) (hField : ContDiff Real 2 field) (coordinate : Vector4) :
    holonomicLocalDensityDivergence intrinsicTemporalCoordinateDensity
      (fun current => (-deriv field (current 0)) • Pi.single (0 : Fin 4) 1) coordinate =
      -deriv (deriv field) (coordinate 0) :=
  holonomicSpatialDensity_negativeTimeCurrent intrinsicTemporalSpatialDensity (deriv field)
    coordinate (intrinsicTemporalSpatialDensity_contDiff.differentiable (by simp) _)
    (intrinsicTemporalSpatialDensity_pos _).ne'
    (hField.differentiable_deriv_two (coordinate 0))

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicTemporalLocalDivergence4D
