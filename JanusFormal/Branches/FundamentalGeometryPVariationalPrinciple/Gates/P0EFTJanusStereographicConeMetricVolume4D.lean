import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusStereographicInverseDifferential4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalStereographicExactVolume4D
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! # Metric volume of the actual stereographic cone

The radial extension used by Gate568 has three conformal spatial directions
and one unit radial direction. Its Gram determinant is evaluated explicitly.
-/

namespace JanusFormal
namespace P0EFTJanusStereographicConeMetricVolume4D

set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace
open MeasureTheory Set
open scoped ENNReal
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCanonicalPhysicalScalarStereographicVolumeComparison4D
open P0EFTJanusStereographicInverseDifferential4D
open P0EFTJanusMappingTorusCanonicalStereographicExactVolume4D

private abbrev Space3 := EuclideanSpace Real (Fin 3)
private abbrev RadialSpace := Space3 × Real
private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1
private abbrev Index4 := Fin 3 ⊕ Fin 1

theorem stereographicInverseVector_inner_fderiv
    (pole : StandardSphere) (coordinate direction : Space3) :
    ⟪stereographicInverseVector pole coordinate,
      fderiv Real (stereographicInverseVector pole) coordinate direction⟫ = 0 := by
  have hDerivative := (((stereographicInverseVector_contDiff pole).differentiable
    (by simp) coordinate).hasFDerivAt.norm_sq).fderiv
  simp only [norm_stereographicInverseVector, one_pow] at hDerivative
  rw [show fderiv Real (fun _ : Space3 => (1 : Real)) coordinate = 0 from
    (hasFDerivAt_const (1 : Real) coordinate).fderiv] at hDerivative
  have hApply := congrArg (fun derivative : Space3 →L[Real] Real =>
    derivative direction) hDerivative
  simpa [ContinuousLinearMap.comp_apply, innerSL_apply_apply] using hApply.symm

theorem stereographicConeMap_fderiv_apply
    (pole : StandardSphere) (coordinate direction : Space3) (radius speed : Real) :
    fderiv Real (stereographicConeMap pole) (coordinate, radius) (direction, speed) =
      radius • fderiv Real (stereographicInverseVector pole) coordinate direction +
        speed • stereographicInverseVector pole coordinate := by
  have hFst : HasFDerivAt (Prod.fst : RadialSpace → Space3)
      (ContinuousLinearMap.fst Real Space3 Real) (coordinate, radius) := hasFDerivAt_fst
  have hSnd : HasFDerivAt (Prod.snd : RadialSpace → Real)
      (ContinuousLinearMap.snd Real Space3 Real) (coordinate, radius) := hasFDerivAt_snd
  have hChart := ((stereographicInverseVector_contDiff pole).differentiable
    (by simp) coordinate).hasFDerivAt
  have hDerivative := (hSnd.smul (hChart.comp (coordinate, radius) hFst)).fderiv
  change fderiv Real (stereographicConeMap pole) (coordinate, radius) = _ at hDerivative
  exact congrArg (fun derivative : RadialSpace →L[Real] EuclideanR4 =>
    derivative (direction, speed)) hDerivative

theorem stereographicConeMap_fderiv_inner
    (pole : StandardSphere) (coordinate first second : Space3)
    (radius firstSpeed secondSpeed : Real) :
    ⟪fderiv Real (stereographicConeMap pole) (coordinate, radius) (first, firstSpeed),
      fderiv Real (stereographicConeMap pole) (coordinate, radius) (second, secondSpeed)⟫ =
      radius ^ 2 * (4 / (‖coordinate‖ ^ 2 + 4)) ^ 2 * ⟪first, second⟫ +
        firstSpeed * secondSpeed := by
  have hLeft : ⟪fderiv Real (stereographicInverseVector pole) coordinate first,
      stereographicInverseVector pole coordinate⟫ = 0 := by
    rw [real_inner_comm]
    exact stereographicInverseVector_inner_fderiv pole coordinate first
  simp only [stereographicConeMap_fderiv_apply, inner_add_left, inner_add_right,
    inner_smul_left, inner_smul_right, conj_trivial, hLeft,
    stereographicInverseVector_inner_fderiv, stereographicInverseVector_fderiv_inner,
    real_inner_self_eq_norm_sq, norm_stereographicInverseVector]
  ring

/-- Standard product-coordinate directions, spatial first and radial last. -/
def stereographicConeCoordinateBasis : Index4 → RadialSpace :=
  Sum.elim (fun index => (EuclideanSpace.basisFun (Fin 3) Real index, 0))
    (fun _ => (0, 1))

def stereographicConeGram (pole : StandardSphere) (coordinate : Space3) (radius : Real) :
    Matrix Index4 Index4 Real := fun first second =>
  ⟪fderiv Real (stereographicConeMap pole) (coordinate, radius)
      (stereographicConeCoordinateBasis first),
    fderiv Real (stereographicConeMap pole) (coordinate, radius)
      (stereographicConeCoordinateBasis second)⟫

theorem stereographicConeGram_eq_diagonal
    (pole : StandardSphere) (coordinate : Space3) (radius : Real) :
    stereographicConeGram pole coordinate radius =
      Matrix.diagonal (Sum.elim
        (fun _ : Fin 3 => radius ^ 2 * (4 / (‖coordinate‖ ^ 2 + 4)) ^ 2)
        (fun _ : Fin 1 => (1 : Real))) := by
  classical
  ext first second
  cases first with
  | inl first =>
    cases second with
    | inl second =>
      simp only [stereographicConeGram, stereographicConeCoordinateBasis, Sum.elim_inl,
        stereographicConeMap_fderiv_inner, mul_zero, add_zero]
      rw [EuclideanSpace.basisFun_inner]
      by_cases h : first = second
      · subst second; simp
      · simp [h, EuclideanSpace.basisFun_apply]
    | inr second => simp [stereographicConeGram, stereographicConeCoordinateBasis,
        stereographicConeMap_fderiv_inner]
  | inr first =>
    cases second with
    | inl second => simp [stereographicConeGram, stereographicConeCoordinateBasis,
        stereographicConeMap_fderiv_inner]
    | inr second =>
      have h : first = second := Subsingleton.elim _ _
      subst second
      simp only [stereographicConeGram, stereographicConeCoordinateBasis, Sum.elim_inr,
        stereographicConeMap_fderiv_inner]
      simp

theorem stereographicConeGram_det
    (pole : StandardSphere) (coordinate : Space3) (radius : Real) :
    (stereographicConeGram pole coordinate radius).det =
      radius ^ 6 * (4 / (‖coordinate‖ ^ 2 + 4)) ^ 6 := by
  rw [stereographicConeGram_eq_diagonal, Matrix.det_diagonal]
  simp [Fintype.prod_sum_type]
  ring

theorem stereographicConeGram_volume
    (pole : StandardSphere) (coordinate : Space3) (radius : Real) (hRadius : 0 ≤ radius) :
    Real.sqrt |(stereographicConeGram pole coordinate radius).det| =
      radius ^ 3 * (4 / (‖coordinate‖ ^ 2 + 4)) ^ 3 := by
  rw [stereographicConeGram_det, abs_of_nonneg (by positivity),
    show radius ^ 6 * (4 / (‖coordinate‖ ^ 2 + 4)) ^ 6 =
      (radius ^ 3 * (4 / (‖coordinate‖ ^ 2 + 4)) ^ 3) ^ 2 by ring,
    Real.sqrt_sq (by positivity)]

private def coneOrthonormalBasis : OrthonormalBasis Index4 Real EuclideanR4 :=
  ((EuclideanSpace.basisFun (Fin 3) Real).prod
    (OrthonormalBasis.singleton (Fin 1) Real)).map radialEuclideanIsometry

private theorem radialVolumeEquiv_coneOrthonormalBasis (index : Index4) :
    radialVolumeEquiv (coneOrthonormalBasis index) =
      stereographicConeCoordinateBasis index := by
  change (radialEuclideanIsometry.symm (radialEuclideanIsometry
    (((EuclideanSpace.basisFun (Fin 3) Real).prod
      (OrthonormalBasis.singleton (Fin 1) Real)) index))).ofLp = _
  rw [radialEuclideanIsometry.symm_apply_apply, OrthonormalBasis.prod_apply]
  cases index <;> simp [stereographicConeCoordinateBasis]

/-- A real endomorphism's Gram determinant in an orthonormal basis is its
Jacobian determinant squared. -/
theorem orthonormal_image_gram_det
    (basis : OrthonormalBasis Index4 Real EuclideanR4)
    (operator : EuclideanR4 →L[Real] EuclideanR4) :
    (Matrix.of (fun first second => ⟪operator (basis first), operator (basis second)⟫)).det =
      operator.det ^ 2 := by
  classical
  let matrix := LinearMap.toMatrix basis.toBasis basis.toBasis operator.toLinearMap
  have hGram : Matrix.of (fun first second =>
      ⟪operator (basis first), operator (basis second)⟫) = matrix.transpose * matrix := by
    ext first second
    change ⟪operator (basis first), operator (basis second)⟫ =
      ∑ index, matrix index first * matrix index second
    simp only [matrix, LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis]
    change ⟪operator (basis first), operator (basis second)⟫ =
      ∑ index, basis.repr (operator (basis first)) index *
        basis.repr (operator (basis second)) index
    simp_rw [basis.repr_apply_apply]
    rw [← basis.sum_inner_mul_inner (operator (basis first)) (operator (basis second))]
    apply Finset.sum_congr rfl
    intro index _
    rw [real_inner_comm (basis index) (operator (basis first))]
  rw [hGram, Matrix.det_mul, Matrix.det_transpose]
  change (LinearMap.toMatrix basis.toBasis basis.toBasis operator.toLinearMap).det *
      (LinearMap.toMatrix basis.toBasis basis.toBasis operator.toLinearMap).det = _
  rw [LinearMap.det_toMatrix]
  exact (pow_two operator.det).symm

private theorem euclideanStereographicCone_fderiv_basis
    (pole : StandardSphere) (coordinate : Space3) (radius : Real) (index : Index4) :
    fderiv Real (euclideanStereographicCone pole)
        (radialVolumeEquiv.symm (coordinate, radius)) (coneOrthonormalBasis index) =
      fderiv Real (stereographicConeMap pole) (coordinate, radius)
        (stereographicConeCoordinateBasis index) := by
  have hDerivative := (((stereographicConeMap_contDiff pole).differentiable (by simp)
    (radialVolumeEquiv (radialVolumeEquiv.symm (coordinate, radius)))).hasFDerivAt.comp
      (radialVolumeEquiv.symm (coordinate, radius)) radialVolumeEquiv.hasFDerivAt).fderiv
  change fderiv Real (euclideanStereographicCone pole)
    (radialVolumeEquiv.symm (coordinate, radius)) = _ at hDerivative
  rw [hDerivative]
  change fderiv Real (stereographicConeMap pole)
    (radialVolumeEquiv (radialVolumeEquiv.symm (coordinate, radius)))
    (radialVolumeEquiv (coneOrthonormalBasis index)) = _
  rw [radialVolumeEquiv.apply_symm_apply, radialVolumeEquiv_coneOrthonormalBasis]

/-- The actual absolute determinant integrated by Gate568 equals the
explicit radial metric volume, with its normalization fully fixed. -/
theorem stereographicConeJacobian_eq_metric_volume
    (pole : StandardSphere) (coordinate : Space3) (radius : Real) (hRadius : 0 ≤ radius) :
    stereographicConeJacobian pole (coordinate, radius) =
      ENNReal.ofReal (radius ^ 3 * (4 / (‖coordinate‖ ^ 2 + 4)) ^ 3) := by
  let operator := fderiv Real (euclideanStereographicCone pole)
    (radialVolumeEquiv.symm (coordinate, radius))
  have hGram := orthonormal_image_gram_det coneOrthonormalBasis operator
  have hMatrix : Matrix.of (fun first second =>
      ⟪operator (coneOrthonormalBasis first), operator (coneOrthonormalBasis second)⟫) =
      stereographicConeGram pole coordinate radius := by
    ext first second
    exact congrArg₂ (fun x y : EuclideanR4 => ⟪x, y⟫)
      (euclideanStereographicCone_fderiv_basis pole coordinate radius first)
      (euclideanStereographicCone_fderiv_basis pole coordinate radius second)
  rw [hMatrix, stereographicConeGram_det] at hGram
  have hSquare : |operator.det| ^ 2 =
      (radius ^ 3 * (4 / (‖coordinate‖ ^ 2 + 4)) ^ 3) ^ 2 := by
    rw [sq_abs, ← hGram]
    ring
  have hAbs := (sq_eq_sq₀ (abs_nonneg operator.det) (by positivity)).mp hSquare
  exact congrArg ENNReal.ofReal hAbs

theorem stereographicRadialShell_integral :
    (∫⁻ radius in Ico (1 : Real) 2, ENNReal.ofReal (radius ^ 3)) =
      ENNReal.ofReal (15 / 4 : Real) := by
  have hInt : IntegrableOn (fun radius : Real => radius ^ 3) (Ico (1 : Real) 2) :=
    ((continuous_id.pow 3).continuousOn.integrableOn_Icc).mono_set Ico_subset_Icc_self
  have hPos : (0 : Real → Real) ≤ᵐ[(volume : Measure Real).restrict (Ico 1 2)]
      (fun radius => radius ^ 3) := by
    filter_upwards [ae_restrict_mem measurableSet_Ico] with radius hRadius
    exact pow_nonneg (le_trans (by norm_num) hRadius.1) 3
  rw [← ofReal_integral_eq_lintegral_ofReal hInt hPos, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num), integral_pow]
  norm_num

/-- The exact measure density constructed by Gate568 is the metric density
computed in Gate569, after evaluating and integrating the cone Jacobian. -/
theorem stereographicExactSurfaceDensity_eq_metric
    (pole : StandardSphere) (coordinate : Space3) :
    stereographicExactSurfaceDensity pole coordinate =
      ENNReal.ofReal ((4 / (‖coordinate‖ ^ 2 + 4)) ^ 3) := by
  have hIntegral : (∫⁻ radius in Ico (1 : Real) 2,
      stereographicConeJacobian pole (coordinate, radius)) =
      ENNReal.ofReal ((4 / (‖coordinate‖ ^ 2 + 4)) ^ 3) *
        ENNReal.ofReal (15 / 4 : Real) := by
    calc
      _ = ∫⁻ radius in Ico (1 : Real) 2,
          ENNReal.ofReal ((4 / (‖coordinate‖ ^ 2 + 4)) ^ 3) *
            ENNReal.ofReal (radius ^ 3) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ico] with radius hRadius
        rw [stereographicConeJacobian_eq_metric_volume pole coordinate radius
          (le_trans (by norm_num) hRadius.1), mul_comm (radius ^ 3),
          ENNReal.ofReal_mul (by positivity)]
      _ = _ := by
        rw [lintegral_const_mul' _ _ (by simp), stereographicRadialShell_integral]
  rw [stereographicExactSurfaceDensity, hIntegral, mul_left_comm,
    ENNReal.inv_mul_cancel (by norm_num) (by simp), mul_one]

theorem stereographicSurfaceCoordinateMeasure_eq_metric_withDensity (pole : StandardSphere) :
    stereographicSurfaceCoordinateMeasure pole =
      (volume : Measure Space3).withDensity
        (fun coordinate => ENNReal.ofReal
          (Real.sqrt |(stereographicSpatialGram pole coordinate).det|)) := by
  rw [stereographicSurfaceCoordinateMeasure_eq_withDensity]
  congr 1
  funext coordinate
  rw [stereographicExactSurfaceDensity_eq_metric, stereographicSpatialGram_volume]

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarLocalVolumeTransport4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance : MeasurableSpace (MappingTorus (reflectedSphereData period hPeriod)) := borel _

/-- The concrete metric density transports exactly to canonical quotient
volume, including the time-shifted charts crossing the seam. -/
theorem shiftedCanonicalStereographic_metric_measurePreserving
    (shift : Real) (pole : StandardSphere) :
    MeasurePreserving
      (shiftedCanonicalInteriorStereographicPhysicalMap period hPeriod shift pole)
      ((canonicalInteriorStereographicLebesgueMeasure period).withDensity
        (fun point => ENNReal.ofReal
          (Real.sqrt |(stereographicSpatialGram pole point.1).det|)))
      ((intrinsicCanonicalLorentzVolumeMeasure period hPeriod).restrict
        (Set.range (shiftedCanonicalInteriorStereographicPhysicalMap
          period hPeriod shift pole))) := by
  simpa only [stereographicExactSurfaceDensity_eq_metric, stereographicSpatialGram_volume] using
    shiftedCanonicalInteriorStereographicPhysicalMap_exactDensity_measurePreserving
      period hPeriod shift pole

theorem stereographic_cone_metric_volume_gate (pole : StandardSphere) :
    stereographicSurfaceCoordinateMeasure pole =
      (volume : Measure Space3).withDensity
        (fun coordinate => ENNReal.ofReal
          (Real.sqrt |(stereographicSpatialGram pole coordinate).det|)) :=
  stereographicSurfaceCoordinateMeasure_eq_metric_withDensity pole

end
end P0EFTJanusStereographicConeMetricVolume4D
end JanusFormal
