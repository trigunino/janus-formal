import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1UniformEllipticity4D

/-!
# Finite-frame to holonomic-coordinate control for the static scalar bridge

The finite smooth tangent family is smooth as a section of the true tangent
bundle.  The fixed `tangentCoordinate` vectors used by the action are only
model-space vectors; the current API does not provide them as a global smooth
tangent frame, nor does it provide continuous transition coefficients from a
`SmoothD8Frame`.  Compactness alone therefore cannot supply the missing
uniform coefficient estimate.

This gate isolates exactly that geometric datum: a field-independent matrix
of coefficients which decomposes every finite-frame vector in the four
holonomic directions and whose finite-dimensional coordinate map has one
uniform quadratic bound.  No action operator or H¹ norm occurs in the
contract.  The contract is then shown to imply the previously isolated
uniform graph ellipticity, using coefficient coercivity derived automatically
from compactness and positivity.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1FrameControl4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff BigOperators Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGlobalHolonomicScalar4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarVariation4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1UniformEllipticity4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Smooth positive metric magnitudes have one common positive upper bound
for all four components. -/
theorem exists_uniform_magnitude_upper
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    ∃ upper : Real, 0 < upper ∧ ∀ point index,
      data.formData.magnitude point index ≤ upper := by
  have hContinuous : Continuous
      (fun point : EffectiveQuotient period hPeriod =>
        ‖data.formData.magnitude point‖) :=
    data.formData.magnitude.contMDiff_toFun.continuous.norm
  rcases isCompact_univ.bddAbove_image hContinuous.continuousOn with
    ⟨upper, hUpper⟩
  refine ⟨|upper| + 1, by positivity, ?_⟩
  intro point index
  calc
    data.formData.magnitude point index ≤
        |data.formData.magnitude point index| := le_abs_self _
    _ = ‖data.formData.magnitude point index‖ := by
      rw [Real.norm_eq_abs]
    _ ≤ ‖data.formData.magnitude point‖ :=
      norm_le_pi_norm _ index
    _ ≤ upper := hUpper ⟨point, Set.mem_univ point, rfl⟩
    _ ≤ |upper| + 1 := by linarith [le_abs_self upper]

/-- The unweighted holonomic first-jet quadratic expression.  The time term
is retained; it vanishes on every `StaticGlobalScalarTest`. -/
def staticScalarHolonomicJetSquare
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data)
    (point : EffectiveQuotient period hPeriod) : Real :=
  field.toField point ^ 2 +
    ∑ index : Fin 4,
      holonomicCovectorComponent period hPeriod field.toField point index ^ 2

/-- Compactness and positivity make the static Jacobi density uniformly
coercive over the unweighted holonomic first jet. -/
theorem exists_uniform_static_holonomic_coercivity
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    ∃ lower : Real, 0 < lower ∧
      ∀ (field : StaticGlobalScalarTest period hPeriod data) point,
        lower * staticScalarHolonomicJetSquare period hPeriod data field point ≤
          globalHolonomicScalarJacobiDensity period hPeriod
            data.formData.massSquared data.formData.magnitude
            field.toField field.toField point := by
  rcases exists_uniform_volume_lower period hPeriod data with
    ⟨volumeLower, hVolumeLower, hVolumeBound⟩
  rcases exists_uniform_magnitude_upper period hPeriod data with
    ⟨magnitudeUpper, hMagnitudeUpper, hMagnitudeBound⟩
  let massLower := volumeLower * data.formData.massSquared
  let kineticLower := volumeLower / magnitudeUpper
  let lower := min massLower kineticLower
  have hMassLower : 0 < massLower :=
    mul_pos hVolumeLower data.massSquared_pos
  have hKineticLower : 0 < kineticLower :=
    div_pos hVolumeLower hMagnitudeUpper
  have hLower : 0 < lower := lt_min hMassLower hKineticLower
  refine ⟨lower, hLower, ?_⟩
  intro field point
  let volume := diagonalMetricVolumeDensity period hPeriod
    data.formData.magnitude point
  let derivative := fun index : Fin 4 =>
    holonomicCovectorComponent period hPeriod field.toField point index
  have hCoefficient (index : Fin 4) :
      kineticLower ≤ volume * (1 / data.formData.magnitude point index) := by
    have hInverse : 1 / magnitudeUpper ≤
        1 / data.formData.magnitude point index :=
      one_div_le_one_div_of_le (data.magnitude_pos point index)
        (hMagnitudeBound point index)
    dsimp only [kineticLower]
    rw [div_eq_mul_inv]
    exact mul_le_mul (hVolumeBound point)
      (by simpa only [one_div] using hInverse)
      (by simpa only [one_div] using (one_div_pos.mpr hMagnitudeUpper).le)
      (diagonalMetricVolumeDensity_pos period hPeriod data point).le
  have hKinetic :
      lower * ∑ index : Fin 4, derivative index ^ 2 ≤
        volume * ∑ index : Fin 4,
          P0EFTJanusGlobalDiagonalLorentzRoot4D.signature index /
              data.formData.magnitude point index *
            derivative index * derivative index := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro index _
    by_cases hIndex : index = 0
    · subst index
      simp [derivative, field.time_static point]
    · have hLowerCoefficient :
          lower ≤ volume * (1 / data.formData.magnitude point index) :=
        (min_le_right massLower kineticLower).trans (hCoefficient index)
      have hScaled := mul_le_mul_of_nonneg_right hLowerCoefficient
        (sq_nonneg (derivative index))
      simpa [P0EFTJanusGlobalDiagonalLorentzRoot4D.signature, hIndex,
        div_eq_mul_inv, pow_two, mul_assoc] using hScaled
  have hMass :
      lower * field.toField point ^ 2 ≤
        volume * (data.formData.massSquared * field.toField point *
          field.toField point) := by
    have hMassCoefficient :
        massLower ≤ volume * data.formData.massSquared := by
      exact mul_le_mul_of_nonneg_right (hVolumeBound point)
        data.massSquared_pos.le
    have hLowerCoefficient :
        lower ≤ volume * data.formData.massSquared :=
      (min_le_left massLower kineticLower).trans hMassCoefficient
    have hScaled := mul_le_mul_of_nonneg_right hLowerCoefficient
      (sq_nonneg (field.toField point))
    simpa [pow_two, mul_assoc] using hScaled
  unfold staticScalarHolonomicJetSquare
  unfold globalHolonomicScalarJacobiDensity
    globalHolonomicScalarFirstVariationDensity
  dsimp only [volume, derivative] at hKinetic hMass ⊢
  calc
    lower * (field.toField point ^ 2 +
        ∑ index : Fin 4,
          holonomicCovectorComponent period hPeriod field.toField point index ^ 2) =
      lower * field.toField point ^ 2 +
        lower * ∑ index : Fin 4,
          holonomicCovectorComponent period hPeriod field.toField point index ^ 2 :=
      mul_add _ _ _
    _ ≤ diagonalMetricVolumeDensity period hPeriod data.formData.magnitude point *
          (data.formData.massSquared * field.toField point * field.toField point) +
        diagonalMetricVolumeDensity period hPeriod data.formData.magnitude point *
          ∑ index : Fin 4,
            P0EFTJanusGlobalDiagonalLorentzRoot4D.signature index /
                data.formData.magnitude point index *
              holonomicCovectorComponent period hPeriod field.toField point index *
              holonomicCovectorComponent period hPeriod field.toField point index :=
      add_le_add hMass hKinetic
    _ = diagonalMetricVolumeDensity period hPeriod data.formData.magnitude point *
        ((∑ index : Fin 4,
            P0EFTJanusGlobalDiagonalLorentzRoot4D.signature index /
                data.formData.magnitude point index *
              holonomicCovectorComponent period hPeriod field.toField point index *
              holonomicCovectorComponent period hPeriod field.toField point index) +
          data.formData.massSquared * field.toField point * field.toField point) := by
      ring

/-- Minimal geometric transition contract.  `coefficients` expresses the
finite smooth tangent generators in the four fixed holonomic directions;
`coordinate_bound` is a uniform bound for that finite-dimensional change of
coordinates, independent of every scalar field. -/
structure StaticScalarHolonomicFrameControl
    (frame : SmoothD8Frame period hPeriod) where
  coefficients : EffectiveQuotient period hPeriod →
    Fin frame.count → Fin 4 → Real
  covector_decomposition : ∀ point frameIndex
      (covector : TangentSpace coverModelWithCorners point →ₗ[Real] Real),
    covector (frame.vectorAt point frameIndex) =
      ∑ holonomicIndex : Fin 4,
        coefficients point frameIndex holonomicIndex *
          covector (tangentCoordinate holonomicIndex)
  constant : Real
  constant_nonneg : 0 ≤ constant
  coordinate_bound : ∀ point (value : Real) (covector : Fin 4 → Real),
    ‖(value, fun frameIndex =>
      ∑ holonomicIndex : Fin 4,
        coefficients point frameIndex holonomicIndex * covector holonomicIndex)‖ ^ 2 ≤
      constant * (value ^ 2 +
        ∑ holonomicIndex : Fin 4, covector holonomicIndex ^ 2)

theorem frameDerivative_eq_holonomicCoefficientSum
    (frame : SmoothD8Frame period hPeriod)
    (control : StaticScalarHolonomicFrameControl period hPeriod frame)
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod)
    (frameIndex : Fin frame.count) :
    frameDerivative period hPeriod Real frame field point frameIndex =
      ∑ holonomicIndex : Fin 4,
        control.coefficients point frameIndex holonomicIndex *
          holonomicCovectorComponent period hPeriod field point holonomicIndex := by
  rw [frameDerivative_eq_mfderiv]
  change scalarDifferential period hPeriod field point
      (frame.vectorAt point frameIndex) = _
  exact control.covector_decomposition point frameIndex
    (scalarDifferential period hPeriod field point)

theorem smoothFirstJet_sq_le_holonomicJetSquare
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (control : StaticScalarHolonomicFrameControl period hPeriod frame)
    (field : StaticGlobalScalarTest period hPeriod data)
    (point : EffectiveQuotient period hPeriod) :
    ‖smoothFirstJet period hPeriod Real frame field.toField point‖ ^ 2 ≤
      control.constant *
        staticScalarHolonomicJetSquare period hPeriod data field point := by
  have hBound := control.coordinate_bound point (field.toField point)
    (fun holonomicIndex =>
      holonomicCovectorComponent period hPeriod field.toField point holonomicIndex)
  unfold staticScalarHolonomicJetSquare
  rw [show smoothFirstJet period hPeriod Real frame field.toField point =
      (field.toField point, fun frameIndex =>
        ∑ holonomicIndex : Fin 4,
          control.coefficients point frameIndex holonomicIndex *
            holonomicCovectorComponent period hPeriod field.toField point
              holonomicIndex) by
    apply Prod.ext
    · rfl
    · funext frameIndex
      exact frameDerivative_eq_holonomicCoefficientSum period hPeriod frame control
        field.toField point frameIndex]
  exact hBound

/-- The purely geometric coefficient contract implies the pointwise uniform
graph ellipticity required by the H¹ bridge. -/
def StaticScalarHolonomicFrameControl.toUniformGraphEllipticity
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (control : StaticScalarHolonomicFrameControl period hPeriod frame) :
    StaticScalarUniformGraphEllipticity period hPeriod data frame := by
  let coercivity :=
    (exists_uniform_static_holonomic_coercivity period hPeriod data).choose
  have hCoercivity : 0 < coercivity :=
    (exists_uniform_static_holonomic_coercivity period hPeriod data).choose_spec.1
  have hCoercive :=
    (exists_uniform_static_holonomic_coercivity period hPeriod data).choose_spec.2
  let ratio := control.constant / coercivity
  refine
    { constant := Real.sqrt ratio
      constant_nonneg := Real.sqrt_nonneg ratio
      pointwise_bound := ?_ }
  intro field point
  let jetNorm := ‖smoothFirstJet period hPeriod Real frame field.toField point‖
  let jetSquare := staticScalarHolonomicJetSquare period hPeriod data field point
  let density := globalHolonomicScalarJacobiDensity period hPeriod
    data.formData.massSquared data.formData.magnitude
    field.toField field.toField point
  have hJet : jetNorm ^ 2 ≤ control.constant * jetSquare :=
    smoothFirstJet_sq_le_holonomicJetSquare period hPeriod data frame control field point
  have hDensity : coercivity * jetSquare ≤ density :=
    hCoercive field point
  have hJetSquare : jetSquare ≤ density / coercivity :=
    (le_div_iff₀ hCoercivity).2 (by simpa [mul_comm] using hDensity)
  have hScaled : control.constant * jetSquare ≤
      control.constant * (density / coercivity) :=
    mul_le_mul_of_nonneg_left hJetSquare control.constant_nonneg
  have hRatio : 0 ≤ ratio :=
    div_nonneg control.constant_nonneg hCoercivity.le
  have hDensityNonneg : 0 ≤ density :=
    staticScalarJacobiDensity_nonneg period hPeriod data field point
  have hJetDensity : jetNorm ^ 2 ≤ ratio * density := by
    calc
      jetNorm ^ 2 ≤ control.constant * jetSquare := hJet
      _ ≤ control.constant * (density / coercivity) := hScaled
      _ = ratio * density := by
        dsimp only [ratio]
        field_simp
  have hRightNonneg :
      0 ≤ Real.sqrt ratio * Real.sqrt density :=
    mul_nonneg (Real.sqrt_nonneg ratio) (Real.sqrt_nonneg density)
  have hSquared : jetNorm ^ 2 ≤
      (Real.sqrt ratio * Real.sqrt density) ^ 2 := by
    calc
      jetNorm ^ 2 ≤ ratio * density := hJetDensity
      _ = (Real.sqrt ratio * Real.sqrt density) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hRatio, Real.sq_sqrt hDensityNonneg]
  have hResult := (sq_le_sq₀ (norm_nonneg _) hRightNonneg).mp hSquared
  simpa [jetNorm, density, ratio, staticScalarJacobiDensityRoot] using hResult

end

end P0EFTJanusMappingTorusGlobalHolonomicScalarStaticH1FrameControl4D
end JanusFormal
