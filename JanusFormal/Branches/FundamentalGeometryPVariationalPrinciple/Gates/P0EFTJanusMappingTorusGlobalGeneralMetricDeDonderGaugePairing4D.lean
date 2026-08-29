import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalGeneralMetricDeDonderLinear4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusEffectiveD8SmoothTensorVectorContraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D

/-!
# Integrated global de Donder gauge pairing

This gate raises the already linear global de Donder one-form with the supplied
smooth Lorentz metric, contracts two such fields smoothly, and integrates the
result against the existing finite general-metric volume.  The result is a
genuine symmetric bilinear form on smooth metric perturbations and the exact
polarization of its unit-weight quadratic functional.

No norm on the raw smooth-section space, formal adjoint, Green identity,
Candidate-A chart insertion, positivity or Fredholm property is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalGeneralMetricDeDonderGaugePairing4D

set_option autoImplicit false
noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGlobalGeneralMetricSymmetricTensorDivergence4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusEffectiveD8BackgroundCategory4D
open P0EFTJanusEffectiveD8SmoothInverseMusical4D
open P0EFTJanusEffectiveD8SmoothTensorVectorContraction4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- Smooth inverse-metric pairing of two global de Donder one-forms. -/
def globalGeneralMetricDeDonderPairingField
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    SmoothQuotientField period hPeriod Real :=
  effectiveD8SmoothLorentzMetricVectorContraction
    (generalMetricDivergenceBackground period hPeriod) metric
    (effectiveD8SmoothInverseMusical
      (generalMetricDivergenceBackground period hPeriod) metric
      (globalGeneralMetricDeDonderLinearMap period hPeriod metric first))
    (effectiveD8SmoothInverseMusical
      (generalMetricDivergenceBackground period hPeriod) metric
      (globalGeneralMetricDeDonderLinearMap period hPeriod metric second))

@[simp]
theorem globalGeneralMetricDeDonderPairingField_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalGeneralMetricDeDonderPairingField period hPeriod metric first second
        point =
      inverseMetricContraction period hPeriod metric point
        (globalGeneralMetricDeDonder period hPeriod metric first point)
        (globalGeneralMetricDeDonder period hPeriod metric second point) := by
  unfold globalGeneralMetricDeDonderPairingField
  rw [effectiveD8SmoothLorentzMetricVectorContraction_apply,
    effectiveD8SmoothInverseMusical_apply,
    effectiveD8SmoothInverseMusical_apply]
  unfold inverseMetricContraction
  rw [← metric.musical_eq_tensor point]
  change
    metric.musical point
        (inverseMetricSharp period hPeriod metric point
          (globalGeneralMetricDeDonder period hPeriod metric first point))
        (inverseMetricSharp period hPeriod metric point
          (globalGeneralMetricDeDonder period hPeriod metric second point)) =
      _
  rw [metric_flat_inverseMetricSharp]

private theorem inverseMetricContraction_add_left
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (first second third :
      TangentSpace coverModelWithCorners point →L[Real] Real) :
    inverseMetricContraction period hPeriod metric point
        (first + second) third =
      inverseMetricContraction period hPeriod metric point first third +
        inverseMetricContraction period hPeriod metric point second third := by
  simp [inverseMetricContraction]

private theorem inverseMetricContraction_smul_left
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (scalar : Real)
    (first second :
      TangentSpace coverModelWithCorners point →L[Real] Real) :
    inverseMetricContraction period hPeriod metric point
        (scalar • first) second =
      scalar *
        inverseMetricContraction period hPeriod metric point first second := by
  simp [inverseMetricContraction]

private theorem inverseMetricContraction_add_right
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (first second third :
      TangentSpace coverModelWithCorners point →L[Real] Real) :
    inverseMetricContraction period hPeriod metric point
        first (second + third) =
      inverseMetricContraction period hPeriod metric point first second +
        inverseMetricContraction period hPeriod metric point first third := by
  simp [inverseMetricContraction, inverseMetricSharp]

private theorem inverseMetricContraction_smul_right
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (scalar : Real)
    (first second :
      TangentSpace coverModelWithCorners point →L[Real] Real) :
    inverseMetricContraction period hPeriod metric point
        first (scalar • second) =
      scalar *
        inverseMetricContraction period hPeriod metric point first second := by
  simp [inverseMetricContraction, inverseMetricSharp]

private theorem inverseMetricContraction_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (point : EffectiveQuotient period hPeriod)
    (first second :
      TangentSpace coverModelWithCorners point →L[Real] Real) :
    inverseMetricContraction period hPeriod metric point first second =
      inverseMetricContraction period hPeriod metric point second first := by
  unfold inverseMetricContraction
  calc
    first (inverseMetricSharp period hPeriod metric point second) =
        metric.tensor.tensor point
          (inverseMetricSharp period hPeriod metric point first)
          (inverseMetricSharp period hPeriod metric point second) := by
      rw [← metric.musical_eq_tensor point]
      exact congrArg
        (fun covector =>
          covector (inverseMetricSharp period hPeriod metric point second))
        (metric_flat_inverseMetricSharp period hPeriod metric point first)
        |>.symm
    _ = metric.tensor.tensor point
          (inverseMetricSharp period hPeriod metric point second)
          (inverseMetricSharp period hPeriod metric point first) :=
      metric.tensor.symmetric point _ _
    _ = second (inverseMetricSharp period hPeriod metric point first) := by
      rw [← metric.musical_eq_tensor point]
      exact congrArg
        (fun covector =>
          covector (inverseMetricSharp period hPeriod metric point first))
        (metric_flat_inverseMetricSharp period hPeriod metric point second)

theorem globalGeneralMetricDeDonderPairingField_add_left
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second third :
      SmoothSymmetricCovariantTwoTensor period hPeriod) :
    globalGeneralMetricDeDonderPairingField period hPeriod metric
        (first + second) third =
      globalGeneralMetricDeDonderPairingField period hPeriod metric first third +
        globalGeneralMetricDeDonderPairingField period hPeriod metric second
          third := by
  apply SmoothQuotientField.ext
  intro point
  change
    globalGeneralMetricDeDonderPairingField period hPeriod metric
        (first + second) third point =
      globalGeneralMetricDeDonderPairingField period hPeriod metric first third
          point +
        globalGeneralMetricDeDonderPairingField period hPeriod metric second
          third point
  rw [globalGeneralMetricDeDonderPairingField_apply,
    globalGeneralMetricDeDonderPairingField_apply,
    globalGeneralMetricDeDonderPairingField_apply,
    globalGeneralMetricDeDonder_add]
  exact inverseMetricContraction_add_left period hPeriod metric point _ _ _

theorem globalGeneralMetricDeDonderPairingField_smul_left
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    globalGeneralMetricDeDonderPairingField period hPeriod metric
        (scalar • first) second =
      scalar •
        globalGeneralMetricDeDonderPairingField period hPeriod metric first
          second := by
  apply SmoothQuotientField.ext
  intro point
  change
    globalGeneralMetricDeDonderPairingField period hPeriod metric
        (scalar • first) second point =
      scalar *
        globalGeneralMetricDeDonderPairingField period hPeriod metric first
          second point
  rw [globalGeneralMetricDeDonderPairingField_apply,
    globalGeneralMetricDeDonderPairingField_apply,
    globalGeneralMetricDeDonder_smul]
  exact inverseMetricContraction_smul_left period hPeriod metric point scalar
    _ _

theorem globalGeneralMetricDeDonderPairingField_add_right
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second third :
      SmoothSymmetricCovariantTwoTensor period hPeriod) :
    globalGeneralMetricDeDonderPairingField period hPeriod metric first
        (second + third) =
      globalGeneralMetricDeDonderPairingField period hPeriod metric first
          second +
        globalGeneralMetricDeDonderPairingField period hPeriod metric first
          third := by
  apply SmoothQuotientField.ext
  intro point
  change
    globalGeneralMetricDeDonderPairingField period hPeriod metric first
        (second + third) point =
      globalGeneralMetricDeDonderPairingField period hPeriod metric first second
          point +
        globalGeneralMetricDeDonderPairingField period hPeriod metric first third
          point
  rw [globalGeneralMetricDeDonderPairingField_apply,
    globalGeneralMetricDeDonderPairingField_apply,
    globalGeneralMetricDeDonderPairingField_apply,
    globalGeneralMetricDeDonder_add]
  exact inverseMetricContraction_add_right period hPeriod metric point _ _ _

theorem globalGeneralMetricDeDonderPairingField_smul_right
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    globalGeneralMetricDeDonderPairingField period hPeriod metric first
        (scalar • second) =
      scalar •
        globalGeneralMetricDeDonderPairingField period hPeriod metric first
          second := by
  apply SmoothQuotientField.ext
  intro point
  change
    globalGeneralMetricDeDonderPairingField period hPeriod metric first
        (scalar • second) point =
      scalar *
        globalGeneralMetricDeDonderPairingField period hPeriod metric first
          second point
  rw [globalGeneralMetricDeDonderPairingField_apply,
    globalGeneralMetricDeDonderPairingField_apply,
    globalGeneralMetricDeDonder_smul]
  exact inverseMetricContraction_smul_right period hPeriod metric point scalar
    _ _

theorem globalGeneralMetricDeDonderPairingField_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    globalGeneralMetricDeDonderPairingField period hPeriod metric first second =
      globalGeneralMetricDeDonderPairingField period hPeriod metric second
        first := by
  apply SmoothQuotientField.ext
  intro point
  rw [globalGeneralMetricDeDonderPairingField_apply,
    globalGeneralMetricDeDonderPairingField_apply]
  exact inverseMetricContraction_symmetric period hPeriod metric point _ _

theorem globalGeneralMetricDeDonderPairingField_integrable
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    Integrable
      (globalGeneralMetricDeDonderPairingField
        period hPeriod metric first second)
      (generalLorentzVolumeMeasure period hPeriod metric) := by
  letI := generalLorentzVolumeMeasure_isFinite period hPeriod metric
  exact
    (globalGeneralMetricDeDonderPairingField
      period hPeriod metric first second)
      |>.contMDiff_toFun.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)

/-- Integrated inverse-metric pairing of two de Donder one-forms. -/
def globalGeneralMetricDeDonderGaugePairingValue
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) : Real :=
  ∫ point,
    globalGeneralMetricDeDonderPairingField
      period hPeriod metric first second point
    ∂generalLorentzVolumeMeasure period hPeriod metric

/-- The integrated de Donder gauge block as a genuine symmetric bilinear form
on smooth metric perturbations. -/
def globalGeneralMetricDeDonderGaugeBilinearForm
    (metric : SmoothGeneralLorentzMetric period hPeriod) :
    LinearMap.BilinForm Real
      (SmoothSymmetricCovariantTwoTensor period hPeriod) :=
  LinearMap.mk₂ Real
    (globalGeneralMetricDeDonderGaugePairingValue period hPeriod metric)
    (fun first second third => by
      unfold globalGeneralMetricDeDonderGaugePairingValue
      rw [globalGeneralMetricDeDonderPairingField_add_left]
      exact integral_add
        (globalGeneralMetricDeDonderPairingField_integrable
          period hPeriod metric first third)
        (globalGeneralMetricDeDonderPairingField_integrable
          period hPeriod metric second third))
    (fun scalar first second => by
      unfold globalGeneralMetricDeDonderGaugePairingValue
      rw [globalGeneralMetricDeDonderPairingField_smul_left]
      change
        (∫ point, scalar *
          globalGeneralMetricDeDonderPairingField
            period hPeriod metric first second point
          ∂generalLorentzVolumeMeasure period hPeriod metric) =
        scalar *
          ∫ point,
            globalGeneralMetricDeDonderPairingField
              period hPeriod metric first second point
            ∂generalLorentzVolumeMeasure period hPeriod metric
      simp only [integral_const_mul])
    (fun first second third => by
      unfold globalGeneralMetricDeDonderGaugePairingValue
      rw [globalGeneralMetricDeDonderPairingField_add_right]
      exact integral_add
        (globalGeneralMetricDeDonderPairingField_integrable
          period hPeriod metric first second)
        (globalGeneralMetricDeDonderPairingField_integrable
          period hPeriod metric first third))
    (fun scalar first second => by
      unfold globalGeneralMetricDeDonderGaugePairingValue
      rw [globalGeneralMetricDeDonderPairingField_smul_right]
      change
        (∫ point, scalar *
          globalGeneralMetricDeDonderPairingField
            period hPeriod metric first second point
          ∂generalLorentzVolumeMeasure period hPeriod metric) =
        scalar *
          ∫ point,
            globalGeneralMetricDeDonderPairingField
              period hPeriod metric first second point
            ∂generalLorentzVolumeMeasure period hPeriod metric
      simp only [integral_const_mul])

@[simp]
theorem globalGeneralMetricDeDonderGaugeBilinearForm_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    globalGeneralMetricDeDonderGaugeBilinearForm period hPeriod metric
        first second =
      globalGeneralMetricDeDonderGaugePairingValue
        period hPeriod metric first second :=
  rfl

theorem globalGeneralMetricDeDonderGaugeBilinearForm_symmetric
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    globalGeneralMetricDeDonderGaugeBilinearForm period hPeriod metric
        first second =
      globalGeneralMetricDeDonderGaugeBilinearForm period hPeriod metric
        second first := by
  rw [globalGeneralMetricDeDonderGaugeBilinearForm_apply,
    globalGeneralMetricDeDonderGaugeBilinearForm_apply]
  unfold globalGeneralMetricDeDonderGaugePairingValue
  rw [globalGeneralMetricDeDonderPairingField_symmetric]

/-- Unit-weight quadratic gauge functional associated with the de Donder
pairing.  This is not inserted into the Candidate-A action by this gate. -/
def globalGeneralMetricDeDonderGaugeQuadratic
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod) : Real :=
  (1 / 2 : Real) *
    globalGeneralMetricDeDonderGaugeBilinearForm period hPeriod metric
      tensor tensor

theorem globalGeneralMetricDeDonderGaugeQuadratic_polarization
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second : SmoothSymmetricCovariantTwoTensor period hPeriod) :
    globalGeneralMetricDeDonderGaugeQuadratic period hPeriod metric
        (first + second) -
        globalGeneralMetricDeDonderGaugeQuadratic period hPeriod metric first -
      globalGeneralMetricDeDonderGaugeQuadratic period hPeriod metric second =
    globalGeneralMetricDeDonderGaugeBilinearForm period hPeriod metric
      first second := by
  unfold globalGeneralMetricDeDonderGaugeQuadratic
  simp only [map_add, LinearMap.add_apply]
  rw [globalGeneralMetricDeDonderGaugeBilinearForm_symmetric
    period hPeriod metric second first]
  ring

end
end P0EFTJanusMappingTorusGlobalGeneralMetricDeDonderGaugePairing4D
end JanusFormal
