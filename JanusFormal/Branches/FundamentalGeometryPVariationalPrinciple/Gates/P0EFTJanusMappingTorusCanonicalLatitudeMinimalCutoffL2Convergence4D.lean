import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLatitudeGlobalThroatNull4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarMinimalCollarCutoffDensity4D

/-!
# Physical bulk `L²` convergence of the global shrinking cutoffs

The global cutoffs satisfy `0 ≤ χₙ ≤ 1` and converge pointwise to one away from
the global throat.  The throat has zero physical Lorentz volume by equatorial
coarea.  Hence

`|(χₙ - 1) φ|² ≤ |φ|²`

and dominated convergence proves convergence to zero of the squared `L²` error.
The corresponding smooth cutoff operators therefore converge strongly to the
identity in physical bulk `L²`.

Combined with unconditional smooth `L²` density, this constructs the concrete
minimal-collar-cutoff package and proves density of the zero-Cauchy minimal core.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusCanonicalLatitudeMinimalCutoffL2Convergence4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff ENNReal
open MeasureTheory Set Topology Filter
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalBulkL2H1Bridge4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarSmoothApproximation4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarFirstSheetGreenCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarMinimalCollarCutoffDensity4D
open P0EFTJanusMappingTorusCanonicalLatitudeMinimalDeckInvariantCutoff4D
open P0EFTJanusMappingTorusCanonicalLatitudeGlobalThroatNull4D

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

local instance canonicalLorentzVolumeFinite :
    IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-- Pointwise squared error density. -/
def canonicalLatitudeMinimalCutoffErrorDensity
    (index : Nat)
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) : Real :=
  ((canonicalLatitudeMinimalQuotientCutoff period hPeriod index point - 1) *
    field point) ^ 2

/-- Continuity of every error density. -/
theorem canonicalLatitudeMinimalCutoffErrorDensity_continuous
    (index : Nat)
    (field : SmoothQuotientField period hPeriod Real) :
    Continuous
      (canonicalLatitudeMinimalCutoffErrorDensity
        period hPeriod index field) := by
  unfold canonicalLatitudeMinimalCutoffErrorDensity
  exact ((((canonicalLatitudeMinimalQuotientCutoff period hPeriod index)
    |>.contMDiff_toFun.continuous.sub continuous_const).mul
      field.contMDiff_toFun.continuous).pow 2)

/-- Error density is nonnegative. -/
theorem canonicalLatitudeMinimalCutoffErrorDensity_nonnegative
    (index : Nat)
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    0 ≤ canonicalLatitudeMinimalCutoffErrorDensity
      period hPeriod index field point :=
  sq_nonneg _

/-- The squared error is dominated by the original squared field. -/
theorem canonicalLatitudeMinimalCutoffErrorDensity_le
    (index : Nat)
    (field : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    canonicalLatitudeMinimalCutoffErrorDensity
        period hPeriod index field point ≤
      field point ^ 2 := by
  let cutoff := canonicalLatitudeMinimalQuotientCutoff
    period hPeriod index point
  have hCutoffNonnegative : 0 ≤ cutoff :=
    canonicalLatitudeMinimalQuotientCutoff_nonnegative
      period hPeriod index point
  have hCutoffLeOne : cutoff ≤ 1 :=
    canonicalLatitudeMinimalQuotientCutoff_le_one
      period hPeriod index point
  have hCoefficient : (cutoff - 1) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg cutoff, sq_nonneg (cutoff - 1)]
  unfold canonicalLatitudeMinimalCutoffErrorDensity
  change ((cutoff - 1) * field point) ^ 2 ≤ field point ^ 2
  rw [mul_pow]
  exact mul_le_mul_of_nonneg_right hCoefficient (sq_nonneg _)

/-- The dominating squared field is integrable. -/
theorem smoothField_sq_integrable
    (field : SmoothQuotientField period hPeriod Real) :
    Integrable (fun point => field point ^ 2)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  (smoothQuotientField_memLp period hPeriod Real
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field).integrable_sq

/-- Almost-everywhere pointwise convergence of the error density to zero. -/
theorem ae_canonicalLatitudeMinimalCutoffErrorDensity_tendsto_zero
    (field : SmoothQuotientField period hPeriod Real) :
    ∀ᵐ point ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod,
      Tendsto
        (fun index : Nat =>
          canonicalLatitudeMinimalCutoffErrorDensity
            period hPeriod index field point)
        atTop (𝓝 0) := by
  filter_upwards
    [ae_canonicalLatitudeMinimalQuotientCutoff_tendsto_one period hPeriod]
    with point hCutoff
  have hDifference : Tendsto
      (fun index : Nat =>
        canonicalLatitudeMinimalQuotientCutoff period hPeriod index point - 1)
      atTop (𝓝 0) := by
    simpa using hCutoff.sub_const 1
  have hProduct : Tendsto
      (fun index : Nat =>
        (canonicalLatitudeMinimalQuotientCutoff period hPeriod index point - 1) *
          field point)
      atTop (𝓝 0) := by
    simpa using hDifference.mul_const (field point)
  simpa [canonicalLatitudeMinimalCutoffErrorDensity] using hProduct.pow 2

/-- Dominated convergence for the squared physical error. -/
theorem integral_canonicalLatitudeMinimalCutoffErrorDensity_tendsto_zero
    (field : SmoothQuotientField period hPeriod Real) :
    Tendsto
      (fun index : Nat =>
        ∫ point,
          canonicalLatitudeMinimalCutoffErrorDensity
            period hPeriod index field point
          ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      atTop (𝓝 0) := by
  have hTarget := tendsto_integral_of_dominated_convergence
    (fun point : EffectiveQuotient period hPeriod => field point ^ 2)
    (fun index =>
      (canonicalLatitudeMinimalCutoffErrorDensity_continuous
        period hPeriod index field).aestronglyMeasurable)
    (smoothField_sq_integrable period hPeriod field)
    (fun index => Filter.Eventually.of_forall fun point => by
      rw [Real.norm_eq_abs,
        abs_of_nonneg
          (canonicalLatitudeMinimalCutoffErrorDensity_nonnegative
            period hPeriod index field point)]
      exact canonicalLatitudeMinimalCutoffErrorDensity_le
        period hPeriod index field point)
    (ae_canonicalLatitudeMinimalCutoffErrorDensity_tendsto_zero
      period hPeriod field)
  simpa using hTarget

/-- Physical `L²` error vector. -/
def canonicalLatitudeMinimalCutoffL2Error
    (index : Nat)
    (field : SmoothQuotientField period hPeriod Real) :
    CanonicalPhysicalBulkL2 period hPeriod :=
  smoothToCanonicalPhysicalBulkL2 period hPeriod
      (canonicalLatitudeMinimalCutoffLinearMap period hPeriod index field) -
    smoothToCanonicalPhysicalBulkL2 period hPeriod field

/-- Squared `L²` error equals the integral of the pointwise squared error. -/
theorem norm_sq_canonicalLatitudeMinimalCutoffL2Error
    (index : Nat)
    (field : SmoothQuotientField period hPeriod Real) :
    ‖canonicalLatitudeMinimalCutoffL2Error
        period hPeriod index field‖ ^ 2 =
      ∫ point,
        canonicalLatitudeMinimalCutoffErrorDensity
          period hPeriod index field point
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  rw [← real_inner_self_eq_norm_sq, MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  filter_upwards
    [Lp.coeFn_sub
      (smoothToCanonicalPhysicalBulkL2 period hPeriod
        (canonicalLatitudeMinimalCutoffLinearMap period hPeriod index field))
      (smoothToCanonicalPhysicalBulkL2 period hPeriod field),
     smoothFieldToL2_ae period hPeriod Real
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)
      (canonicalLatitudeMinimalCutoffLinearMap period hPeriod index field),
     smoothFieldToL2_ae period hPeriod Real
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) field]
    with point hSub hCutoff hField
  rw [hSub, hCutoff, hField]
  simp only [canonicalLatitudeMinimalCutoffLinearMap_apply]
  unfold canonicalLatitudeMinimalCutoffErrorDensity
  rw [real_inner_self_eq_norm_sq, Real.norm_eq_abs, sq_abs]

/-- Squared `L²` errors converge to zero. -/
theorem norm_sq_canonicalLatitudeMinimalCutoffL2Error_tendsto_zero
    (field : SmoothQuotientField period hPeriod Real) :
    Tendsto
      (fun index : Nat =>
        ‖canonicalLatitudeMinimalCutoffL2Error
          period hPeriod index field‖ ^ 2)
      atTop (𝓝 0) := by
  simpa only [norm_sq_canonicalLatitudeMinimalCutoffL2Error] using
    integral_canonicalLatitudeMinimalCutoffErrorDensity_tendsto_zero
      period hPeriod field

/-- `L²` error norms converge to zero. -/
theorem norm_canonicalLatitudeMinimalCutoffL2Error_tendsto_zero
    (field : SmoothQuotientField period hPeriod Real) :
    Tendsto
      (fun index : Nat =>
        ‖canonicalLatitudeMinimalCutoffL2Error
          period hPeriod index field‖)
      atTop (𝓝 0) := by
  have hSquare :=
    norm_sq_canonicalLatitudeMinimalCutoffL2Error_tendsto_zero
      period hPeriod field
  have hSqrt := Real.continuousAt_sqrt.tendsto.comp hSquare
  simpa [Real.sqrt_sq (norm_nonneg _)] using hSqrt

/-- Strong convergence of the globally cut smooth fields in physical bulk
`L²`. -/
theorem smoothToCanonicalPhysicalBulkL2_minimalCutoff_tendsto
    (field : SmoothQuotientField period hPeriod Real) :
    Tendsto
      (fun index : Nat =>
        smoothToCanonicalPhysicalBulkL2 period hPeriod
          (canonicalLatitudeMinimalCutoffLinearMap
            period hPeriod index field))
      atTop
      (𝓝 (smoothToCanonicalPhysicalBulkL2 period hPeriod field)) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hNormEventually : ∀ᶠ index : Nat in atTop,
      ‖canonicalLatitudeMinimalCutoffL2Error
        period hPeriod index field‖ < ε :=
    (tendsto_order.1
      (norm_canonicalLatitudeMinimalCutoffL2Error_tendsto_zero
        period hPeriod field)).2 ε hε
  filter_upwards [hNormEventually] with index hIndex
  simpa [canonicalLatitudeMinimalCutoffL2Error, dist_eq_norm] using hIndex

/-- Concrete physical minimal-collar-cutoff package. -/
def canonicalPhysicalScalarMinimalCollarCutoffData
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared) :
    CanonicalPhysicalScalarMinimalCollarCutoffData
      period hPeriod green where
  smoothing := canonicalPhysicalScalarContinuousSmoothApproximationData
    period hPeriod
  cutoff := canonicalLatitudeMinimalCutoffLinearMap period hPeriod
  boundary_zero := by
    intro index field
    change smoothCanonicalPhysicalScalarFirstSheetCauchyTrace period hPeriod
      (canonicalLatitudeMinimalCutoffLinearMap
        period hPeriod index field) = 0
    exact smoothFirstSheetCauchyTrace_minimalCutoff_eq_zero
      period hPeriod index field
  tendsto_l2 := smoothToCanonicalPhysicalBulkL2_minimalCutoff_tendsto
    period hPeriod

/-- The physical zero-Cauchy minimal core is dense, with no remaining cutoff or
smooth-density hypothesis. -/
theorem canonicalPhysicalScalarMinimalCoreDense
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared) :
    green.MinimalCoreDense period hPeriod :=
  (canonicalPhysicalScalarMinimalCollarCutoffData
    period hPeriod green).minimalCoreDense green

/-- The completed physical maximal graph is single-valued. -/
theorem canonicalPhysicalScalarGraphInclusion_injective
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared) :
    Function.Injective
      (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreGraphInclusion
        green.core) :=
  (canonicalPhysicalScalarMinimalCollarCutoffData
    period hPeriod green).graphInclusion_injective green

/-- Complete global-cutoff convergence certificate. -/
theorem canonicalLatitudeMinimalCutoffL2Convergence_certificate
    (green : CanonicalPhysicalScalarFirstSheetGreenCoreData
      period hPeriod massSquared) :
    (∀ field : SmoothQuotientField period hPeriod Real,
      Tendsto
        (fun index : Nat =>
          smoothToCanonicalPhysicalBulkL2 period hPeriod
            (canonicalLatitudeMinimalCutoffLinearMap
              period hPeriod index field))
        atTop
        (𝓝 (smoothToCanonicalPhysicalBulkL2 period hPeriod field))) ∧
      green.MinimalCoreDense period hPeriod ∧
      Function.Injective
        (P0EFTJanusMappingTorusScalarHilbertGreenCoreCompletion4D.canonicalScalarGreenCoreGraphInclusion
          green.core) :=
  ⟨smoothToCanonicalPhysicalBulkL2_minimalCutoff_tendsto
      period hPeriod,
    canonicalPhysicalScalarMinimalCoreDense period hPeriod green,
    canonicalPhysicalScalarGraphInclusion_injective period hPeriod green⟩

end
end P0EFTJanusMappingTorusCanonicalLatitudeMinimalCutoffL2Convergence4D
end JanusFormal
