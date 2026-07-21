import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusInfiniteTemporalH1ZeroModeCohomology4D

/-!
# Smooth finite Fourier core of the temporal H¹ graph

Finite temporal Fourier polynomials form a dense core of the spatially
constant weighted graph.  On that core the synthesized derivative is the
actual time-flow derivative and the temporal component of the exact gauge
potential `dc`.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusInfiniteTemporalH1SmoothCoreClosure4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory
open P0EFTJanusCircleUnboundedDiracDomain
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusShiftedSobolevMappingTorusFiniteTemporalFourierBridge4D
open P0EFTJanusMappingTorusFiniteTemporalFourierGaugeGhostZeroMode4D
open P0EFTJanusMappingTorusFiniteTemporalFourierGaugeGhostCohomology4D
open P0EFTJanusMappingTorusInfiniteTemporalFourierSobolevBridge4D
open P0EFTJanusMappingTorusL2PTFunctionalSpace4D
open P0EFTJanusMappingTorusTimeTranslationMetricMatterGaugeNoether4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D

variable (period : Real) [hPeriodPos : Fact (0 < period)]

private abbrev sphereData := reflectedSphereData period hPeriodPos.out.ne'
private abbrev EffectiveQuotient := MappingTorus (sphereData period)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period) :=
  reflectedSphereQuotientChartedSpace period hPeriodPos.out.ne'

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period) :=
  reflectedSphereQuotient_isManifold period hPeriodPos.out.ne'

local instance normalizedCanonicalLorentzVolumeMeasure_isFinite :
    IsFiniteMeasure (normalizedCanonicalLorentzVolumeMeasure period) := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriodPos.out.ne') :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriodPos.out.ne'
  unfold normalizedCanonicalLorentzVolumeMeasure
  exact Measure.smul_finite _
    (ENNReal.inv_ne_top.mpr (canonicalTemporalMass_ne_zero period))

/-- Weighted inclusion of finite Fourier coefficients into the completed
temporal H¹ coefficient graph. -/
def finiteTemporalH1SmoothCore :
    FiniteTemporalFourierCoefficients →ₗ[Complex]
      TemporalH1CoefficientHilbert period :=
  Finsupp.linearCombination Complex
    (fun mode : Int => lp.single 2 mode
      (Real.sqrt (temporalH1Weight period mode) : Complex))

@[simp]
theorem finiteTemporalH1SmoothCore_apply
    (coefficients : FiniteTemporalFourierCoefficients) (mode : Int) :
    finiteTemporalH1SmoothCore period coefficients mode =
      coefficients mode *
        (Real.sqrt (temporalH1Weight period mode) : Complex) := by
  classical
  rw [finiteTemporalH1SmoothCore, Finsupp.linearCombination_apply]
  simp only [Finsupp.sum, Finset.sum_apply, Pi.smul_apply,
    lp.coeFn_sum, lp.coeFn_smul, lp.single_apply, smul_eq_mul,
    Pi.single_apply]
  rw [Finset.sum_eq_single mode]
  · simp
  · intro other _ hOther
    simp [lp.single_apply, Ne.symm hOther]
  · intro hMode
    have hCoeff : coefficients mode = 0 := by
      simpa [Finsupp.mem_support_iff] using hMode
    simp [hCoeff]

theorem finiteTemporalH1SmoothCore_single
    (mode : Int) (value : Complex) :
    finiteTemporalH1SmoothCore period
        (Finsupp.single mode
          (value *
            (Real.sqrt (temporalH1Weight period mode) : Complex)⁻¹)) =
      lp.single 2 mode value := by
  ext current
  by_cases hCurrent : current = mode
  · subst current
    rw [finiteTemporalH1SmoothCore_apply]
    have hSqrt :
        (Real.sqrt (temporalH1Weight period mode) : Complex) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr
        (Real.sqrt_ne_zero'.2 (temporalH1Weight_pos period mode))
    change
      (Finsupp.single mode
        (value * (Real.sqrt (temporalH1Weight period mode) : Complex)⁻¹)) mode *
          (Real.sqrt (temporalH1Weight period mode) : Complex) =
        (lp.single 2 mode value : CircleHilbert) mode
    rw [Finsupp.single_eq_same, lp.single_apply, Pi.single_eq_same]
    simp [hSqrt]
  · rw [finiteTemporalH1SmoothCore_apply]
    change
      (Finsupp.single mode
        (value * (Real.sqrt (temporalH1Weight period mode) : Complex)⁻¹)) current *
          (Real.sqrt (temporalH1Weight period current) : Complex) =
        (lp.single 2 mode value : CircleHilbert) current
    rw [Finsupp.single_eq_of_ne hCurrent]
    simp [lp.single_apply, hCurrent]

/-- Finite temporal Fourier polynomials are dense in the completed weighted
H¹ coefficient space. -/
theorem finiteTemporalH1SmoothCore_denseRange :
    DenseRange (finiteTemporalH1SmoothCore period) := by
  rw [denseRange_iff_closure_range]
  apply Set.eq_univ_of_forall
  intro state
  let closedRange :=
    (LinearMap.range (finiteTemporalH1SmoothCore period)).topologicalClosure
  change state ∈ closedRange
  apply (Submodule.isClosed_topologicalClosure _).mem_of_tendsto
    (lp.hasSum_single ENNReal.ofNat_ne_top state)
  filter_upwards with modes
  apply Submodule.sum_mem
  intro mode _
  apply Submodule.le_topologicalClosure
  exact ⟨Finsupp.single mode
      (state mode *
        (Real.sqrt (temporalH1Weight period mode) : Complex)⁻¹),
    finiteTemporalH1SmoothCore_single period mode (state mode)⟩

/-- The completed temporal graph, retaining both the field and its synthesized
derivative in quotient `L²`. -/
def temporalH1GraphLinearMap :
    TemporalH1CoefficientHilbert period →L[Complex]
      CanonicalTemporalQuotientL2 period × CanonicalTemporalQuotientL2 period :=
  (temporalH1FieldL2 period).prod (temporalH1DerivativeL2 period)

/-- The finite smooth graph jets are dense in the range of the completed
field/derivative graph. -/
theorem finiteTemporalH1SmoothGraph_dense :
    Set.range (temporalH1GraphLinearMap period) ⊆
      closure (Set.range (fun coefficients : FiniteTemporalFourierCoefficients =>
        temporalH1GraphLinearMap period
          (finiteTemporalH1SmoothCore period coefficients))) := by
  have hDense : Dense (Set.range (finiteTemporalH1SmoothCore period)) :=
    finiteTemporalH1SmoothCore_denseRange period
  have hRange :
      temporalH1GraphLinearMap period ''
          Set.range (finiteTemporalH1SmoothCore period) =
        Set.range (fun coefficients : FiniteTemporalFourierCoefficients =>
          temporalH1GraphLinearMap period
            (finiteTemporalH1SmoothCore period coefficients)) := by
    ext value
    constructor
    · rintro ⟨state, ⟨coefficients, rfl⟩, rfl⟩
      exact ⟨coefficients, rfl⟩
    · rintro ⟨coefficients, rfl⟩
      exact ⟨finiteTemporalH1SmoothCore period coefficients,
        ⟨coefficients, rfl⟩, rfl⟩
  rw [← hRange]
  exact (temporalH1GraphLinearMap period).continuous
    |>.range_subset_closure_image_dense hDense

theorem temporalH1FieldCoefficientOperator_smoothCore
    (coefficients : FiniteTemporalFourierCoefficients) :
    temporalH1FieldCoefficientOperator period
        (finiteTemporalH1SmoothCore period coefficients) =
      finiteTemporalCoefficientsToCircleHilbert coefficients := by
  ext mode
  rw [temporalH1FieldCoefficientOperator_apply,
    finiteTemporalH1SmoothCore_apply,
    finiteTemporalCoefficientsToCircleHilbert_apply]
  have hSqrt :
      (Real.sqrt (temporalH1Weight period mode) : Complex) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr
      (Real.sqrt_ne_zero'.2 (temporalH1Weight_pos period mode))
  change (Real.sqrt (temporalH1Weight period mode) : Complex)⁻¹ *
      (coefficients mode *
        (Real.sqrt (temporalH1Weight period mode) : Complex)) =
    coefficients mode
  field_simp

theorem temporalH1DerivativeCoefficientOperator_smoothCore
    (coefficients : FiniteTemporalFourierCoefficients) :
    temporalH1DerivativeCoefficientOperator period
        (finiteTemporalH1SmoothCore period coefficients) =
      finiteTemporalCoefficientsToCircleHilbert
        (temporalFourierDerivativeCoefficients period coefficients) := by
  ext mode
  rw [temporalH1DerivativeCoefficientOperator_apply,
    temporalH1FieldCoefficientOperator_smoothCore,
    finiteTemporalCoefficientsToCircleHilbert_apply,
    finiteTemporalCoefficientsToCircleHilbert_apply,
    temporalFourierDerivativeCoefficients_apply]
  ring

theorem temporalH1FieldL2_smoothCore_eq_smoothFieldToL2
    (coefficients : FiniteTemporalFourierCoefficients) :
    temporalH1FieldL2 period
        (finiteTemporalH1SmoothCore period coefficients) =
      smoothFieldToL2 period hPeriodPos.out.ne' Complex
        (normalizedCanonicalLorentzVolumeMeasure period)
        (finiteTemporalFourierFieldLinearMap period coefficients) := by
  change mappingTorusTemporalL2Synthesis period
      (temporalH1FieldCoefficientOperator period
        (finiteTemporalH1SmoothCore period coefficients)) = _
  rw [temporalH1FieldCoefficientOperator_smoothCore]
  exact mappingTorusTemporalL2Synthesis_finite_eq_smoothFieldToL2
    period coefficients

/-- On the finite core, the synthesized derivative is the `L²` realization of
the genuine smooth Fourier derivative field. -/
theorem temporalH1DerivativeL2_smoothCore_eq_smoothDerivativeL2
    (coefficients : FiniteTemporalFourierCoefficients) :
    temporalH1DerivativeL2 period
        (finiteTemporalH1SmoothCore period coefficients) =
      smoothFieldToL2 period hPeriodPos.out.ne' Complex
        (normalizedCanonicalLorentzVolumeMeasure period)
        (finiteTemporalFourierFieldLinearMap period
          (temporalFourierDerivativeCoefficients period coefficients)) := by
  change mappingTorusTemporalL2Synthesis period
      (temporalH1DerivativeCoefficientOperator period
        (finiteTemporalH1SmoothCore period coefficients)) = _
  rw [temporalH1DerivativeCoefficientOperator_smoothCore]
  exact mappingTorusTemporalL2Synthesis_finite_eq_smoothFieldToL2
    period (temporalFourierDerivativeCoefficients period coefficients)

/-- Pointwise identification of that smooth derivative with the true
manifold derivative along time translation. -/
theorem smoothCoreDerivative_eq_mvfderiv_timeTranslation
    (coefficients : FiniteTemporalFourierCoefficients)
    (point : EffectiveQuotient period) :
    finiteTemporalFourierFieldLinearMap period
        (temporalFourierDerivativeCoefficients period coefficients) point =
      mfderiv coverModelWithCorners 𝓘(Real, Complex)
        (finiteTemporalFourierFieldLinearMap period coefficients).toFun point
        (effectiveTimeTranslationVelocity period hPeriodPos.out.ne' point) :=
  (finiteTemporalFourierField_mvfderiv_timeTranslationVelocity
    period coefficients point).symm

/-- The same derivative is the temporal component of the actual exact gauge
potential `dc`, in both real gauge coordinates. -/
theorem smoothCoreExactGauge_timeTranslationVelocity
    (coefficients : FiniteTemporalFourierCoefficients)
    (component : Fin 2) (point : EffectiveQuotient period) :
    (finiteTemporalFourierExactGaugeLinearMap period coefficients).toFun
        component point
        (effectiveTimeTranslationVelocity period hPeriodPos.out.ne' point) =
      (complexGaugeLieAlgebraEquiv
        (finiteTemporalFourierFieldLinearMap period
          (temporalFourierDerivativeCoefficients period coefficients) point))
        component :=
  finiteTemporalFourierExactGauge_timeTranslationVelocity
    period coefficients component point

end
end P0EFTJanusMappingTorusInfiniteTemporalH1SmoothCoreClosure4D
end JanusFormal
