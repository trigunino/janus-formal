import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D

/-! # Pointwise separation by genuine smooth Maxwell tests -/

namespace JanusFormal
namespace P0EFTJanusProgramPRegularFrameMaxwellSmoothGaugeTestSeparation4D

set_option autoImplicit false

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarEulerCanonicalFullSupport4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPRegularFrameGaugePotentialReconstruction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

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

/-- Euclidean pairing of a smooth eight-component Maxwell residual with a
smooth coefficient test. -/
noncomputable def smoothGaugeResidualPairing
    (residual direction : SmoothQuotientField period hPeriod GaugeFiber)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Real :=
  ∫ point, inner Real (residual point) (direction point) ∂measure

/-- Every smooth Maxwell coefficient residual is detected pointwise by all
smooth coefficient tests under a finite full-support measure. -/
theorem smoothGaugeField_pairing_detects_pointwise_zero
    (residual : SmoothQuotientField period hPeriod GaugeFiber)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] [measure.IsOpenPosMeasure] :
    (∀ direction : SmoothQuotientField period hPeriod GaugeFiber,
        smoothGaugeResidualPairing period hPeriod residual direction measure =
          0) ↔
      ∀ point : EffectiveQuotient period hPeriod, residual point = 0 := by
  constructor
  · intro hPairing
    have hSelf := hPairing residual
    have hSquareIntegral :
        (∫ point, ‖residual point‖ ^ 2 ∂measure) = 0 := by
      simpa only [smoothGaugeResidualPairing,
        real_inner_self_eq_norm_sq] using hSelf
    have hSquareIntegrable :
        Integrable (fun point => ‖residual point‖ ^ 2) measure :=
      (residual.contMDiff_toFun.continuous.norm.pow 2
        ).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hSquareZero :
        (fun point => ‖residual point‖ ^ 2) =ᵐ[measure] 0 :=
      (integral_eq_zero_iff_of_nonneg
        (fun point => sq_nonneg ‖residual point‖) hSquareIntegrable).mp
          hSquareIntegral
    have hResidualZero :
        residual.toFun =ᵐ[measure]
          (fun _ : EffectiveQuotient period hPeriod => (0 : GaugeFiber)) := by
      filter_upwards [hSquareZero] with point hPoint
      exact norm_eq_zero.mp (sq_eq_zero_iff.mp hPoint)
    have hFunctionZero :
        residual.toFun =
          (fun _ : EffectiveQuotient period hPeriod => (0 : GaugeFiber)) :=
      (Continuous.ae_eq_iff_eq measure residual.contMDiff_toFun.continuous
        continuous_const).mp hResidualZero
    exact fun point => congrFun hFunctionZero point
  · intro hPointwise direction
    have hIntegrand :
        (fun point => inner Real (residual point) (direction point)) = 0 := by
      funext point
      rw [hPointwise point]
      simp
    rw [smoothGaugeResidualPairing, hIntegrand]
    simp

/-- A nonzero physical coupling does not weaken smooth test separation. -/
theorem smoothGaugeField_coupled_pairing_detects_pointwise_zero
    (residual : SmoothQuotientField period hPeriod GaugeFiber)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] [measure.IsOpenPosMeasure]
    (coupling : Real) (hCoupling : coupling ≠ 0) :
    (∀ direction : SmoothQuotientField period hPeriod GaugeFiber,
        coupling *
          smoothGaugeResidualPairing period hPeriod residual direction measure =
            0) ↔
      ∀ point : EffectiveQuotient period hPeriod, residual point = 0 := by
  constructor
  · intro hCoupled
    apply (smoothGaugeField_pairing_detects_pointwise_zero period hPeriod
      residual measure).mp
    intro direction
    exact (mul_eq_zero.mp (hCoupled direction)).resolve_left hCoupling
  · intro hPointwise direction
    have hZero :=
      (smoothGaugeField_pairing_detects_pointwise_zero period hPeriod residual
        measure).mpr hPointwise direction
    rw [hZero, mul_zero]

/-- Pairing against a genuine intrinsic smooth gauge-potential variation,
read through the chosen regular frame. -/
noncomputable def regularFrameIntrinsicGaugeResidualPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (residual : SmoothQuotientField period hPeriod GaugeFiber)
    (variation : SmoothAbelianGaugePotential period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Real :=
  smoothGaugeResidualPairing period hPeriod residual
    (gaugePotentialFrameCoefficients period hPeriod metric variation) measure

/-- Genuine intrinsic gauge variations separate every smooth coefficient
residual.  Surjectivity is supplied by regular-frame reconstruction. -/
theorem regularFrameIntrinsicGaugeResidualCoupledPairing_detects_pointwise_zero
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (residual : SmoothQuotientField period hPeriod GaugeFiber)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] [measure.IsOpenPosMeasure]
    (coupling : Real) (hCoupling : coupling ≠ 0) :
    (∀ variation : SmoothAbelianGaugePotential period hPeriod,
        coupling * regularFrameIntrinsicGaugeResidualPairing period hPeriod
          metric residual variation measure = 0) ↔
      ∀ point : EffectiveQuotient period hPeriod, residual point = 0 := by
  constructor
  · intro hPotential
    apply (smoothGaugeField_coupled_pairing_detects_pointwise_zero period
      hPeriod residual measure coupling hCoupling).mp
    intro coefficients
    simpa only [regularFrameIntrinsicGaugeResidualPairing,
      gaugePotentialFrameCoefficients_reconstructed] using
      hPotential (regularFrameGaugePotentialFromCoefficients period hPeriod
        metric coefficients)
  · intro hPointwise variation
    exact
      ((smoothGaugeField_coupled_pairing_detects_pointwise_zero period hPeriod
        residual measure coupling hCoupling).mpr hPointwise)
          (gaugePotentialFrameCoefficients period hPeriod metric variation)

/-- Canonical-volume intrinsic Maxwell residual pairing. -/
noncomputable def canonicalRegularFrameIntrinsicGaugeResidualPairing
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (residual : SmoothQuotientField period hPeriod GaugeFiber)
    (variation : SmoothAbelianGaugePotential period hPeriod) : Real :=
  regularFrameIntrinsicGaugeResidualPairing period hPeriod metric residual
    variation (intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

/-- Gate: the canonical weak Maxwell equation, with a nonzero coupling and
all genuine smooth gauge variations, is equivalent to pointwise vanishing. -/
theorem regular_frame_maxwell_smooth_gauge_test_separation_gate
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (residual : SmoothQuotientField period hPeriod GaugeFiber)
    (coupling : Real) (hCoupling : coupling ≠ 0) :
    (∀ variation : SmoothAbelianGaugePotential period hPeriod,
        coupling * canonicalRegularFrameIntrinsicGaugeResidualPairing period
          hPeriod metric residual variation = 0) ↔
      ∀ point : EffectiveQuotient period hPeriod, residual point = 0 := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  letI : Measure.IsOpenPosMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isOpenPosMeasure period hPeriod
  simpa only [canonicalRegularFrameIntrinsicGaugeResidualPairing] using
    regularFrameIntrinsicGaugeResidualCoupledPairing_detects_pointwise_zero
      period hPeriod metric residual
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) coupling
          hCoupling

end

end P0EFTJanusProgramPRegularFrameMaxwellSmoothGaugeTestSeparation4D
end JanusFormal
