import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLLGeneratingFrameVariation4D

/-!
# The non-frozen LL generating-frame Hessian

An arbitrary linear frame tangent need not preserve the spanning condition.
The exact missing datum is therefore a curve of actual generating frames
realizing that tangent.  This file records that criterion and constructs the
simultaneous four-slot curve whenever such a realization is supplied.

Exponential frame rescaling realizes every radial frame tangent globally.
On the resulting four-slot space (frame rate, auxiliary metric, measure
coefficient, and LL flux), the true PT action has an actual Euler derivative,
a symmetric bilinear mixed Hessian, and a bundled Jacobi operator.  The frame
slot is genuinely varied: its pure radial Hessian is the kinetic action term,
not zero.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusLLGeneratingFrameFullHessian4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology BigOperators
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGlobalLLVariation4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D
open P0EFTJanusDifferentialLLKineticSimultaneousVariation4D
open P0EFTJanusPTSymmetricDifferentialLLKineticSimultaneousVariation4D
open P0EFTJanusIntegratedPTDifferentialLLKineticSimultaneousVariation4D
open P0EFTJanusIntegratedPTDifferentialLLKineticHessianVariation4D
open P0EFTJanusIntegratedPTDifferentialLLKineticMixedHessian4D
open P0EFTJanusLLMeasureFieldTwoParameterDensity4D
open P0EFTJanusIntegratedPTLLWorldvolumeHessian4D
open P0EFTJanusIntegratedPTLLWorldvolumeHessianVariation4D
open P0EFTJanusIntegratedPTFullDifferentialLLSimultaneousVariation4D
open P0EFTJanusIntegratedPTFullLLHessianVariation4D
open P0EFTJanusTruePTDifferentialLLSimultaneousVariation4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusMappingTorusLLFullWeakJacobiGaugeComplex4D
open P0EFTJanusMappingTorusLLGeneratingFrameVariation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-! ## Exact realization criterion for a general frame tangent -/

/-- A genuine simultaneous curve realizing all four LL slots.  The frame
component is a curve of actual spanning frames; the remaining three
components are the already proved affine LL curve. -/
structure LLFourSlotCurveRealization
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : LLFourSlotTangent period hPeriod frame) where
  frameCurve : LLGeneratingFrameCurve period hPeriod frame
  frameVelocity :
    frameCurve.HasVelocity period hPeriod direction.1
  fieldCurve : Real → IndependentFields period hPeriod
  fieldCurve_eq :
    ∀ t, fieldCurve t =
      llFullWeakCurve period hPeriod fields direction.2 t

/-- The only extra datum needed to realize a general four-slot tangent is an
actual generating-frame curve with the requested frame velocity. -/
theorem llFourSlotCurveRealization_nonempty_iff
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : LLFourSlotTangent period hPeriod frame) :
    Nonempty
        (LLFourSlotCurveRealization
          period hPeriod frame fields direction) ↔
      ∃ curve : LLGeneratingFrameCurve period hPeriod frame,
        curve.HasVelocity period hPeriod direction.1 := by
  constructor
  · rintro ⟨realization⟩
    exact ⟨realization.frameCurve, realization.frameVelocity⟩
  · rintro ⟨curve, hVelocity⟩
    exact ⟨
      { frameCurve := curve
        frameVelocity := hVelocity
        fieldCurve := llFullWeakCurve period hPeriod fields direction.2
        fieldCurve_eq := fun _ => rfl }⟩

/-! ## Globally realized radial four-slot curve -/

/-- Four actual variational slots, with the frame slot represented by its
globally realizable exponential radial rate. -/
abbrev LLRadialFourSlotTangent :=
  Real × LLFullWeakTangent period hPeriod

abbrev LLRadialFourSlotDual :=
  LLRadialFourSlotTangent period hPeriod →ₗ[Real] Real

/-- Embed a radial rate as the corresponding genuine frame tangent. -/
def llRadialFourSlotEmbedding
    (frame : SmoothThroatGeneratingFrame period hPeriod) :
    LLRadialFourSlotTangent period hPeriod →ₗ[Real]
      LLFourSlotTangent period hPeriod frame where
  toFun direction :=
    (llFrameRadialDirection period hPeriod frame direction.1, direction.2)
  map_add' first second := by
    apply Prod.ext
    · simp [llFrameRadialDirection, add_smul]
    · rfl
  map_smul' scalar direction := by
    apply Prod.ext
    · simp [llFrameRadialDirection, mul_smul]
    · rfl

/-- Every radial four-slot tangent has a global realization by actual
generating frames. -/
def llRadialFourSlotCurveRealization
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : LLRadialFourSlotTangent period hPeriod) :
    LLFourSlotCurveRealization period hPeriod frame fields
      (llRadialFourSlotEmbedding period hPeriod frame direction) where
  frameCurve :=
    llFrameExponentialCurve period hPeriod frame direction.1
  frameVelocity := by
    simpa [llRadialFourSlotEmbedding] using
      llFrameExponentialCurve_hasVelocity
        period hPeriod frame direction.1
  fieldCurve := llFullWeakCurve period hPeriod fields direction.2
  fieldCurve_eq := fun _ => rfl

/-- The true simultaneous curve: its first component is an actual spanning
frame at every parameter and its second component varies all three LL
fields. -/
def llRadialFourSlotCurve
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : LLRadialFourSlotTangent period hPeriod) (t : Real) :
    SmoothThroatGeneratingFrame period hPeriod ×
      IndependentFields period hPeriod :=
  ((llFrameExponentialCurve
      period hPeriod frame direction.1).toFrame t,
    llFullWeakCurve period hPeriod fields direction.2 t)

@[simp]
theorem llRadialFourSlotCurve_zero_frame_vector
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : LLRadialFourSlotTangent period hPeriod)
    (point : EffectiveThroat period hPeriod)
    (index : Fin frame.count) :
    (llRadialFourSlotCurve period hPeriod frame fields direction 0).1.vectorAt
        point index =
      frame.vectorAt point index := by
  simp [llRadialFourSlotCurve, llFrameExponentialCurve,
    llScaleGeneratingFrame]

@[simp]
theorem llRadialFourSlotCurve_zero_fields
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : LLRadialFourSlotTangent period hPeriod) :
    (llRadialFourSlotCurve period hPeriod frame fields direction 0).2 =
      fields := by
  cases fields
  simp [llRadialFourSlotCurve, llFullWeakCurve]

/-- The true PT action evaluated on the simultaneous non-frozen curve. -/
def llRadialFourSlotActionCurve
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : LLRadialFourSlotTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) (t : Real) : Real :=
  globalPTSymmetricDifferentialLLAction period hPeriod
    (llRadialFourSlotCurve period hPeriod frame fields direction t).1
    (llRadialFourSlotCurve period hPeriod frame fields direction t).2 mu

/-! ## Kinetic and worldvolume Euler pieces -/

def llFrameKineticAction
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  globalPTDifferentialLLKineticAction period hPeriod frame
    fields.llAuxMetric fields.llField mu

theorem llFrameKineticAction_scale_frame
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (scale : Real) (hScale : scale ≠ 0)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    llFrameKineticAction period hPeriod
        (llScaleGeneratingFrame period hPeriod frame scale hScale)
        fields mu =
      scale ^ 2 *
        llFrameKineticAction period hPeriod frame fields mu :=
  globalPTDifferentialLLKineticAction_scale
    period hPeriod frame scale hScale
      fields.llAuxMetric fields.llField mu

def llFrameKineticEuler
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : LLFullWeakTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ point, ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
    frame fields.llAuxMetric fields.llField
      direction.1 direction.2.2 point ∂mu

def llFrameWorldvolumeEuler
    (fields : IndependentFields period hPeriod)
    (direction : LLFullWeakTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  globalPTLLFirstVariation period hPeriod fields
    (llFullWeakVariation period hPeriod direction) mu

theorem fullLLEuler_llFullWeakDirectionPacket
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : LLFullWeakTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    fullLLEuler period hPeriod frame fields
        (llFullWeakDirectionPacket period hPeriod direction) mu =
      llFrameKineticEuler period hPeriod frame fields direction mu +
        llFrameWorldvolumeEuler period hPeriod fields direction mu :=
  rfl

private theorem throatDerivativePairing_add_right_full
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (base first second :
      SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    throatDerivativePairing period hPeriod frame base
        (first + second) point =
      throatDerivativePairing period hPeriod frame base first point +
        throatDerivativePairing period hPeriod frame base second point := by
  unfold throatDerivativePairing
  simp_rw [congrFun (congrFun
    (throatFrameDerivative_add period hPeriod LLFieldFiber frame
      first second) point)]
  simp only [Pi.add_apply, inner_add_right, Finset.sum_add_distrib]

private theorem throatDerivativePairing_smul_right_full
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (base direction :
      SmoothThroatField period hPeriod LLFieldFiber)
    (scalar : Real) (point : EffectiveThroat period hPeriod) :
    throatDerivativePairing period hPeriod frame base
        (scalar • direction) point =
      scalar *
        throatDerivativePairing period hPeriod frame base direction point := by
  unfold throatDerivativePairing
  simp_rw [congrFun (congrFun
    (throatFrameDerivative_smul period hPeriod LLFieldFiber frame
      scalar direction) point)]
  simp only [Pi.smul_apply, real_inner_smul_right, Finset.mul_sum]

private theorem ptKineticFirstVariation_add_direction
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (firstAux secondAux :
      SmoothThroatField period hPeriod LLMetricFiber)
    (firstField secondField :
      SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
        frame aux field (firstAux + secondAux)
          (firstField + secondField) point =
      ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
          frame aux field firstAux firstField point +
        ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
          frame aux field secondAux secondField point := by
  have hAux :
      differentialLLAuxMetricDirectionPT period hPeriod
          (firstAux + secondAux) =
        differentialLLAuxMetricDirectionPT period hPeriod firstAux +
          differentialLLAuxMetricDirectionPT period hPeriod secondAux := by
    apply SmoothThroatField.ext period hPeriod LLMetricFiber
    intro current
    rfl
  have hField :
      differentialLLFluxDirectionPT period hPeriod
          (firstField + secondField) =
        differentialLLFluxDirectionPT period hPeriod firstField +
          differentialLLFluxDirectionPT period hPeriod secondField := by
    apply SmoothThroatField.ext period hPeriod LLFieldFiber
    intro current
    rfl
  unfold ptSymmetricDifferentialLLKineticFirstVariation
    differentialLLKineticFirstVariation
  rw [hAux, hField,
    throatDerivativePairing_add_right_full,
    throatDerivativePairing_add_right_full]
  rw [show (firstAux + secondAux) point =
      firstAux point + secondAux point by rfl,
    show
      (differentialLLAuxMetricDirectionPT period hPeriod firstAux +
          differentialLLAuxMetricDirectionPT period hPeriod secondAux) point =
        differentialLLAuxMetricDirectionPT period hPeriod firstAux point +
          differentialLLAuxMetricDirectionPT period hPeriod secondAux point by
      rfl,
    inner_add_right, inner_add_right]
  ring

private theorem ptKineticFirstVariation_smul_direction
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (aux : SmoothThroatField period hPeriod LLMetricFiber)
    (field : SmoothThroatField period hPeriod LLFieldFiber)
    (scalar : Real)
    (dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (dField : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
        frame aux field (scalar • dAux) (scalar • dField) point =
      scalar *
        ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
          frame aux field dAux dField point := by
  have hAux :
      differentialLLAuxMetricDirectionPT period hPeriod (scalar • dAux) =
        scalar •
          differentialLLAuxMetricDirectionPT period hPeriod dAux := by
    apply SmoothThroatField.ext period hPeriod LLMetricFiber
    intro current
    rfl
  have hField :
      differentialLLFluxDirectionPT period hPeriod (scalar • dField) =
        scalar • differentialLLFluxDirectionPT period hPeriod dField := by
    apply SmoothThroatField.ext period hPeriod LLFieldFiber
    intro current
    rfl
  unfold ptSymmetricDifferentialLLKineticFirstVariation
    differentialLLKineticFirstVariation
  rw [hAux, hField,
    throatDerivativePairing_smul_right_full,
    throatDerivativePairing_smul_right_full]
  rw [show (scalar • dAux) point = scalar • dAux point by rfl,
    show
      (scalar • differentialLLAuxMetricDirectionPT period hPeriod dAux)
          point =
        scalar •
          differentialLLAuxMetricDirectionPT period hPeriod dAux point by
      rfl,
    real_inner_smul_right, real_inner_smul_right]
  ring

theorem llFrameKineticEuler_add
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : LLFullWeakTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    llFrameKineticEuler period hPeriod frame fields (first + second) mu =
      llFrameKineticEuler period hPeriod frame fields first mu +
        llFrameKineticEuler period hPeriod frame fields second mu := by
  unfold llFrameKineticEuler
  change (∫ point,
      ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
        frame fields.llAuxMetric fields.llField
          (first.1 + second.1) (first.2.2 + second.2.2) point ∂mu) = _
  rw [show
    (fun point =>
      ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
        frame fields.llAuxMetric fields.llField
          (first.1 + second.1) (first.2.2 + second.2.2) point) =
      fun point =>
        ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
            frame fields.llAuxMetric fields.llField
              first.1 first.2.2 point +
          ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
            frame fields.llAuxMetric fields.llField
              second.1 second.2.2 point by
    funext point
    exact ptKineticFirstVariation_add_direction
      period hPeriod frame fields.llAuxMetric fields.llField
        first.1 second.1 first.2.2 second.2.2 point]
  rw [integral_add
    (ptSymmetricDifferentialLLKineticFirstVariation_integrable
      period hPeriod frame fields.llAuxMetric fields.llField
        first.1 first.2.2 mu)
    (ptSymmetricDifferentialLLKineticFirstVariation_integrable
      period hPeriod frame fields.llAuxMetric fields.llField
        second.1 second.2.2 mu)]

theorem llFrameKineticEuler_smul
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (scalar : Real) (direction : LLFullWeakTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    llFrameKineticEuler period hPeriod frame fields
        (scalar • direction) mu =
      scalar *
        llFrameKineticEuler period hPeriod frame fields direction mu := by
  unfold llFrameKineticEuler
  change (∫ point,
      ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
        frame fields.llAuxMetric fields.llField
          (scalar • direction.1) (scalar • direction.2.2) point ∂mu) = _
  rw [show
    (fun point =>
      ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
        frame fields.llAuxMetric fields.llField
          (scalar • direction.1) (scalar • direction.2.2) point) =
      fun point => scalar *
        ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
          frame fields.llAuxMetric fields.llField
            direction.1 direction.2.2 point by
    funext point
    exact ptKineticFirstVariation_smul_direction
      period hPeriod frame fields.llAuxMetric fields.llField scalar
        direction.1 direction.2.2 point]
  exact integral_const_mul scalar _

@[simp]
theorem llFrameKineticEuler_zero
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    llFrameKineticEuler period hPeriod frame fields
        (0 : LLFullWeakTangent period hPeriod) mu = 0 := by
  simpa using llFrameKineticEuler_smul
    period hPeriod frame fields 0
      (0 : LLFullWeakTangent period hPeriod) mu

private theorem throatDerivativePairing_scale_frame
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (scale : Real) (hScale : scale ≠ 0)
    (first second :
      SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    throatDerivativePairing period hPeriod
        (llScaleGeneratingFrame period hPeriod frame scale hScale)
        first second point =
      scale ^ 2 *
        throatDerivativePairing period hPeriod frame first second point := by
  unfold throatDerivativePairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [throatFrameDerivative_scale, throatFrameDerivative_scale]
  simp only [real_inner_smul_left, real_inner_smul_right]
  ring

private theorem ptKineticFirstVariation_scale_frame
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (scale : Real) (hScale : scale ≠ 0)
    (aux dAux : SmoothThroatField period hPeriod LLMetricFiber)
    (field dField : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
        (llScaleGeneratingFrame period hPeriod frame scale hScale)
        aux field dAux dField point =
      scale ^ 2 *
        ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
          frame aux field dAux dField point := by
  unfold ptSymmetricDifferentialLLKineticFirstVariation
    differentialLLKineticFirstVariation
  rw [throatDerivativePairing_scale_frame,
    throatDerivativeEnergy_scale,
    throatDerivativePairing_scale_frame,
    throatDerivativeEnergy_scale]
  ring

theorem llFrameKineticEuler_scale_frame
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (scale : Real) (hScale : scale ≠ 0)
    (fields : IndependentFields period hPeriod)
    (direction : LLFullWeakTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    llFrameKineticEuler period hPeriod
        (llScaleGeneratingFrame period hPeriod frame scale hScale)
        fields direction mu =
      scale ^ 2 *
        llFrameKineticEuler period hPeriod frame fields direction mu := by
  unfold llFrameKineticEuler
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with point
  exact ptKineticFirstVariation_scale_frame
    period hPeriod frame scale hScale
      fields.llAuxMetric direction.1 fields.llField direction.2.2 point

/-! ## Actual Euler derivative -/

def llRadialFourSlotEuler
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : LLRadialFourSlotTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  2 * direction.1 *
      llFrameKineticAction period hPeriod frame fields mu +
    llFrameKineticEuler period hPeriod frame fields direction.2 mu +
    llFrameWorldvolumeEuler period hPeriod fields direction.2 mu

private theorem llRadialFourSlotActionCurve_eq_fixed_add_correction
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : LLRadialFourSlotTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (t : Real) :
    llRadialFourSlotActionCurve period hPeriod frame fields direction mu t =
      globalPTSymmetricDifferentialLLAction period hPeriod frame
          (llFullWeakCurve period hPeriod fields direction.2 t) mu +
        (Real.exp (direction.1 * t) ^ 2 - 1) *
          llFrameKineticAction period hPeriod frame
            (llFullWeakCurve period hPeriod fields direction.2 t) mu := by
  unfold llRadialFourSlotActionCurve llRadialFourSlotCurve
    llFrameKineticAction
  rw [truePTAction_frameExponential_eq]
  rw [← globalPTFullDifferentialLLAction_eq_true period hPeriod frame
    (llFullWeakCurve period hPeriod fields direction.2 t) mu]
  unfold globalPTFullDifferentialLLAction
  ring

theorem llRadialFourSlotActionCurve_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : LLRadialFourSlotTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      (llRadialFourSlotActionCurve
        period hPeriod frame fields direction mu)
      (llRadialFourSlotEuler
        period hPeriod frame fields direction mu) 0 := by
  have hFixed := truePTAction_fullCurve_hasDerivAt_fullLLEuler
    period hPeriod frame fields
      (llFullWeakDirectionPacket period hPeriod direction.2) mu
  have hFixed' :
      HasDerivAt
        (fun t : Real =>
          globalPTSymmetricDifferentialLLAction period hPeriod frame
            (llFullWeakCurve period hPeriod fields direction.2 t) mu)
        (llFrameKineticEuler period hPeriod frame fields direction.2 mu +
          llFrameWorldvolumeEuler period hPeriod fields direction.2 mu) 0 := by
    rw [show
      (fun t : Real =>
        globalPTSymmetricDifferentialLLAction period hPeriod frame
          (llFullWeakCurve period hPeriod fields direction.2 t) mu) =
        fun t : Real =>
          globalPTSymmetricDifferentialLLAction period hPeriod frame
            (differentialLLFullCurve period hPeriod fields
              (llFullWeakDirectionPacket
                period hPeriod direction.2).llAuxMetric
              (llFullWeakDirectionPacket
                period hPeriod direction.2).llMeasure
              (llFullWeakDirectionPacket
                period hPeriod direction.2).common.ll t) mu by
      rfl]
    rw [← fullLLEuler_llFullWeakDirectionPacket]
    exact hFixed
  have hExp :
      HasDerivAt (fun t : Real => Real.exp (direction.1 * t))
        direction.1 0 := by
    have hInner :
        HasDerivAt (fun t : Real => direction.1 * t) direction.1 0 := by
      simpa using (hasDerivAt_id (0 : Real)).const_mul direction.1
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (direction.1 * 0)).comp 0 hInner
  have hScale :
      HasDerivAt
        (fun t : Real => Real.exp (direction.1 * t) ^ 2 - 1)
        (2 * direction.1) 0 := by
    simpa using (hExp.pow 2).sub_const 1
  have hKinetic :=
    globalPTDifferentialLLKineticAction_simultaneous_hasDerivAt
      period hPeriod frame fields.llAuxMetric direction.2.1
        fields.llField direction.2.2.2 mu
  have hKinetic' :
      HasDerivAt
        (fun t : Real =>
          llFrameKineticAction period hPeriod frame
            (llFullWeakCurve period hPeriod fields direction.2 t) mu)
        (llFrameKineticEuler
          period hPeriod frame fields direction.2 mu) 0 := by
    simpa [llFrameKineticAction, llFrameKineticEuler,
      llFullWeakCurve] using hKinetic
  have hFieldsZero :
      llFullWeakCurve period hPeriod fields direction.2 0 = fields := by
    cases fields
    simp [llFullWeakCurve]
  have hCorrection := hScale.mul hKinetic'
  simp [hFieldsZero] at hCorrection
  rw [show
    llRadialFourSlotActionCurve period hPeriod frame fields direction mu =
      (fun t =>
        globalPTSymmetricDifferentialLLAction period hPeriod frame
          (llFullWeakCurve period hPeriod fields direction.2 t) mu) +
      (fun t =>
        (Real.exp (direction.1 * t) ^ 2 - 1) *
            llFrameKineticAction period hPeriod frame
              (llFullWeakCurve period hPeriod fields direction.2 t) mu) by
    funext t
    exact llRadialFourSlotActionCurve_eq_fixed_add_correction
      period hPeriod frame fields direction mu t]
  have hValue :
      (llFrameKineticEuler period hPeriod frame fields direction.2 mu +
          llFrameWorldvolumeEuler period hPeriod fields direction.2 mu) +
        2 * direction.1 *
          llFrameKineticAction period hPeriod frame fields mu =
      llRadialFourSlotEuler
        period hPeriod frame fields direction mu := by
    unfold llRadialFourSlotEuler
    ring
  rw [← hValue]
  exact hFixed'.add hCorrection

/-! ## Mixed Euler derivative and full radial-frame Hessian -/

def llRadialFourSlotNestedActionCurve
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : LLRadialFourSlotTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (t s : Real) : Real :=
  llRadialFourSlotActionCurve period hPeriod
    ((llFrameExponentialCurve
      period hPeriod frame second.1).toFrame t)
    (llFullWeakCurve period hPeriod fields second.2 t)
    first mu s

def llRadialFourSlotEulerAlong
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : LLRadialFourSlotTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) (t : Real) : Real :=
  llRadialFourSlotEuler period hPeriod
    ((llFrameExponentialCurve
      period hPeriod frame second.1).toFrame t)
    (llFullWeakCurve period hPeriod fields second.2 t)
    first mu

theorem llRadialFourSlotNestedActionCurve_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : LLRadialFourSlotTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (t : Real) :
    HasDerivAt
      (fun s =>
        llRadialFourSlotNestedActionCurve
          period hPeriod frame fields first second mu t s)
      (llRadialFourSlotEulerAlong
        period hPeriod frame fields first second mu t) 0 := by
  exact llRadialFourSlotActionCurve_hasDerivAt
    period hPeriod
      ((llFrameExponentialCurve
        period hPeriod frame second.1).toFrame t)
      (llFullWeakCurve period hPeriod fields second.2 t)
      first mu

private def llKineticEulerAlong
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : LLFullWeakTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) (t : Real) : Real :=
  ∫ point, ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
    frame
      (fields.llAuxMetric + t • second.1)
      (fields.llField + t • second.2.2)
      first.1 first.2.2 point ∂mu

private def llWorldvolumeEulerAlong
    (fields : IndependentFields period hPeriod)
    (first second : LLFullWeakTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) (t : Real) : Real :=
  globalPTLLFirstVariation period hPeriod
    (llMeasureFieldCurve period hPeriod fields
      (llFullWeakVariation period hPeriod second) t t)
    (llFullWeakVariation period hPeriod first) mu

private theorem llRadialFourSlotEulerAlong_formula
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : LLRadialFourSlotTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) (t : Real) :
    llRadialFourSlotEulerAlong
        period hPeriod frame fields first second mu t =
      2 * first.1 * Real.exp (second.1 * t) ^ 2 *
          llFrameKineticAction period hPeriod frame
            (llFullWeakCurve period hPeriod fields second.2 t) mu +
        Real.exp (second.1 * t) ^ 2 *
          llKineticEulerAlong period hPeriod frame fields
            first.2 second.2 mu t +
        llWorldvolumeEulerAlong period hPeriod fields
          first.2 second.2 mu t := by
  unfold llRadialFourSlotEulerAlong llRadialFourSlotEuler
    llFrameWorldvolumeEuler llKineticEulerAlong llWorldvolumeEulerAlong
  dsimp only [llFrameExponentialCurve]
  rw [llFrameKineticAction_scale_frame]
  rw [llFrameKineticEuler_scale_frame]
  change
    2 * first.1 * (Real.exp (second.1 * t) ^ 2 *
        llFrameKineticAction period hPeriod frame
          (llFullWeakCurve period hPeriod fields second.2 t) mu) +
      Real.exp (second.1 * t) ^ 2 *
        (∫ point,
          ptSymmetricDifferentialLLKineticFirstVariation period hPeriod
            frame
              (fields.llAuxMetric + t • second.2.1)
              (fields.llField + t • second.2.2.2)
              first.2.1 first.2.2.2 point ∂mu) +
      globalPTLLFirstVariation period hPeriod
        (llMeasureFieldCurve period hPeriod fields
          (llFullWeakVariation period hPeriod second.2) t t)
        (llFullWeakVariation period hPeriod first.2) mu = _
  ring

def llRadialFourSlotHessian
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : LLRadialFourSlotTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  llFullWeakHessian period hPeriod frame fields first.2 second.2 mu +
    4 * first.1 * second.1 *
      llFrameKineticAction period hPeriod frame fields mu +
    2 * first.1 *
      llFrameKineticEuler period hPeriod frame fields second.2 mu +
    2 * second.1 *
      llFrameKineticEuler period hPeriod frame fields first.2 mu

theorem llRadialFourSlotEulerAlong_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : LLRadialFourSlotTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      (llRadialFourSlotEulerAlong
        period hPeriod frame fields first second mu)
      (llRadialFourSlotHessian
        period hPeriod frame fields first second mu) 0 := by
  have hExp :
      HasDerivAt (fun t : Real => Real.exp (second.1 * t))
        second.1 0 := by
    have hInner :
        HasDerivAt (fun t : Real => second.1 * t) second.1 0 := by
      simpa using (hasDerivAt_id (0 : Real)).const_mul second.1
    simpa [Function.comp_def] using
      (Real.hasDerivAt_exp (second.1 * 0)).comp 0 hInner
  have hScale := hExp.pow 2
  have hKinetic :=
    globalPTDifferentialLLKineticAction_simultaneous_hasDerivAt
      period hPeriod frame fields.llAuxMetric second.2.1
        fields.llField second.2.2.2 mu
  have hKinetic' :
      HasDerivAt
        (fun t : Real =>
          llFrameKineticAction period hPeriod frame
            (llFullWeakCurve period hPeriod fields second.2 t) mu)
        (llFrameKineticEuler period hPeriod frame fields second.2 mu) 0 := by
    simpa [llFrameKineticAction, llFrameKineticEuler,
      llFullWeakCurve] using hKinetic
  have hFieldsZero :
      llFullWeakCurve period hPeriod fields second.2 0 = fields := by
    cases fields
    simp [llFullWeakCurve]
  have hScaledKinetic := hScale.mul hKinetic'
  simp [hFieldsZero] at hScaledKinetic
  have hFirst :=
    globalPTDifferentialLLKineticFirstVariation_second_direction_hasDerivAt
      period hPeriod frame
        fields.llAuxMetric first.2.1 second.2.1
        fields.llField first.2.2.2 second.2.2.2 mu
  have hFirst' :
      HasDerivAt
        (llKineticEulerAlong period hPeriod frame fields
          first.2 second.2 mu)
        (globalPTDifferentialLLKineticMixedHessian period hPeriod frame
          fields.llAuxMetric fields.llField
          first.2.1 second.2.1 first.2.2.2 second.2.2.2 mu) 0 := by
    exact hFirst
  have hScaledFirst := hScale.mul hFirst'
  simp [llKineticEulerAlong, llFrameKineticEuler] at hScaledFirst
  have hWorld :=
    globalPTLLFirstVariation_second_direction_hasDerivAt
      period hPeriod fields
        (llFullWeakVariation period hPeriod first.2)
        (llFullWeakVariation period hPeriod second.2) mu
  have hWorld' :
      HasDerivAt
        (llWorldvolumeEulerAlong period hPeriod fields
          first.2 second.2 mu)
        (globalPTLLWorldvolumeHessian period hPeriod fields
          (llFullWeakVariation period hPeriod first.2)
          (llFullWeakVariation period hPeriod second.2) mu) 0 :=
    hWorld
  have hTotal :=
    ((hScaledKinetic.const_mul (2 * first.1)).add
      hScaledFirst).add hWorld'
  rw [show
    llRadialFourSlotEulerAlong
        period hPeriod frame fields first second mu =
      ((fun t =>
        (2 * first.1) *
          (Real.exp (second.1 * t) ^ 2 *
            llFrameKineticAction period hPeriod frame
              (llFullWeakCurve period hPeriod fields second.2 t) mu)) +
        (fun t =>
          Real.exp (second.1 * t) ^ 2 *
            llKineticEulerAlong period hPeriod frame fields
              first.2 second.2 mu t)) +
        llWorldvolumeEulerAlong period hPeriod fields
          first.2 second.2 mu by
    funext t
    simp only [Pi.add_apply]
    rw [llRadialFourSlotEulerAlong_formula]
    ring]
  have hValue :
      (2 * first.1) *
          (2 * second.1 *
              llFrameKineticAction period hPeriod frame fields mu +
            llFrameKineticEuler
              period hPeriod frame fields second.2 mu) +
        (2 * second.1 *
            llFrameKineticEuler
              period hPeriod frame fields first.2 mu +
          globalPTDifferentialLLKineticMixedHessian period hPeriod frame
            fields.llAuxMetric fields.llField
            first.2.1 second.2.1 first.2.2.2 second.2.2.2 mu) +
        globalPTLLWorldvolumeHessian period hPeriod fields
          (llFullWeakVariation period hPeriod first.2)
          (llFullWeakVariation period hPeriod second.2) mu =
      llRadialFourSlotHessian
        period hPeriod frame fields first second mu := by
    unfold llRadialFourSlotHessian llFullWeakHessian
    ring
  rw [← hValue]
  exact hTotal

theorem llRadialFourSlotHessian_symmetric
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : LLRadialFourSlotTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    llRadialFourSlotHessian period hPeriod frame fields first second mu =
      llRadialFourSlotHessian
        period hPeriod frame fields second first mu := by
  unfold llRadialFourSlotHessian
  rw [llFullWeakHessian_symmetric]
  ring

theorem llRadialFourSlotHessian_add_left
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second test : LLRadialFourSlotTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    llRadialFourSlotHessian period hPeriod frame fields
        (first + second) test mu =
      llRadialFourSlotHessian period hPeriod frame fields first test mu +
        llRadialFourSlotHessian
          period hPeriod frame fields second test mu := by
  unfold llRadialFourSlotHessian
  change
    llFullWeakHessian period hPeriod frame fields
        (first.2 + second.2) test.2 mu +
      4 * (first.1 + second.1) * test.1 *
        llFrameKineticAction period hPeriod frame fields mu +
      2 * (first.1 + second.1) *
        llFrameKineticEuler period hPeriod frame fields test.2 mu +
      2 * test.1 *
        llFrameKineticEuler period hPeriod frame fields
          (first.2 + second.2) mu = _
  rw [llFullWeakHessian_add_left, llFrameKineticEuler_add]
  ring

theorem llRadialFourSlotHessian_smul_left
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (scalar : Real)
    (first test : LLRadialFourSlotTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    llRadialFourSlotHessian period hPeriod frame fields
        (scalar • first) test mu =
      scalar *
        llRadialFourSlotHessian
          period hPeriod frame fields first test mu := by
  unfold llRadialFourSlotHessian
  change
    llFullWeakHessian period hPeriod frame fields
        (scalar • first.2) test.2 mu +
      4 * (scalar * first.1) * test.1 *
        llFrameKineticAction period hPeriod frame fields mu +
      2 * (scalar * first.1) *
        llFrameKineticEuler period hPeriod frame fields test.2 mu +
      2 * test.1 *
        llFrameKineticEuler period hPeriod frame fields
          (scalar • first.2) mu = _
  rw [llFullWeakHessian_smul_left, llFrameKineticEuler_smul]
  ring

theorem llRadialFourSlotHessian_add_right
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second test : LLRadialFourSlotTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    llRadialFourSlotHessian period hPeriod frame fields test
        (first + second) mu =
      llRadialFourSlotHessian period hPeriod frame fields test first mu +
        llRadialFourSlotHessian
          period hPeriod frame fields test second mu := by
  rw [llRadialFourSlotHessian_symmetric
      period hPeriod frame fields test (first + second) mu,
    llRadialFourSlotHessian_add_left,
    llRadialFourSlotHessian_symmetric
      period hPeriod frame fields first test mu,
    llRadialFourSlotHessian_symmetric
      period hPeriod frame fields second test mu]

theorem llRadialFourSlotHessian_smul_right
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (scalar : Real)
    (first test : LLRadialFourSlotTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    llRadialFourSlotHessian period hPeriod frame fields test
        (scalar • first) mu =
      scalar *
        llRadialFourSlotHessian
          period hPeriod frame fields test first mu := by
  rw [llRadialFourSlotHessian_symmetric
      period hPeriod frame fields test (scalar • first) mu,
    llRadialFourSlotHessian_smul_left,
    llRadialFourSlotHessian_symmetric
      period hPeriod frame fields first test mu]

/-- The genuine four-slot Jacobi operator on the globally realized radial
frame sector. -/
def llRadialFourSlotJacobiOperator
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    LLRadialFourSlotTangent period hPeriod →ₗ[Real]
      LLRadialFourSlotDual period hPeriod where
  toFun first :=
    { toFun := fun second =>
        llRadialFourSlotHessian
          period hPeriod frame fields first second mu
      map_add' := fun second third =>
        llRadialFourSlotHessian_add_right
          period hPeriod frame fields second third first mu
      map_smul' := fun scalar second =>
        llRadialFourSlotHessian_smul_right
          period hPeriod frame fields scalar second first mu }
  map_add' first second := by
    apply LinearMap.ext
    intro test
    exact llRadialFourSlotHessian_add_left
      period hPeriod frame fields first second test mu
  map_smul' scalar first := by
    apply LinearMap.ext
    intro test
    exact llRadialFourSlotHessian_smul_left
      period hPeriod frame fields scalar first test mu

@[simp]
theorem llRadialFourSlotJacobiOperator_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (first second : LLRadialFourSlotTangent period hPeriod) :
    llRadialFourSlotJacobiOperator period hPeriod frame fields mu
        first second =
      llRadialFourSlotHessian
        period hPeriod frame fields first second mu :=
  rfl

/-- Unlike the old frame-frozen pullback, the true pure-frame Hessian is the
radial second variation of the kinetic action. -/
theorem llRadialFourSlotHessian_pureFrame
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (firstRate secondRate : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    llRadialFourSlotHessian period hPeriod frame fields
        (firstRate, 0) (secondRate, 0) mu =
      4 * firstRate * secondRate *
        llFrameKineticAction period hPeriod frame fields mu := by
  unfold llRadialFourSlotHessian
  have hHessian :
      llFullWeakHessian period hPeriod frame fields
          (0 : LLFullWeakTangent period hPeriod)
          (0 : LLFullWeakTangent period hPeriod) mu = 0 := by
    simpa using llFullWeakHessian_smul_left
      period hPeriod frame fields 0
        (0 : LLFullWeakTangent period hPeriod)
        (0 : LLFullWeakTangent period hPeriod) mu
  rw [hHessian, llFrameKineticEuler_zero]
  ring

/-! ## Exact Jacobi and gauge criteria -/

private theorem llFullWeakHessian_zero_right_full
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : LLFullWeakTangent period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    llFullWeakHessian period hPeriod frame fields direction
        (0 : LLFullWeakTangent period hPeriod) mu = 0 := by
  simpa using llFullWeakHessian_smul_right
    period hPeriod frame fields 0
      (0 : LLFullWeakTangent period hPeriod) direction mu

/-- Exact kernel criterion for the non-frozen Jacobi operator.  The first
equation is the frame test; the second is the complete three-slot test. -/
theorem llRadialFourSlotJacobiOperator_eq_zero_iff
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (direction : LLRadialFourSlotTangent period hPeriod) :
    llRadialFourSlotJacobiOperator period hPeriod frame fields mu
        direction = 0 ↔
      (4 * direction.1 *
          llFrameKineticAction period hPeriod frame fields mu +
        2 * llFrameKineticEuler period hPeriod frame fields
          direction.2 mu = 0) ∧
      (∀ test : LLFullWeakTangent period hPeriod,
        llFullWeakHessian period hPeriod frame fields
            direction.2 test mu +
          2 * direction.1 *
            llFrameKineticEuler period hPeriod frame fields test mu = 0) := by
  constructor
  · intro hZero
    constructor
    · have hApply := congrArg
        (fun functional =>
          functional ((1 : Real), (0 : LLFullWeakTangent period hPeriod)))
        hZero
      simpa [llRadialFourSlotHessian, llFrameKineticEuler_zero,
        llFullWeakHessian_zero_right_full] using hApply
    · intro test
      have hApply := congrArg
        (fun functional => functional ((0 : Real), test)) hZero
      simpa [llRadialFourSlotHessian] using hApply
  · rintro ⟨hFrame, hField⟩
    apply LinearMap.ext
    intro test
    rw [llRadialFourSlotJacobiOperator_apply]
    unfold llRadialFourSlotHessian
    calc
      _ = test.1 *
            (4 * direction.1 *
                llFrameKineticAction period hPeriod frame fields mu +
              2 * llFrameKineticEuler period hPeriod frame fields
                direction.2 mu) +
          (llFullWeakHessian period hPeriod frame fields
              direction.2 test.2 mu +
            2 * direction.1 *
              llFrameKineticEuler period hPeriod frame fields test.2 mu) := by
            ring
      _ = 0 := by rw [hFrame, hField test.2]; ring

/-- A diagonal Lie direction lies in the globally realized radial sector
exactly when its frame Lie derivative is radial. -/
def LLDiagonalGaugeFrameIsRadial
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (ghost : CInfinityThroatGhost period hPeriod)
    (rate : Real) : Prop :=
  llFrameLieDerivative period hPeriod frame ghost
      (llFrameBaseTangent period hPeriod frame) =
    llFrameRadialDirection period hPeriod frame rate

/-- Candidate diagonal gauge direction in the radial four-slot coordinates. -/
def llRadialDiagonalGaugeDirection
    (fields : IndependentFields period hPeriod)
    (rate : Real) (ghost : CInfinityThroatGhost period hPeriod) :
    LLRadialFourSlotTangent period hPeriod :=
  (rate,
    (llEuclideanLieDerivative period hPeriod ghost fields.llAuxMetric,
      (llRealLieDerivative period hPeriod ghost fields.llMeasure,
        llEuclideanLieDerivative period hPeriod ghost fields.llField)))

theorem llRadialDiagonalGaugeDirection_embedding_eq
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (rate : Real) (ghost : CInfinityThroatGhost period hPeriod)
    (hRadial :
      LLDiagonalGaugeFrameIsRadial
        period hPeriod frame ghost rate) :
    llRadialFourSlotEmbedding period hPeriod frame
        (llRadialDiagonalGaugeDirection
          period hPeriod fields rate ghost) =
      llFourSlotDiagonalGaugeDirection
        period hPeriod frame fields ghost := by
  apply Prod.ext
  · exact hRadial.symm
  · rfl

/-- No gauge-nullity is postulated.  Under the exact radiality condition
above, this equivalence gives the two and only two equations needed for a
diagonal Lie direction to be a Jacobi gauge direction. -/
theorem llRadialDiagonalGaugeDirection_jacobi_eq_zero_iff
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (rate : Real) (ghost : CInfinityThroatGhost period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    llRadialFourSlotJacobiOperator period hPeriod frame fields mu
        (llRadialDiagonalGaugeDirection
          period hPeriod fields rate ghost) = 0 ↔
      (4 * rate *
          llFrameKineticAction period hPeriod frame fields mu +
        2 * llFrameKineticEuler period hPeriod frame fields
          (llRadialDiagonalGaugeDirection
            period hPeriod fields rate ghost).2 mu = 0) ∧
      (∀ test : LLFullWeakTangent period hPeriod,
        llFullWeakHessian period hPeriod frame fields
            (llRadialDiagonalGaugeDirection
              period hPeriod fields rate ghost).2 test mu +
          2 * rate *
            llFrameKineticEuler period hPeriod frame fields test mu = 0) :=
  llRadialFourSlotJacobiOperator_eq_zero_iff
    period hPeriod frame fields mu
      (llRadialDiagonalGaugeDirection
        period hPeriod fields rate ghost)

end

end P0EFTJanusMappingTorusLLGeneratingFrameFullHessian4D
end JanusFormal
