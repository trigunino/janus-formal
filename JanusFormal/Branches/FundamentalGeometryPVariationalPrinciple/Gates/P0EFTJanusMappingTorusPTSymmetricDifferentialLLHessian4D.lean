import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D

/-!
# Hessian of the PT-symmetrized differential LL weak action

The PT-averaged action is unchanged.  This gate differentiates its already
derived weak Euler pairing in an independent flux direction.  The result is a
global symmetric two-direction Hessian, and the linearization identity is exact for
the complete affine curve, not merely asymptotic.  Its kinetic part is
nonnegative on diagonal directions for every measure.

The full Hessian also contains the algebraic coefficient `llMeasure`; without
a sign assumption on that independent field it is not claimed positive.  The
construction remains the weak finite-generator model and does not identify a
strong self-adjoint divergence operator or its boundary domain.
The auxiliary-metric Hessian of each raw orbit term is derived and proved
positive, but its separate PT-averaged stationarity package is not assembled
in this gate.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGlobalLLCovariance4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLWeakEquation4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

local instance effectiveThroatCompactSpace :
    CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod

local instance effectiveThroatMeasurableSpace :
    MeasurableSpace (EffectiveThroat period hPeriod) := borel _

local instance effectiveThroatBorelSpace :
    BorelSpace (EffectiveThroat period hPeriod) where
  measurable_eq := rfl

/-- Exact linearity of the differentiated finite-frame pairing in its first
field along an affine curve. -/
theorem throatDerivativePairing_fluxCurve_affine
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (base first second : SmoothThroatField period hPeriod LLFieldFiber)
    (epsilon : Real) (point : EffectiveThroat period hPeriod) :
    throatDerivativePairing period hPeriod frame
        (base + epsilon • first) second point =
      throatDerivativePairing period hPeriod frame base second point +
        epsilon * throatDerivativePairing period hPeriod frame
          first second point := by
  have hDerivative (index : Fin frame.count) :
      throatFrameDerivative period hPeriod LLFieldFiber frame
          (base + epsilon • first) point index =
        throatFrameDerivative period hPeriod LLFieldFiber frame base point index +
          epsilon • throatFrameDerivative period hPeriod LLFieldFiber frame
            first point index := by
    rw [congrFun (congrFun
      (throatFrameDerivative_add period hPeriod LLFieldFiber frame
        base (epsilon • first)) point) index]
    simp only [Pi.add_apply]
    rw [congrFun (congrFun
      (throatFrameDerivative_smul period hPeriod LLFieldFiber frame
        epsilon first) point) index]
    simp only [Pi.smul_apply]
  unfold throatDerivativePairing
  simp_rw [hDerivative, inner_add_left, real_inner_smul_left,
    Finset.sum_add_distrib, ← Finset.mul_sum]

/-- Pointwise raw flux Hessian: derivative of the weak Euler pairing in an
independent flux direction. -/
def differentialLLFluxHessianDensity
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) : Real :=
  llAuxiliaryKineticWeight period hPeriod fields point *
      throatDerivativePairing period hPeriod frame first second point +
    2 * fields.llMeasure point *
      inner Real (first point) (second point)

/-- Exact pointwise identification of the Hessian with the linearized weak
Euler density. -/
theorem differentialLLFluxFirstVariationDensity_fluxCurve_affine
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (epsilon : Real) (point : EffectiveThroat period hPeriod) :
    differentialLLFluxFirstVariationDensity period hPeriod frame
        (differentialLLFluxCurve period hPeriod fields first epsilon)
        second point =
      differentialLLFluxFirstVariationDensity period hPeriod frame
          fields second point +
        epsilon * differentialLLFluxHessianDensity period hPeriod
          frame fields first second point := by
  have hFieldCurve :
      (fields.llField + epsilon • first) point =
        fields.llField point + epsilon • first point :=
    rfl
  unfold differentialLLFluxFirstVariationDensity
    differentialLLFluxCurve differentialLLFluxHessianDensity
    llAuxiliaryKineticWeight
  rw [throatDerivativePairing_fluxCurve_affine period hPeriod frame
    fields.llField first second epsilon point]
  change
    (1 + ‖fields.llAuxMetric point‖ ^ 2) *
          (throatDerivativePairing period hPeriod frame
              fields.llField second point +
            epsilon * throatDerivativePairing period hPeriod frame
              first second point) +
        2 * fields.llMeasure point *
          inner Real ((fields.llField + epsilon • first) point) (second point) = _
  rw [hFieldCurve, inner_add_left, real_inner_smul_left]
  ring

theorem differentialLLFluxHessianDensity_continuous
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber) :
    Continuous (differentialLLFluxHessianDensity period hPeriod
      frame fields first second) := by
  exact
    ((llAuxiliaryKineticWeight_continuous period hPeriod fields).mul
      (throatDerivativePairing_continuous period hPeriod frame first second)).add
    ((continuous_const.mul fields.llMeasure.contMDiff_toFun.continuous).mul
      (first.contMDiff_toFun.continuous.inner
        second.contMDiff_toFun.continuous))

/-- Integrated raw Hessian. -/
def globalDifferentialLLFluxHessian
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ point, differentialLLFluxHessianDensity period hPeriod
    frame fields first second point ∂mu

private theorem continuous_real_integrable
    (function : EffectiveThroat period hPeriod → Real)
    (hContinuous : Continuous function)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable function mu :=
  hContinuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace function)

/-- Exact global affine linearization of the raw weak pairing. -/
theorem globalDifferentialLLFluxFirstVariation_fluxCurve_affine
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (epsilon : Real) :
    globalDifferentialLLFluxFirstVariation period hPeriod frame
        (differentialLLFluxCurve period hPeriod fields first epsilon)
        second mu =
      globalDifferentialLLFluxFirstVariation period hPeriod
          frame fields second mu +
        epsilon * globalDifferentialLLFluxHessian period hPeriod
          frame fields first second mu := by
  have hFirst := continuous_real_integrable period hPeriod
    (differentialLLFluxFirstVariationDensity period hPeriod
      frame fields second)
    (differentialLLFluxFirstVariationDensity_continuous period hPeriod
      frame fields second) mu
  have hHessian := continuous_real_integrable period hPeriod
    (differentialLLFluxHessianDensity period hPeriod
      frame fields first second)
    (differentialLLFluxHessianDensity_continuous period hPeriod
      frame fields first second) mu
  unfold globalDifferentialLLFluxFirstVariation
    globalDifferentialLLFluxHessian
  simp_rw [differentialLLFluxFirstVariationDensity_fluxCurve_affine
    period hPeriod frame fields first second epsilon]
  calc
    (∫ point,
        differentialLLFluxFirstVariationDensity period hPeriod
            frame fields second point +
          epsilon * differentialLLFluxHessianDensity period hPeriod
            frame fields first second point ∂mu) =
        (∫ point, differentialLLFluxFirstVariationDensity period hPeriod
          frame fields second point ∂mu) +
          ∫ point, epsilon * differentialLLFluxHessianDensity period hPeriod
            frame fields first second point ∂mu := by
      simpa only [Pi.add_apply] using
        integral_add hFirst (hHessian.const_mul epsilon)
    _ = _ := by
      simp only [integral_const_mul]

/-- The raw Hessian is the actual derivative of the weak Euler pairing. -/
theorem globalDifferentialLLFluxFirstVariation_fluxCurve_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      (fun epsilon : Real =>
        globalDifferentialLLFluxFirstVariation period hPeriod frame
          (differentialLLFluxCurve period hPeriod fields first epsilon)
          second mu)
      (globalDifferentialLLFluxHessian period hPeriod
        frame fields first second mu) 0 := by
  rw [show (fun epsilon : Real =>
      globalDifferentialLLFluxFirstVariation period hPeriod frame
        (differentialLLFluxCurve period hPeriod fields first epsilon)
        second mu) =
      (fun epsilon : Real =>
        globalDifferentialLLFluxFirstVariation period hPeriod
            frame fields second mu +
          epsilon * globalDifferentialLLFluxHessian period hPeriod
            frame fields first second mu) from by
      funext epsilon
      exact globalDifferentialLLFluxFirstVariation_fluxCurve_affine
        period hPeriod frame fields first second mu epsilon]
  have h := (hasDerivAt_id (0 : Real)).mul_const
    (globalDifferentialLLFluxHessian period hPeriod
      frame fields first second mu) |>.const_add
        (globalDifferentialLLFluxFirstVariation period hPeriod
          frame fields second mu)
  exact h.congr_deriv (one_mul _)

theorem throatDerivativePairing_comm
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    throatDerivativePairing period hPeriod frame first second point =
      throatDerivativePairing period hPeriod frame second first point := by
  unfold throatDerivativePairing
  apply Finset.sum_congr rfl
  intro index _
  exact real_inner_comm _ _

theorem throatDerivativePairing_self_eq_energy
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    throatDerivativePairing period hPeriod frame direction direction point =
      throatDerivativeEnergy period hPeriod frame direction point := by
  unfold throatDerivativePairing throatDerivativeEnergy
  apply Finset.sum_congr rfl
  intro index _
  exact real_inner_self_eq_norm_sq _

theorem differentialLLFluxHessianDensity_comm
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (point : EffectiveThroat period hPeriod) :
    differentialLLFluxHessianDensity period hPeriod
        frame fields first second point =
      differentialLLFluxHessianDensity period hPeriod
        frame fields second first point := by
  unfold differentialLLFluxHessianDensity
  rw [throatDerivativePairing_comm period hPeriod frame first second point,
    real_inner_comm (first point) (second point)]

theorem globalDifferentialLLFluxHessian_comm
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    globalDifferentialLLFluxHessian period hPeriod
        frame fields first second mu =
      globalDifferentialLLFluxHessian period hPeriod
        frame fields second first mu := by
  unfold globalDifferentialLLFluxHessian
  apply integral_congr_ae
  exact Filter.Eventually.of_forall
    (differentialLLFluxHessianDensity_comm period hPeriod
      frame fields first second)

/-- Hessian of the unchanged PT-averaged action. -/
def globalPTSymmetricDifferentialLLFluxHessian
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  (1 / 2 : Real) *
    (globalDifferentialLLFluxHessian period hPeriod
        frame fields first second mu +
      globalDifferentialLLFluxHessian period hPeriod frame
        (llPTPullback period hPeriod fields)
        (differentialLLFluxDirectionPT period hPeriod first)
        (differentialLLFluxDirectionPT period hPeriod second) mu)

/-- Exact affine linearization of the PT-averaged weak Euler pairing. -/
theorem globalPTSymmetricDifferentialLLFluxFirstVariation_fluxCurve_affine
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (epsilon : Real) :
    globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
        (differentialLLFluxCurve period hPeriod fields first epsilon)
        second mu =
      globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
          frame fields second mu +
        epsilon * globalPTSymmetricDifferentialLLFluxHessian period hPeriod
          frame fields first second mu := by
  unfold globalPTSymmetricDifferentialLLFluxFirstVariation
  rw [llPTPullback_differentialLLFluxCurve period hPeriod
    fields first epsilon]
  rw [globalDifferentialLLFluxFirstVariation_fluxCurve_affine period hPeriod
    frame fields first second mu epsilon]
  rw [globalDifferentialLLFluxFirstVariation_fluxCurve_affine period hPeriod
    frame (llPTPullback period hPeriod fields)
    (differentialLLFluxDirectionPT period hPeriod first)
    (differentialLLFluxDirectionPT period hPeriod second) mu epsilon]
  unfold globalPTSymmetricDifferentialLLFluxHessian
  ring

/-- The displayed symmetric bilinear functional is exactly the mixed second
derivative of the PT-averaged action, equivalently the derivative of its weak
Euler pairing. -/
theorem globalPTSymmetricDifferentialLLFluxFirstVariation_fluxCurve_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      (fun epsilon : Real =>
        globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
          (differentialLLFluxCurve period hPeriod fields first epsilon)
          second mu)
      (globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        frame fields first second mu) 0 := by
  rw [show (fun epsilon : Real =>
      globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame
        (differentialLLFluxCurve period hPeriod fields first epsilon)
        second mu) =
      (fun epsilon : Real =>
        globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
            frame fields second mu +
          epsilon * globalPTSymmetricDifferentialLLFluxHessian period hPeriod
            frame fields first second mu) from by
      funext epsilon
      exact globalPTSymmetricDifferentialLLFluxFirstVariation_fluxCurve_affine
        period hPeriod frame fields first second mu epsilon]
  have h := (hasDerivAt_id (0 : Real)).mul_const
    (globalPTSymmetricDifferentialLLFluxHessian period hPeriod
      frame fields first second mu) |>.const_add
        (globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
          frame fields second mu)
  exact h.congr_deriv (one_mul _)

theorem globalPTSymmetricDifferentialLLFluxHessian_comm
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        frame fields first second mu =
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        frame fields second first mu := by
  unfold globalPTSymmetricDifferentialLLFluxHessian
  rw [globalDifferentialLLFluxHessian_comm period hPeriod
      frame fields first second mu,
    globalDifferentialLLFluxHessian_comm period hPeriod frame
      (llPTPullback period hPeriod fields)
      (differentialLLFluxDirectionPT period hPeriod first)
      (differentialLLFluxDirectionPT period hPeriod second) mu]

theorem globalPTSymmetricDifferentialLLFluxHessian_pt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    globalPTSymmetricDifferentialLLFluxHessian period hPeriod frame
        (llPTPullback period hPeriod fields)
        (differentialLLFluxDirectionPT period hPeriod first)
        (differentialLLFluxDirectionPT period hPeriod second) mu =
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        frame fields first second mu := by
  unfold globalPTSymmetricDifferentialLLFluxHessian
  rw [llPTPullback_involutive,
    differentialLLFluxDirectionPT_involutive,
    differentialLLFluxDirectionPT_involutive]
  ring

/-- Kinetic portion of the raw Hessian, before the possibly indefinite
`llMeasure` zeroth-order term. -/
def globalDifferentialLLFluxKineticHessian
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ point,
    llAuxiliaryKineticWeight period hPeriod fields point *
      throatDerivativePairing period hPeriod frame first second point ∂mu

def globalPTSymmetricDifferentialLLFluxKineticHessian
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  (1 / 2 : Real) *
    (globalDifferentialLLFluxKineticHessian period hPeriod
        frame fields first second mu +
      globalDifferentialLLFluxKineticHessian period hPeriod frame
        (llPTPullback period hPeriod fields)
        (differentialLLFluxDirectionPT period hPeriod first)
        (differentialLLFluxDirectionPT period hPeriod second) mu)

theorem globalDifferentialLLFluxKineticHessian_self_nonneg
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    0 ≤ globalDifferentialLLFluxKineticHessian period hPeriod
      frame fields direction direction mu := by
  unfold globalDifferentialLLFluxKineticHessian
  apply integral_nonneg
  intro point
  change 0 ≤ llAuxiliaryKineticWeight period hPeriod fields point *
    throatDerivativePairing period hPeriod frame direction direction point
  rw [throatDerivativePairing_self_eq_energy period hPeriod
    frame direction point]
  apply mul_nonneg
  · exact (llAuxiliaryKineticWeight_pos period hPeriod fields point).le
  · unfold throatDerivativeEnergy
    exact Finset.sum_nonneg fun index _ => sq_nonneg _

/-- Positivity of the complete PT-averaged kinetic Hessian. -/
theorem globalPTSymmetricDifferentialLLFluxKineticHessian_self_nonneg
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLFieldFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    0 ≤ globalPTSymmetricDifferentialLLFluxKineticHessian period hPeriod
      frame fields direction direction mu := by
  unfold globalPTSymmetricDifferentialLLFluxKineticHessian
  exact mul_nonneg (by norm_num)
    (add_nonneg
      (globalDifferentialLLFluxKineticHessian_self_nonneg period hPeriod
        frame fields direction mu)
      (globalDifferentialLLFluxKineticHessian_self_nonneg period hPeriod frame
        (llPTPullback period hPeriod fields)
        (differentialLLFluxDirectionPT period hPeriod direction) mu))

/-- Pointwise auxiliary-metric Hessian of the same differential action. -/
def differentialLLAuxMetricHessianDensity
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLMetricFiber)
    (point : EffectiveThroat period hPeriod) : Real :=
  inner Real (first point) (second point) *
    throatDerivativeEnergy period hPeriod frame fields.llField point

theorem differentialLLAuxMetricFirstVariationDensity_auxCurve_affine
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLMetricFiber)
    (epsilon : Real) (point : EffectiveThroat period hPeriod) :
    differentialLLAuxMetricFirstVariationDensity period hPeriod frame
        (differentialLLAuxMetricCurve period hPeriod fields first epsilon)
        second point =
      differentialLLAuxMetricFirstVariationDensity period hPeriod
          frame fields second point +
        epsilon * differentialLLAuxMetricHessianDensity period hPeriod
          frame fields first second point := by
  have hAuxCurve :
      (fields.llAuxMetric + epsilon • first) point =
        fields.llAuxMetric point + epsilon • first point :=
    rfl
  unfold differentialLLAuxMetricFirstVariationDensity
    differentialLLAuxMetricCurve differentialLLAuxMetricHessianDensity
  change
    inner Real ((fields.llAuxMetric + epsilon • first) point) (second point) *
        throatDerivativeEnergy period hPeriod frame fields.llField point = _
  rw [hAuxCurve, inner_add_left, real_inner_smul_left]
  ring

theorem differentialLLAuxMetricHessianDensity_continuous
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLMetricFiber) :
    Continuous (differentialLLAuxMetricHessianDensity period hPeriod
      frame fields first second) := by
  exact
    (first.contMDiff_toFun.continuous.inner
      second.contMDiff_toFun.continuous).mul
      (throatDerivativeEnergy_continuous period hPeriod frame fields.llField)

def globalDifferentialLLAuxMetricHessian
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLMetricFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) : Real :=
  ∫ point, differentialLLAuxMetricHessianDensity period hPeriod
    frame fields first second point ∂mu

theorem globalDifferentialLLAuxMetricFirstVariation_auxCurve_affine
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLMetricFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (epsilon : Real) :
    globalDifferentialLLAuxMetricFirstVariation period hPeriod frame
        (differentialLLAuxMetricCurve period hPeriod fields first epsilon)
        second mu =
      globalDifferentialLLAuxMetricFirstVariation period hPeriod
          frame fields second mu +
        epsilon * globalDifferentialLLAuxMetricHessian period hPeriod
          frame fields first second mu := by
  have hFirst := continuous_real_integrable period hPeriod
    (differentialLLAuxMetricFirstVariationDensity period hPeriod
      frame fields second)
    (differentialLLAuxMetricFirstVariationDensity_continuous period hPeriod
      frame fields second) mu
  have hHessian := continuous_real_integrable period hPeriod
    (differentialLLAuxMetricHessianDensity period hPeriod
      frame fields first second)
    (differentialLLAuxMetricHessianDensity_continuous period hPeriod
      frame fields first second) mu
  unfold globalDifferentialLLAuxMetricFirstVariation
    globalDifferentialLLAuxMetricHessian
  simp_rw [differentialLLAuxMetricFirstVariationDensity_auxCurve_affine
    period hPeriod frame fields first second epsilon]
  calc
    (∫ point,
        differentialLLAuxMetricFirstVariationDensity period hPeriod
            frame fields second point +
          epsilon * differentialLLAuxMetricHessianDensity period hPeriod
            frame fields first second point ∂mu) =
        (∫ point, differentialLLAuxMetricFirstVariationDensity period hPeriod
          frame fields second point ∂mu) +
          ∫ point, epsilon *
            differentialLLAuxMetricHessianDensity period hPeriod
              frame fields first second point ∂mu := by
      simpa only [Pi.add_apply] using
        integral_add hFirst (hHessian.const_mul epsilon)
    _ = _ := by
      simp only [integral_const_mul]

theorem globalDifferentialLLAuxMetricFirstVariation_auxCurve_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLMetricFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      (fun epsilon : Real =>
        globalDifferentialLLAuxMetricFirstVariation period hPeriod frame
          (differentialLLAuxMetricCurve period hPeriod fields first epsilon)
          second mu)
      (globalDifferentialLLAuxMetricHessian period hPeriod
        frame fields first second mu) 0 := by
  rw [show (fun epsilon : Real =>
      globalDifferentialLLAuxMetricFirstVariation period hPeriod frame
        (differentialLLAuxMetricCurve period hPeriod fields first epsilon)
        second mu) =
      (fun epsilon : Real =>
        globalDifferentialLLAuxMetricFirstVariation period hPeriod
            frame fields second mu +
          epsilon * globalDifferentialLLAuxMetricHessian period hPeriod
            frame fields first second mu) from by
      funext epsilon
      exact globalDifferentialLLAuxMetricFirstVariation_auxCurve_affine
        period hPeriod frame fields first second mu epsilon]
  have h := (hasDerivAt_id (0 : Real)).mul_const
    (globalDifferentialLLAuxMetricHessian period hPeriod
      frame fields first second mu) |>.const_add
        (globalDifferentialLLAuxMetricFirstVariation period hPeriod
          frame fields second mu)
  exact h.congr_deriv (one_mul _)

theorem globalDifferentialLLAuxMetricHessian_comm
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : SmoothThroatField period hPeriod LLMetricFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    globalDifferentialLLAuxMetricHessian period hPeriod
        frame fields first second mu =
      globalDifferentialLLAuxMetricHessian period hPeriod
        frame fields second first mu := by
  unfold globalDifferentialLLAuxMetricHessian
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point => by
    unfold differentialLLAuxMetricHessianDensity
    rw [real_inner_comm (first point) (second point)]

theorem globalDifferentialLLAuxMetricHessian_self_nonneg
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : SmoothThroatField period hPeriod LLMetricFiber)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    0 ≤ globalDifferentialLLAuxMetricHessian period hPeriod
      frame fields direction direction mu := by
  unfold globalDifferentialLLAuxMetricHessian
  apply integral_nonneg
  intro point
  change 0 ≤ inner Real (direction point) (direction point) *
    throatDerivativeEnergy period hPeriod frame fields.llField point
  rw [real_inner_self_eq_norm_sq]
  apply mul_nonneg (sq_nonneg _)
  unfold throatDerivativeEnergy
  exact Finset.sum_nonneg fun index _ => sq_nonneg _

end

end P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D
end JanusFormal
