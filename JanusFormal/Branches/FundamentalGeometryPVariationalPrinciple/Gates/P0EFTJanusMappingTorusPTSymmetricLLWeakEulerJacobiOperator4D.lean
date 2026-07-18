import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D

/-!
# Weak Euler and Jacobi operators for the PT-symmetric LL action

The smooth throat-field space currently carries an algebraic real module but
no selected Banach topology.  Accordingly, the honest operator available here
is a genuine algebraic linear functional on smooth test fields, and its Jacobi
operator is a linear map into that algebraic dual.  Exact affine identities and
pointwise scalar `HasDerivAt` theorems replace an unjustified operator-valued
Fréchet derivative.

The weak Euler functional is exactly the first variation of the unchanged
PT-symmetrized differential LL action.  Its exact linearization is the
previously derived symmetric Hessian.  No nontrivial concrete gauge generator
on the LL flux field has yet been constructed, so no artificial zero map is
introduced to claim `J ∘ R = 0`; the `R/B` complex remains open.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D

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
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLHessian4D

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

abbrev LLWeakTestSpace :=
  SmoothThroatField period hPeriod LLFieldFiber

abbrev LLWeakTestDual :=
  LLWeakTestSpace period hPeriod →ₗ[Real] Real

theorem throatDerivativePairing_add_right
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (base first second : LLWeakTestSpace period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    throatDerivativePairing period hPeriod frame base (first + second) point =
      throatDerivativePairing period hPeriod frame base first point +
        throatDerivativePairing period hPeriod frame base second point := by
  have hDerivative (index : Fin frame.count) :
      throatFrameDerivative period hPeriod LLFieldFiber frame
          (first + second) point index =
        throatFrameDerivative period hPeriod LLFieldFiber frame first point index +
          throatFrameDerivative period hPeriod LLFieldFiber frame
            second point index := by
    rw [congrFun (congrFun
      (throatFrameDerivative_add period hPeriod LLFieldFiber frame
        first second) point) index]
    simp only [Pi.add_apply]
  unfold throatDerivativePairing
  simp_rw [hDerivative, inner_add_right, Finset.sum_add_distrib]

theorem throatDerivativePairing_smul_right
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (base direction : LLWeakTestSpace period hPeriod)
    (scalar : Real) (point : EffectiveThroat period hPeriod) :
    throatDerivativePairing period hPeriod frame
        base (scalar • direction) point =
      scalar * throatDerivativePairing period hPeriod frame
        base direction point := by
  have hDerivative (index : Fin frame.count) :
      throatFrameDerivative period hPeriod LLFieldFiber frame
          (scalar • direction) point index =
        scalar • throatFrameDerivative period hPeriod LLFieldFiber frame
          direction point index := by
    rw [congrFun (congrFun
      (throatFrameDerivative_smul period hPeriod LLFieldFiber frame
        scalar direction) point) index]
    simp only [Pi.smul_apply]
  unfold throatDerivativePairing
  simp_rw [hDerivative, real_inner_smul_right, ← Finset.mul_sum]

theorem differentialLLFluxFirstVariationDensity_add_test
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : LLWeakTestSpace period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    differentialLLFluxFirstVariationDensity period hPeriod frame fields
        (first + second) point =
      differentialLLFluxFirstVariationDensity period hPeriod frame fields
          first point +
        differentialLLFluxFirstVariationDensity period hPeriod frame fields
          second point := by
  unfold differentialLLFluxFirstVariationDensity
  rw [throatDerivativePairing_add_right period hPeriod frame
    fields.llField first second point]
  change _ + 2 * fields.llMeasure point *
    inner Real (fields.llField point) (first point + second point) = _
  rw [inner_add_right]
  ring

theorem differentialLLFluxFirstVariationDensity_smul_test
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (scalar : Real) (direction : LLWeakTestSpace period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    differentialLLFluxFirstVariationDensity period hPeriod frame fields
        (scalar • direction) point =
      scalar * differentialLLFluxFirstVariationDensity period hPeriod
        frame fields direction point := by
  unfold differentialLLFluxFirstVariationDensity
  rw [throatDerivativePairing_smul_right period hPeriod frame
    fields.llField direction scalar point]
  change _ + 2 * fields.llMeasure point *
    inner Real (fields.llField point) (scalar • direction point) = _
  rw [real_inner_smul_right]
  ring

private theorem continuous_real_integrable
    (function : EffectiveThroat period hPeriod → Real)
    (hContinuous : Continuous function)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    Integrable function mu :=
  hContinuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace function)

theorem globalDifferentialLLFluxFirstVariation_add_test
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : LLWeakTestSpace period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalDifferentialLLFluxFirstVariation period hPeriod frame fields
        (first + second) mu =
      globalDifferentialLLFluxFirstVariation period hPeriod frame fields first mu +
        globalDifferentialLLFluxFirstVariation period hPeriod
          frame fields second mu := by
  have hFirst := continuous_real_integrable period hPeriod
    (differentialLLFluxFirstVariationDensity period hPeriod frame fields first)
    (differentialLLFluxFirstVariationDensity_continuous period hPeriod
      frame fields first) mu
  have hSecond := continuous_real_integrable period hPeriod
    (differentialLLFluxFirstVariationDensity period hPeriod frame fields second)
    (differentialLLFluxFirstVariationDensity_continuous period hPeriod
      frame fields second) mu
  unfold globalDifferentialLLFluxFirstVariation
  simp_rw [differentialLLFluxFirstVariationDensity_add_test period hPeriod
    frame fields first second]
  exact integral_add hFirst hSecond

theorem globalDifferentialLLFluxFirstVariation_smul_test
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (scalar : Real) (direction : LLWeakTestSpace period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    globalDifferentialLLFluxFirstVariation period hPeriod frame fields
        (scalar • direction) mu =
      scalar * globalDifferentialLLFluxFirstVariation period hPeriod
        frame fields direction mu := by
  unfold globalDifferentialLLFluxFirstVariation
  simp_rw [differentialLLFluxFirstVariationDensity_smul_test period hPeriod
    frame fields scalar direction]
  simp only [integral_const_mul]

theorem differentialLLFluxDirectionPT_add
    (first second : LLWeakTestSpace period hPeriod) :
    differentialLLFluxDirectionPT period hPeriod (first + second) =
      differentialLLFluxDirectionPT period hPeriod first +
        differentialLLFluxDirectionPT period hPeriod second := by
  apply SmoothThroatField.ext period hPeriod LLFieldFiber
  intro point
  rfl

theorem differentialLLFluxDirectionPT_smul
    (scalar : Real) (direction : LLWeakTestSpace period hPeriod) :
    differentialLLFluxDirectionPT period hPeriod (scalar • direction) =
      scalar • differentialLLFluxDirectionPT period hPeriod direction := by
  apply SmoothThroatField.ext period hPeriod LLFieldFiber
  intro point
  rfl

theorem globalPTSymmetricDifferentialLLFluxFirstVariation_add_test
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : LLWeakTestSpace period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame fields
        (first + second) mu =
      globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
          frame fields first mu +
        globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
          frame fields second mu := by
  unfold globalPTSymmetricDifferentialLLFluxFirstVariation
  rw [differentialLLFluxDirectionPT_add]
  rw [globalDifferentialLLFluxFirstVariation_add_test period hPeriod
    frame fields first second mu]
  rw [globalDifferentialLLFluxFirstVariation_add_test period hPeriod frame
    (llPTPullback period hPeriod fields)
    (differentialLLFluxDirectionPT period hPeriod first)
    (differentialLLFluxDirectionPT period hPeriod second) mu]
  ring

theorem globalPTSymmetricDifferentialLLFluxFirstVariation_smul_test
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (scalar : Real) (direction : LLWeakTestSpace period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) :
    globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod frame fields
        (scalar • direction) mu =
      scalar * globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
        frame fields direction mu := by
  unfold globalPTSymmetricDifferentialLLFluxFirstVariation
  rw [differentialLLFluxDirectionPT_smul]
  rw [globalDifferentialLLFluxFirstVariation_smul_test period hPeriod
    frame fields scalar direction mu]
  rw [globalDifferentialLLFluxFirstVariation_smul_test period hPeriod frame
    (llPTPullback period hPeriod fields) scalar
    (differentialLLFluxDirectionPT period hPeriod direction) mu]
  ring

/-- The true weak Euler operator as a linear functional on smooth tests. -/
def weakLLEulerOperator
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    LLWeakTestDual period hPeriod where
  toFun direction :=
    globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
      frame fields direction mu
  map_add' first second :=
    globalPTSymmetricDifferentialLLFluxFirstVariation_add_test period hPeriod
      frame fields first second mu
  map_smul' scalar direction :=
    globalPTSymmetricDifferentialLLFluxFirstVariation_smul_test period hPeriod
      frame fields scalar direction mu

@[simp]
theorem weakLLEulerOperator_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (direction : LLWeakTestSpace period hPeriod) :
    weakLLEulerOperator period hPeriod frame fields mu direction =
      globalPTSymmetricDifferentialLLFluxFirstVariation period hPeriod
        frame fields direction mu :=
  rfl

theorem globalPTSymmetricDifferentialLLFluxHessian_eq_euler_difference
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : LLWeakTestSpace period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        frame fields first second mu =
      weakLLEulerOperator period hPeriod frame
          (differentialLLFluxCurve period hPeriod fields first 1) mu second -
        weakLLEulerOperator period hPeriod frame fields mu second := by
  have h :=
    globalPTSymmetricDifferentialLLFluxFirstVariation_fluxCurve_affine
      period hPeriod frame fields first second mu 1
  rw [weakLLEulerOperator_apply, weakLLEulerOperator_apply]
  simp only [one_mul] at h
  linarith

theorem globalPTSymmetricDifferentialLLFluxHessian_add_right
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second third : LLWeakTestSpace period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        frame fields first (second + third) mu =
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
          frame fields first second mu +
        globalPTSymmetricDifferentialLLFluxHessian period hPeriod
          frame fields first third mu := by
  rw [globalPTSymmetricDifferentialLLFluxHessian_eq_euler_difference
      period hPeriod frame fields first (second + third) mu,
    globalPTSymmetricDifferentialLLFluxHessian_eq_euler_difference
      period hPeriod frame fields first second mu,
    globalPTSymmetricDifferentialLLFluxHessian_eq_euler_difference
      period hPeriod frame fields first third mu]
  simp only [map_add]
  ring

theorem globalPTSymmetricDifferentialLLFluxHessian_smul_right
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : LLWeakTestSpace period hPeriod)
    (scalar : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        frame fields first (scalar • second) mu =
      scalar * globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        frame fields first second mu := by
  rw [globalPTSymmetricDifferentialLLFluxHessian_eq_euler_difference
      period hPeriod frame fields first (scalar • second) mu,
    globalPTSymmetricDifferentialLLFluxHessian_eq_euler_difference
      period hPeriod frame fields first second mu]
  simp only [map_smul]
  ring

theorem globalPTSymmetricDifferentialLLFluxHessian_add_left
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second third : LLWeakTestSpace period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        frame fields (first + second) third mu =
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
          frame fields first third mu +
        globalPTSymmetricDifferentialLLFluxHessian period hPeriod
          frame fields second third mu := by
  rw [globalPTSymmetricDifferentialLLFluxHessian_comm period hPeriod
      frame fields (first + second) third mu,
    globalPTSymmetricDifferentialLLFluxHessian_add_right period hPeriod
      frame fields third first second mu,
    globalPTSymmetricDifferentialLLFluxHessian_comm period hPeriod
      frame fields third first mu,
    globalPTSymmetricDifferentialLLFluxHessian_comm period hPeriod
      frame fields third second mu]

theorem globalPTSymmetricDifferentialLLFluxHessian_smul_left
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : LLWeakTestSpace period hPeriod)
    (scalar : Real)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        frame fields (scalar • first) second mu =
      scalar * globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        frame fields first second mu := by
  rw [globalPTSymmetricDifferentialLLFluxHessian_comm period hPeriod
      frame fields (scalar • first) second mu,
    globalPTSymmetricDifferentialLLFluxHessian_smul_right period hPeriod
      frame fields second first scalar mu,
    globalPTSymmetricDifferentialLLFluxHessian_comm period hPeriod
      frame fields second first mu]

/-- The weak Jacobi operator, bundled as a linear map into the algebraic dual. -/
def weakLLJacobiOperator
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    LLWeakTestSpace period hPeriod →ₗ[Real] LLWeakTestDual period hPeriod where
  toFun first :=
    { toFun := fun second =>
        globalPTSymmetricDifferentialLLFluxHessian period hPeriod
          frame fields first second mu
      map_add' := fun second third =>
        globalPTSymmetricDifferentialLLFluxHessian_add_right period hPeriod
          frame fields first second third mu
      map_smul' := fun scalar second =>
        globalPTSymmetricDifferentialLLFluxHessian_smul_right period hPeriod
          frame fields first second scalar mu }
  map_add' first second := by
    ext third
    exact globalPTSymmetricDifferentialLLFluxHessian_add_left period hPeriod
      frame fields first second third mu
  map_smul' scalar first := by
    ext second
    exact globalPTSymmetricDifferentialLLFluxHessian_smul_left period hPeriod
      frame fields first second scalar mu

@[simp]
theorem weakLLJacobiOperator_apply
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (first second : LLWeakTestSpace period hPeriod) :
    weakLLJacobiOperator period hPeriod frame fields mu first second =
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        frame fields first second mu :=
  rfl

/-- Exact operator-valued affine linearization of the weak Euler operator. -/
theorem weakLLEulerOperator_fluxCurve_affine
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : LLWeakTestSpace period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (epsilon : Real) :
    weakLLEulerOperator period hPeriod frame
        (differentialLLFluxCurve period hPeriod fields direction epsilon) mu =
      weakLLEulerOperator period hPeriod frame fields mu +
        epsilon • weakLLJacobiOperator period hPeriod frame fields mu direction := by
  ext test
  exact globalPTSymmetricDifferentialLLFluxFirstVariation_fluxCurve_affine
    period hPeriod frame fields direction test mu epsilon

/-- Pointwise scalar derivative of `K`: this is the honest derivative statement
available before choosing a topology on the algebraic dual. -/
theorem weakLLEulerOperator_fluxCurve_hasDerivAt
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction test : LLWeakTestSpace period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      (fun epsilon : Real =>
        weakLLEulerOperator period hPeriod frame
          (differentialLLFluxCurve period hPeriod fields direction epsilon)
          mu test)
      (weakLLJacobiOperator period hPeriod frame fields mu direction test) 0 := by
  exact globalPTSymmetricDifferentialLLFluxFirstVariation_fluxCurve_hasDerivAt
    period hPeriod frame fields direction test mu

theorem weakLLJacobiOperator_symmetric
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (first second : LLWeakTestSpace period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    weakLLJacobiOperator period hPeriod frame fields mu first second =
      weakLLJacobiOperator period hPeriod frame fields mu second first :=
  globalPTSymmetricDifferentialLLFluxHessian_comm period hPeriod
    frame fields first second mu

/-- `K` is exactly the first derivative of the unchanged PT-symmetric action. -/
theorem globalPTSymmetricDifferentialLLAction_fluxCurve_hasDerivAt_weakEuler
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : LLWeakTestSpace period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu] :
    HasDerivAt
      (fun epsilon : Real =>
        globalPTSymmetricDifferentialLLAction period hPeriod frame
          (differentialLLFluxCurve period hPeriod fields direction epsilon) mu)
      (weakLLEulerOperator period hPeriod frame fields mu direction) 0 := by
  exact globalPTSymmetricDifferentialLLAction_fluxCurve_hasDerivAt
    period hPeriod frame fields direction mu

end

end P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D
end JanusFormal
