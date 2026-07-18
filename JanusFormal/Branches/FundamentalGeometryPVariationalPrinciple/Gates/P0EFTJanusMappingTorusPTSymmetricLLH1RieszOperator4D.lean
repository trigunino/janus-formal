import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Measure.OpenPos
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D

/-!
# H1--Riesz realization of the PT-symmetric differential LL operator

The current throat data provide a compact smooth manifold, a finite smooth
generating family and a finite measure, but no volume form, divergence or
formal-adjoint/Stokes theorem.  Thus a pointwise second-order formula cannot be
derived honestly yet.  This gate instead constructs the canonical energy-space
realization of the already proved weak Hessian in the positive `llMeasure`
sector.  Positivity is derived from the density and open-positive measure; it
is not an adjoint or coercivity hypothesis.  No equivalence with an externally
defined Sobolev norm, no coercive estimate against such a norm, and no
unbounded `L2` strong realization are claimed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Topology
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
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
open P0EFTJanusMappingTorusPTSymmetricLLWeakEulerJacobiOperator4D

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

theorem differentialLLFluxHessianDensity_self_nonneg
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : LLWeakTestSpace period hPeriod)
    (hMeasure : ∀ point, 0 ≤ fields.llMeasure point)
    (point : EffectiveThroat period hPeriod) :
    0 ≤ differentialLLFluxHessianDensity period hPeriod
      frame fields direction direction point := by
  unfold differentialLLFluxHessianDensity
  rw [throatDerivativePairing_self_eq_energy period hPeriod
    frame direction point, real_inner_self_eq_norm_sq]
  apply add_nonneg
  · apply mul_nonneg
    · exact (llAuxiliaryKineticWeight_pos period hPeriod fields point).le
    · unfold throatDerivativeEnergy
      exact Finset.sum_nonneg fun index _ => sq_nonneg _
  · exact mul_nonneg (mul_nonneg (by norm_num) (hMeasure point))
      (sq_nonneg ‖direction point‖)

theorem globalDifferentialLLFluxHessian_self_nonneg_of_measure
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : LLWeakTestSpace period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    (hMeasure : ∀ point, 0 ≤ fields.llMeasure point) :
    0 ≤ globalDifferentialLLFluxHessian period hPeriod
      frame fields direction direction mu := by
  unfold globalDifferentialLLFluxHessian
  exact integral_nonneg fun point =>
    differentialLLFluxHessianDensity_self_nonneg period hPeriod
      frame fields direction hMeasure point

theorem globalDifferentialLLFluxHessian_self_pos_of_measure
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : LLWeakTestSpace period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure mu] [Measure.IsOpenPosMeasure mu]
    (hMeasure : ∀ point, 0 < fields.llMeasure point)
    (hDirection : direction ≠ 0) :
    0 < globalDifferentialLLFluxHessian period hPeriod
      frame fields direction direction mu := by
  have hExists : ∃ point, direction point ≠ 0 := by
    by_contra h
    apply hDirection
    apply SmoothThroatField.ext period hPeriod LLFieldFiber
    intro point
    by_contra hPoint
    exact h ⟨point, hPoint⟩
  rcases hExists with ⟨point, hPoint⟩
  have hDensityNonneg :
      0 ≤ differentialLLFluxHessianDensity period hPeriod
        frame fields direction direction :=
    differentialLLFluxHessianDensity_self_nonneg period hPeriod
      frame fields direction (fun point => (hMeasure point).le)
  have hDensityPoint :
      differentialLLFluxHessianDensity period hPeriod
          frame fields direction direction point ≠ 0 := by
    have hNorm : 0 < ‖direction point‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr hPoint)
    unfold differentialLLFluxHessianDensity
    rw [throatDerivativePairing_self_eq_energy period hPeriod
      frame direction point, real_inner_self_eq_norm_sq]
    have hKinetic : 0 ≤ llAuxiliaryKineticWeight period hPeriod fields point *
        throatDerivativeEnergy period hPeriod frame direction point := by
      apply mul_nonneg
      · exact (llAuxiliaryKineticWeight_pos period hPeriod fields point).le
      · unfold throatDerivativeEnergy
        exact Finset.sum_nonneg fun index _ => sq_nonneg _
    have hMass : 0 < 2 * fields.llMeasure point * ‖direction point‖ ^ 2 :=
      mul_pos (mul_pos (by norm_num) (hMeasure point)) hNorm
    linarith
  unfold globalDifferentialLLFluxHessian
  exact integral_pos_of_integrable_nonneg_nonzero
    (differentialLLFluxHessianDensity_continuous period hPeriod
      frame fields direction direction)
    ((differentialLLFluxHessianDensity_continuous period hPeriod
      frame fields direction direction).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _))
    hDensityNonneg hDensityPoint

theorem globalPTSymmetricDifferentialLLFluxHessian_self_pos_of_measure
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (direction : LLWeakTestSpace period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod))
    [IsFiniteMeasure mu] [Measure.IsOpenPosMeasure mu]
    (hMeasure : ∀ point, 0 < fields.llMeasure point)
    (hDirection : direction ≠ 0) :
    0 < globalPTSymmetricDifferentialLLFluxHessian period hPeriod
      frame fields direction direction mu := by
  have hFirst := globalDifferentialLLFluxHessian_self_pos_of_measure
    period hPeriod frame fields direction mu hMeasure hDirection
  have hPTMeasure : ∀ point,
      0 ≤ (llPTPullback period hPeriod fields).llMeasure point := by
    intro point
    change 0 ≤ fields.llMeasure (fixedThroatPT period hPeriod point)
    exact (hMeasure _).le
  have hSecond := globalDifferentialLLFluxHessian_self_nonneg_of_measure
    period hPeriod frame (llPTPullback period hPeriod fields)
    (differentialLLFluxDirectionPT period hPeriod direction) mu hPTMeasure
  unfold globalPTSymmetricDifferentialLLFluxHessian
  nlinarith

/-- The PT Euler operator is the Jacobi form evaluated on the current LL
field; the differential LL action has no independent flux source term. -/
theorem weakLLEulerOperator_eq_jacobi_llField
    (frame : SmoothThroatGeneratingFrame period hPeriod)
    (fields : IndependentFields period hPeriod)
    (mu : Measure (EffectiveThroat period hPeriod)) [IsFiniteMeasure mu]
    (test : LLWeakTestSpace period hPeriod) :
    weakLLEulerOperator period hPeriod frame fields mu test =
      weakLLJacobiOperator period hPeriod frame fields mu
        fields.llField test := by
  rfl

/-- Data sufficient to turn the selected PT Jacobi form into a genuine
positive energy inner product.  Open positivity belongs to the measure, while
strict positivity is required only of the independent zeroth-order LL field. -/
structure PositiveLLH1Data where
  fields : IndependentFields period hPeriod
  mu : Measure (EffectiveThroat period hPeriod)
  finiteMeasure : IsFiniteMeasure mu
  openPosMeasure : Measure.IsOpenPosMeasure mu
  llMeasure_pos : ∀ point, 0 < fields.llMeasure point

/-- A tagged copy of smooth LL tests.  The tag keeps the energy norm attached
to its coefficients and measure. -/
structure LLH1Smooth (_data : PositiveLLH1Data period hPeriod) where
  toTest : LLWeakTestSpace period hPeriod

@[ext]
theorem LLH1Smooth.ext
    {data : PositiveLLH1Data period hPeriod}
    {first second : LLH1Smooth period hPeriod data}
    (h : first.toTest = second.toTest) : first = second := by
  cases first
  cases second
  congr

instance (data : PositiveLLH1Data period hPeriod) :
    Zero (LLH1Smooth period hPeriod data) := ⟨⟨0⟩⟩

instance (data : PositiveLLH1Data period hPeriod) :
    Add (LLH1Smooth period hPeriod data) :=
  ⟨fun first second => ⟨first.toTest + second.toTest⟩⟩

instance (data : PositiveLLH1Data period hPeriod) :
    Neg (LLH1Smooth period hPeriod data) :=
  ⟨fun field => ⟨-field.toTest⟩⟩

instance (data : PositiveLLH1Data period hPeriod) :
    Sub (LLH1Smooth period hPeriod data) :=
  ⟨fun first second => ⟨first.toTest - second.toTest⟩⟩

instance (data : PositiveLLH1Data period hPeriod) :
    AddCommGroup (LLH1Smooth period hPeriod data) where
  add_assoc first second third := by
    apply LLH1Smooth.ext
    exact add_assoc _ _ _
  zero_add field := by
    apply LLH1Smooth.ext
    exact zero_add _
  add_zero field := by
    apply LLH1Smooth.ext
    exact add_zero _
  nsmul := nsmulRec
  add_comm first second := by
    apply LLH1Smooth.ext
    exact add_comm _ _
  neg_add_cancel field := by
    apply LLH1Smooth.ext
    exact neg_add_cancel _
  sub_eq_add_neg first second := by
    apply LLH1Smooth.ext
    exact sub_eq_add_neg _ _
  zsmul := zsmulRec

instance (data : PositiveLLH1Data period hPeriod) :
    SMul Real (LLH1Smooth period hPeriod data) :=
  ⟨fun scalar field => ⟨scalar • field.toTest⟩⟩

instance (data : PositiveLLH1Data period hPeriod) :
    Module Real (LLH1Smooth period hPeriod data) where
  one_smul field := by
    apply LLH1Smooth.ext
    exact one_smul Real field.toTest
  mul_smul first second field := by
    apply LLH1Smooth.ext
    exact mul_smul first second field.toTest
  smul_add scalar first second := by
    apply LLH1Smooth.ext
    exact smul_add scalar first.toTest second.toTest
  smul_zero scalar := by
    apply LLH1Smooth.ext
    exact smul_zero scalar
  add_smul first second field := by
    apply LLH1Smooth.ext
    exact add_smul first second field.toTest
  zero_smul field := by
    apply LLH1Smooth.ext
    exact zero_smul Real field.toTest

def LLH1Smooth.ofTest
    (data : PositiveLLH1Data period hPeriod)
    (test : LLWeakTestSpace period hPeriod) :
    LLH1Smooth period hPeriod data :=
  ⟨test⟩

@[simp]
theorem LLH1Smooth.toTest_zero
    (data : PositiveLLH1Data period hPeriod) :
    (0 : LLH1Smooth period hPeriod data).toTest = 0 :=
  rfl

@[simp]
theorem LLH1Smooth.toTest_add
    {data : PositiveLLH1Data period hPeriod}
    (first second : LLH1Smooth period hPeriod data) :
    (first + second).toTest = first.toTest + second.toTest :=
  rfl

@[simp]
theorem LLH1Smooth.toTest_smul
    {data : PositiveLLH1Data period hPeriod}
    (scalar : Real) (field : LLH1Smooth period hPeriod data) :
    (scalar • field).toTest = scalar • field.toTest :=
  rfl

@[implicit_reducible]
noncomputable def llH1PreCore
    (data : PositiveLLH1Data period hPeriod) :
    PreInnerProductSpace.Core Real (LLH1Smooth period hPeriod data) := by
  letI : IsFiniteMeasure data.mu := data.finiteMeasure
  letI : Measure.IsOpenPosMeasure data.mu := data.openPosMeasure
  let frame := finiteSmoothThroatGeneratingFrame period hPeriod
  refine
    { inner := fun first second =>
        weakLLJacobiOperator period hPeriod frame data.fields data.mu
          first.toTest second.toTest
      conj_inner_symm := ?_
      re_inner_nonneg := ?_
      add_left := ?_
      smul_left := ?_ }
  · intro first second
    simpa using
      (weakLLJacobiOperator_symmetric period hPeriod frame data.fields
        second.toTest first.toTest data.mu)
  · intro direction
    change 0 ≤ globalPTSymmetricDifferentialLLFluxHessian period hPeriod
      frame data.fields direction.toTest direction.toTest data.mu
    by_cases hDirection : direction.toTest = 0
    · have hZero : direction = 0 := by
        apply LLH1Smooth.ext
        simpa using hDirection
      subst direction
      change 0 ≤ globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        frame data.fields (0 : LLWeakTestSpace period hPeriod) 0 data.mu
      rw [← weakLLJacobiOperator_apply period hPeriod frame data.fields
        data.mu (0 : LLWeakTestSpace period hPeriod) 0]
      simp
    · exact (globalPTSymmetricDifferentialLLFluxHessian_self_pos_of_measure
        period hPeriod frame data.fields direction.toTest data.mu
        data.llMeasure_pos hDirection).le
  · intro first second third
    exact congrArg (fun functional => functional third.toTest)
      ((weakLLJacobiOperator period hPeriod frame data.fields data.mu).map_add
        first.toTest second.toTest)
  · intro first second scalar
    exact congrArg (fun functional => functional second.toTest)
      ((weakLLJacobiOperator period hPeriod frame data.fields data.mu).map_smul
        scalar first.toTest)

@[implicit_reducible]
noncomputable def llH1Core
    (data : PositiveLLH1Data period hPeriod) :
    InnerProductSpace.Core Real (LLH1Smooth period hPeriod data) := by
  letI : IsFiniteMeasure data.mu := data.finiteMeasure
  letI : Measure.IsOpenPosMeasure data.mu := data.openPosMeasure
  let frame := finiteSmoothThroatGeneratingFrame period hPeriod
  refine
    { __ := llH1PreCore period hPeriod data
      definite := ?_ }
  intro direction hZero
  by_contra hDirection
  have hTest : direction.toTest ≠ 0 := by
    intro hTest
    apply hDirection
    apply LLH1Smooth.ext
    simpa using hTest
  have hPositive :=
    globalPTSymmetricDifferentialLLFluxHessian_self_pos_of_measure
      period hPeriod frame data.fields direction.toTest data.mu
      data.llMeasure_pos hTest
  change globalPTSymmetricDifferentialLLFluxHessian period hPeriod
    frame data.fields direction.toTest direction.toTest data.mu = 0 at hZero
  linarith

noncomputable instance llH1NormedAddCommGroup
    (data : PositiveLLH1Data period hPeriod) :
    NormedAddCommGroup (LLH1Smooth period hPeriod data) :=
  InnerProductSpace.Core.toNormedAddCommGroup
    (cd := llH1Core period hPeriod data)

noncomputable instance llH1InnerProductSpace
    (data : PositiveLLH1Data period hPeriod) :
    InnerProductSpace Real (LLH1Smooth period hPeriod data) :=
  InnerProductSpace.ofCore (llH1PreCore period hPeriod data)

@[simp]
theorem llH1Smooth_inner
    (data : PositiveLLH1Data period hPeriod)
    (first second : LLH1Smooth period hPeriod data) :
    inner Real first second =
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod)
        data.fields first.toTest second.toTest data.mu := by
  rfl

/-- Intrinsic Hilbert completion of the positive PT Jacobi energy space. -/
abbrev LLH1Space (data : PositiveLLH1Data period hPeriod) :=
  UniformSpace.Completion (LLH1Smooth period hPeriod data)

/-- The smooth form domain embedded isometrically in its Hilbert completion. -/
def llH1SmoothEmbedding
    (data : PositiveLLH1Data period hPeriod) :
    LLH1Smooth period hPeriod data →L[Real] LLH1Space period hPeriod data :=
  UniformSpace.Completion.toComplL

@[simp]
theorem llH1SmoothEmbedding_apply
    (data : PositiveLLH1Data period hPeriod)
    (direction : LLH1Smooth period hPeriod data) :
    llH1SmoothEmbedding period hPeriod data direction =
      (direction : LLH1Space period hPeriod data) :=
  rfl

/-- The strong form domain is dense; this is the actual completion density,
not a separately assumed analytic condition. -/
theorem llH1SmoothEmbedding_denseRange
    (data : PositiveLLH1Data period hPeriod) :
    DenseRange (llH1SmoothEmbedding period hPeriod data) := by
  change DenseRange
    ((↑) : LLH1Smooth period hPeriod data → LLH1Space period hPeriod data)
  exact UniformSpace.Completion.denseRange_coe

/-- Continuous weak Jacobi functional on the completed H1 energy space. -/
def weakLLJacobiH1Extension
    (data : PositiveLLH1Data period hPeriod)
    (direction : LLH1Smooth period hPeriod data) :
    LLH1Space period hPeriod data →L[Real] Real :=
  InnerProductSpace.toDualMap Real (LLH1Space period hPeriod data)
    (llH1SmoothEmbedding period hPeriod data direction)

@[simp]
theorem weakLLJacobiH1Extension_apply_smooth
    (data : PositiveLLH1Data period hPeriod)
    (direction test : LLH1Smooth period hPeriod data) :
    weakLLJacobiH1Extension period hPeriod data direction
        (llH1SmoothEmbedding period hPeriod data test) =
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) data.fields
        direction.toTest test.toTest data.mu := by
  change inner Real
    (direction : LLH1Space period hPeriod data)
    (test : LLH1Space period hPeriod data) = _
  rw [UniformSpace.Completion.inner_coe]
  exact llH1Smooth_inner period hPeriod data direction test

/-- Strong H1 Jacobi realization.  Since the H1 scalar product is the Jacobi
energy form, its Riesz representative is the dense-domain inclusion. -/
def strongLLJacobiH1Operator
    (data : PositiveLLH1Data period hPeriod) :
    LLH1Smooth period hPeriod data →L[Real] LLH1Space period hPeriod data :=
  llH1SmoothEmbedding period hPeriod data

theorem strongLLJacobiH1Operator_toDual
    (data : PositiveLLH1Data period hPeriod)
    (direction : LLH1Smooth period hPeriod data) :
    InnerProductSpace.toDual Real (LLH1Space period hPeriod data)
        (strongLLJacobiH1Operator period hPeriod data direction) =
      weakLLJacobiH1Extension period hPeriod data direction :=
  rfl

/-- The strong operator is obtained by the Frechet--Riesz inverse, rather than
by postulating a formal adjoint. -/
theorem strongLLJacobiH1Operator_eq_rieszInverse
    (data : PositiveLLH1Data period hPeriod)
    (direction : LLH1Smooth period hPeriod data) :
    strongLLJacobiH1Operator period hPeriod data direction =
      (InnerProductSpace.toDual Real (LLH1Space period hPeriod data)).symm
        (weakLLJacobiH1Extension period hPeriod data direction) := by
  rw [← strongLLJacobiH1Operator_toDual period hPeriod data direction]
  simp

/-- Full strong--weak equivalence against every completed H1 test. -/
theorem strongLLJacobiH1Operator_represents
    (data : PositiveLLH1Data period hPeriod)
    (direction : LLH1Smooth period hPeriod data)
    (test : LLH1Space period hPeriod data) :
    inner Real (strongLLJacobiH1Operator period hPeriod data direction) test =
      weakLLJacobiH1Extension period hPeriod data direction test := by
  rw [strongLLJacobiH1Operator_eq_rieszInverse]
  exact InnerProductSpace.toDual_symm_apply

/-- Explicit strong--weak equality on the original smooth throat tests. -/
theorem strongLLJacobiH1Operator_iff_weak_on_smooth
    (data : PositiveLLH1Data period hPeriod)
    (direction test : LLH1Smooth period hPeriod data) :
    inner Real (strongLLJacobiH1Operator period hPeriod data direction)
        (llH1SmoothEmbedding period hPeriod data test) =
      globalPTSymmetricDifferentialLLFluxHessian period hPeriod
        (finiteSmoothThroatGeneratingFrame period hPeriod) data.fields
        direction.toTest test.toTest data.mu := by
  rw [strongLLJacobiH1Operator_represents]
  exact weakLLJacobiH1Extension_apply_smooth period hPeriod data direction test

theorem strongLLJacobiH1Operator_denseDomain
    (data : PositiveLLH1Data period hPeriod) :
    DenseRange (strongLLJacobiH1Operator period hPeriod data) :=
  llH1SmoothEmbedding_denseRange period hPeriod data

theorem strongLLJacobiH1Operator_kernel
    (data : PositiveLLH1Data period hPeriod)
    (direction : LLH1Smooth period hPeriod data) :
    strongLLJacobiH1Operator period hPeriod data direction = 0 ↔
      direction = 0 := by
  change (direction : LLH1Space period hPeriod data) = 0 ↔ direction = 0
  rw [← UniformSpace.Completion.coe_zero]
  exact UniformSpace.Completion.coe_inj

/-- Vanishing against all smooth tests has no hidden distributional kernel in
the positive energy sector. -/
theorem weakLLJacobiH1Extension_vanishes_iff
    (data : PositiveLLH1Data period hPeriod)
    (direction : LLH1Smooth period hPeriod data) :
    (∀ test : LLH1Smooth period hPeriod data,
      weakLLJacobiH1Extension period hPeriod data direction
        (llH1SmoothEmbedding period hPeriod data test) = 0) ↔
      direction = 0 := by
  constructor
  · intro hWeak
    apply (inner_self_eq_zero (𝕜 := Real)).mp
    rw [llH1Smooth_inner period hPeriod data direction direction]
    simpa only [weakLLJacobiH1Extension_apply_smooth] using hWeak direction
  · intro hDirection
    subst direction
    intro test
    simp [weakLLJacobiH1Extension]

end

end P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
end JanusFormal
