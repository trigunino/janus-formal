import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.MeasureTheory.Measure.OpenPos
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAutomaticScalarIntegrability4D

/-!
# Weak Euler, Jacobi and positive-sector Riesz operators for the D8 scalar

The weak operators below are derived from the existing global holonomic scalar
action and its exact variation.  The full Lorentzian kinetic form is not used
as a Hilbert inner product: its time component has negative sign.  The energy
completion is therefore constructed only on the explicitly time-static sector,
with positive metric magnitudes, positive mass squared and an open-positive
finite measure.  No divergence, Stokes formula or pointwise strong PDE is
invented.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D

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
open P0EFTJanusMappingTorusAutomaticScalarIntegrability4D
open P0EFTJanusGlobalDiagonalLorentzRoot4D

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

abbrev GlobalScalarTestSpace :=
  SmoothQuotientField period hPeriod Real

theorem holonomicCovectorComponent_add
    (first second : GlobalScalarTestSpace period hPeriod)
    (point : EffectiveQuotient period hPeriod) (index : Fin 4) :
    holonomicCovectorComponent period hPeriod (first + second) point index =
      holonomicCovectorComponent period hPeriod first point index +
        holonomicCovectorComponent period hPeriod second point index := by
  simpa [scalarAffineCurve] using
    (holonomicCovectorComponent_affine period hPeriod first second 1 point index)

theorem holonomicCovectorComponent_smul
    (scalar : Real) (field : GlobalScalarTestSpace period hPeriod)
    (point : EffectiveQuotient period hPeriod) (index : Fin 4) :
    holonomicCovectorComponent period hPeriod (scalar • field) point index =
      scalar * holonomicCovectorComponent period hPeriod field point index := by
  unfold holonomicCovectorComponent scalarDifferential
  change mfderiv coverModelWithCorners 𝓘(Real, Real)
      (scalar • field.toFun) point
      (tangentCoordinate index) = _
  rw [const_smul_mfderiv
    (field.contMDiff_toFun.mdifferentiableAt (by simp)) scalar]
  rfl

/-- The mixed second-variation density of the existing action. -/
abbrev globalHolonomicScalarJacobiDensity
    (massSquared : Real)
    (magnitude : SmoothQuotientField period hPeriod (Fin 4 → Real))
    (first second : GlobalScalarTestSpace period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  globalHolonomicScalarFirstVariationDensity period hPeriod massSquared
    magnitude first second point

theorem globalHolonomicScalarJacobiDensity_comm
    (massSquared : Real)
    (magnitude : SmoothQuotientField period hPeriod (Fin 4 → Real))
    (first second : GlobalScalarTestSpace period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalHolonomicScalarJacobiDensity period hPeriod massSquared magnitude
        first second point =
      globalHolonomicScalarJacobiDensity period hPeriod massSquared magnitude
        second first point := by
  unfold globalHolonomicScalarJacobiDensity
    globalHolonomicScalarFirstVariationDensity
  have hSum :
      (∑ index : Fin 4,
        signature index / magnitude point index *
          holonomicCovectorComponent period hPeriod first point index *
          holonomicCovectorComponent period hPeriod second point index) =
      ∑ index : Fin 4,
        signature index / magnitude point index *
          holonomicCovectorComponent period hPeriod second point index *
          holonomicCovectorComponent period hPeriod first point index := by
    apply Finset.sum_congr rfl
    intro index _
    ring
  rw [hSum]
  ring_nf

theorem globalHolonomicScalarJacobiDensity_add_right
    (massSquared : Real)
    (magnitude : SmoothQuotientField period hPeriod (Fin 4 → Real))
    (first second third : GlobalScalarTestSpace period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalHolonomicScalarJacobiDensity period hPeriod massSquared magnitude
        first (second + third) point =
      globalHolonomicScalarJacobiDensity period hPeriod massSquared magnitude
          first second point +
        globalHolonomicScalarJacobiDensity period hPeriod massSquared magnitude
          first third point := by
  unfold globalHolonomicScalarJacobiDensity
    globalHolonomicScalarFirstVariationDensity
  simp_rw [holonomicCovectorComponent_add period hPeriod]
  change _ * ((∑ index : Fin 4, _ * (_ + _)) +
    massSquared * first point * (second point + third point)) = _
  simp only [mul_add, Finset.sum_add_distrib]
  ring

theorem globalHolonomicScalarJacobiDensity_smul_right
    (massSquared : Real)
    (magnitude : SmoothQuotientField period hPeriod (Fin 4 → Real))
    (first second : GlobalScalarTestSpace period hPeriod)
    (scalar : Real) (point : EffectiveQuotient period hPeriod) :
    globalHolonomicScalarJacobiDensity period hPeriod massSquared magnitude
        first (scalar • second) point =
      scalar * globalHolonomicScalarJacobiDensity period hPeriod massSquared
        magnitude first second point := by
  unfold globalHolonomicScalarJacobiDensity
    globalHolonomicScalarFirstVariationDensity
  simp_rw [holonomicCovectorComponent_smul period hPeriod]
  change _ * ((∑ index : Fin 4, _ * (scalar * _)) +
    massSquared * first point * (scalar * second point)) = _
  have hSum :
      (∑ index : Fin 4,
        signature index / magnitude point index *
          holonomicCovectorComponent period hPeriod first point index *
          (scalar * holonomicCovectorComponent period hPeriod second point index)) =
        scalar * ∑ index : Fin 4,
          signature index / magnitude point index *
            holonomicCovectorComponent period hPeriod first point index *
            holonomicCovectorComponent period hPeriod second point index := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro index _
    ring
  rw [hSum]
  ring

/-- Explicit common form-domain contract.  It is needed because the fixed
frame components are not yet known globally continuous in the quotient atlas. -/
structure GlobalHolonomicScalarFormData where
  massSquared : Real
  magnitude : SmoothQuotientField period hPeriod (Fin 4 → Real)
  measure : Measure (EffectiveQuotient period hPeriod)
  pair_integrable : ∀ first second : GlobalScalarTestSpace period hPeriod,
    Integrable (globalHolonomicScalarJacobiDensity period hPeriod massSquared
      magnitude first second) measure

def globalHolonomicScalarJacobiForm
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (first second : GlobalScalarTestSpace period hPeriod) : Real :=
  ∫ point, globalHolonomicScalarJacobiDensity period hPeriod data.massSquared
    data.magnitude first second point ∂data.measure

theorem globalHolonomicScalarJacobiForm_comm
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (first second : GlobalScalarTestSpace period hPeriod) :
    globalHolonomicScalarJacobiForm period hPeriod data first second =
      globalHolonomicScalarJacobiForm period hPeriod data second first := by
  unfold globalHolonomicScalarJacobiForm
  apply integral_congr_ae
  exact Filter.Eventually.of_forall
    (globalHolonomicScalarJacobiDensity_comm period hPeriod
      data.massSquared data.magnitude first second)

theorem globalHolonomicScalarJacobiForm_add_right
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (first second third : GlobalScalarTestSpace period hPeriod) :
    globalHolonomicScalarJacobiForm period hPeriod data first (second + third) =
      globalHolonomicScalarJacobiForm period hPeriod data first second +
        globalHolonomicScalarJacobiForm period hPeriod data first third := by
  unfold globalHolonomicScalarJacobiForm
  simp_rw [globalHolonomicScalarJacobiDensity_add_right period hPeriod]
  exact integral_add (data.pair_integrable first second)
    (data.pair_integrable first third)

theorem globalHolonomicScalarJacobiForm_smul_right
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (first second : GlobalScalarTestSpace period hPeriod) (scalar : Real) :
    globalHolonomicScalarJacobiForm period hPeriod data first (scalar • second) =
      scalar * globalHolonomicScalarJacobiForm period hPeriod data first second := by
  unfold globalHolonomicScalarJacobiForm
  simp_rw [globalHolonomicScalarJacobiDensity_smul_right period hPeriod]
  simp only [integral_const_mul]

theorem globalHolonomicScalarJacobiForm_add_left
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (first second third : GlobalScalarTestSpace period hPeriod) :
    globalHolonomicScalarJacobiForm period hPeriod data (first + second) third =
      globalHolonomicScalarJacobiForm period hPeriod data first third +
        globalHolonomicScalarJacobiForm period hPeriod data second third := by
  rw [globalHolonomicScalarJacobiForm_comm period hPeriod data
      (first + second) third,
    globalHolonomicScalarJacobiForm_add_right period hPeriod data
      third first second,
    globalHolonomicScalarJacobiForm_comm period hPeriod data third first,
    globalHolonomicScalarJacobiForm_comm period hPeriod data third second]

theorem globalHolonomicScalarJacobiForm_smul_left
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (first second : GlobalScalarTestSpace period hPeriod) (scalar : Real) :
    globalHolonomicScalarJacobiForm period hPeriod data (scalar • first) second =
      scalar * globalHolonomicScalarJacobiForm period hPeriod data first second := by
  rw [globalHolonomicScalarJacobiForm_comm period hPeriod data
      (scalar • first) second,
    globalHolonomicScalarJacobiForm_smul_right period hPeriod data
      second first scalar,
    globalHolonomicScalarJacobiForm_comm period hPeriod data second first]

/-- Weak Euler operator of the existing global holonomic scalar action. -/
def weakGlobalHolonomicScalarEulerOperator
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (field : GlobalScalarTestSpace period hPeriod) :
    GlobalScalarTestSpace period hPeriod →ₗ[Real] Real where
  toFun test := globalHolonomicScalarJacobiForm period hPeriod data field test
  map_add' := globalHolonomicScalarJacobiForm_add_right period hPeriod data field
  map_smul' scalar test :=
    globalHolonomicScalarJacobiForm_smul_right period hPeriod data field test scalar

/-- Symmetric Jacobi operator, linear into the algebraic weak dual. -/
def weakGlobalHolonomicScalarJacobiOperator
    (data : GlobalHolonomicScalarFormData period hPeriod) :
    GlobalScalarTestSpace period hPeriod →ₗ[Real]
      (GlobalScalarTestSpace period hPeriod →ₗ[Real] Real) where
  toFun first := weakGlobalHolonomicScalarEulerOperator period hPeriod data first
  map_add' first second := by
    ext test
    exact globalHolonomicScalarJacobiForm_add_left period hPeriod data
      first second test
  map_smul' scalar first := by
    ext test
    exact globalHolonomicScalarJacobiForm_smul_left period hPeriod data
      first test scalar

@[simp]
theorem weakGlobalHolonomicScalarEulerOperator_apply
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (field test : GlobalScalarTestSpace period hPeriod) :
    weakGlobalHolonomicScalarEulerOperator period hPeriod data field test =
      globalHolonomicScalarFirstVariation period hPeriod data.massSquared
        data.magnitude field test data.measure :=
  rfl

@[simp]
theorem weakGlobalHolonomicScalarJacobiOperator_apply
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (first second : GlobalScalarTestSpace period hPeriod) :
    weakGlobalHolonomicScalarJacobiOperator period hPeriod data first second =
      globalHolonomicScalarJacobiForm period hPeriod data first second :=
  rfl

theorem weakGlobalHolonomicScalarJacobiOperator_symmetric
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (first second : GlobalScalarTestSpace period hPeriod) :
    weakGlobalHolonomicScalarJacobiOperator period hPeriod data first second =
      weakGlobalHolonomicScalarJacobiOperator period hPeriod data second first :=
  globalHolonomicScalarJacobiForm_comm period hPeriod data first second

theorem globalHolonomicScalarDensity_eq_half_jacobi
    (massSquared : Real)
    (magnitude : SmoothQuotientField period hPeriod (Fin 4 → Real))
    (field : GlobalScalarTestSpace period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalHolonomicScalarDensity period hPeriod massSquared magnitude field point =
      (1 / 2 : Real) *
        globalHolonomicScalarJacobiDensity period hPeriod massSquared magnitude
          field field point := by
  unfold globalHolonomicScalarDensity diagonalHolonomicKineticDensity
    globalHolonomicScalarJacobiDensity
    globalHolonomicScalarFirstVariationDensity
  ring_nf

/-- The common pair-integrability contract supplies the exact variation
contract required by the already proved action theorem. -/
def GlobalHolonomicScalarFormData.variationContract
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (field variation : GlobalScalarTestSpace period hPeriod) :
    GlobalScalarVariationContract period hPeriod data.massSquared
      data.magnitude field variation data.measure where
  base_integrable := by
    rw [show globalHolonomicScalarDensity period hPeriod data.massSquared
        data.magnitude field =
      fun point => (1 / 2 : Real) *
        globalHolonomicScalarJacobiDensity period hPeriod data.massSquared
          data.magnitude field field point from by
      funext point
      exact globalHolonomicScalarDensity_eq_half_jacobi period hPeriod
        data.massSquared data.magnitude field point]
    exact (data.pair_integrable field field).const_mul (1 / 2 : Real)
  first_integrable := data.pair_integrable field variation
  quadratic_integrable := by
    rw [show globalHolonomicScalarDensity period hPeriod data.massSquared
        data.magnitude variation =
      fun point => (1 / 2 : Real) *
        globalHolonomicScalarJacobiDensity period hPeriod data.massSquared
          data.magnitude variation variation point from by
      funext point
      exact globalHolonomicScalarDensity_eq_half_jacobi period hPeriod
        data.massSquared data.magnitude variation point]
    exact (data.pair_integrable variation variation).const_mul (1 / 2 : Real)

/-- `K` is the exact derivative of the unchanged global scalar action. -/
theorem globalHolonomicScalarAction_hasDerivAt_weakEuler
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (field variation : GlobalScalarTestSpace period hPeriod) :
    HasDerivAt
      (fun epsilon : Real =>
        globalHolonomicScalarAction period hPeriod data.massSquared
          data.magnitude
          (scalarAffineCurve period hPeriod field variation epsilon)
          data.measure)
      (weakGlobalHolonomicScalarEulerOperator period hPeriod data field variation) 0 := by
  exact globalHolonomicScalarAction_affine_hasDerivAt period hPeriod
    data.massSquared data.magnitude field variation data.measure
    (data.variationContract period hPeriod field variation)

theorem weakGlobalHolonomicScalarEulerOperator_affine
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (field direction : GlobalScalarTestSpace period hPeriod)
    (epsilon : Real) :
    weakGlobalHolonomicScalarEulerOperator period hPeriod data
        (scalarAffineCurve period hPeriod field direction epsilon) =
      weakGlobalHolonomicScalarEulerOperator period hPeriod data field +
        epsilon • weakGlobalHolonomicScalarJacobiOperator period hPeriod data direction := by
  ext test
  change globalHolonomicScalarJacobiForm period hPeriod data
      (field + epsilon • direction) test = _
  rw [globalHolonomicScalarJacobiForm_add_left period hPeriod data,
    globalHolonomicScalarJacobiForm_smul_left period hPeriod data]
  rfl

/-- The Jacobi pairing is the pointwise scalar derivative of the weak Euler
operator along every affine field curve. -/
theorem weakGlobalHolonomicScalarEulerOperator_hasDerivAt
    (data : GlobalHolonomicScalarFormData period hPeriod)
    (field direction test : GlobalScalarTestSpace period hPeriod) :
    HasDerivAt
      (fun epsilon : Real =>
        weakGlobalHolonomicScalarEulerOperator period hPeriod data
          (scalarAffineCurve period hPeriod field direction epsilon) test)
      (weakGlobalHolonomicScalarJacobiOperator period hPeriod data direction test) 0 := by
  rw [show (fun epsilon : Real =>
      weakGlobalHolonomicScalarEulerOperator period hPeriod data
        (scalarAffineCurve period hPeriod field direction epsilon) test) =
      (fun epsilon : Real =>
        weakGlobalHolonomicScalarEulerOperator period hPeriod data field test +
          epsilon * weakGlobalHolonomicScalarJacobiOperator period hPeriod
            data direction test) from by
      funext epsilon
      exact congrArg (fun functional => functional test)
        (weakGlobalHolonomicScalarEulerOperator_affine period hPeriod data
          field direction epsilon)]
  simpa only [id_eq, one_mul] using
    (((hasDerivAt_id (0 : Real)).mul_const
      (weakGlobalHolonomicScalarJacobiOperator period hPeriod
        data direction test)).const_add
      (weakGlobalHolonomicScalarEulerOperator period hPeriod data field test))

/-- The obstruction to using the full Lorentzian Hessian as an energy inner
product is explicit: its time coefficient is strictly negative. -/
theorem lorentz_time_kinetic_coefficient_neg
    (magnitude : SmoothQuotientField period hPeriod (Fin 4 → Real))
    (hMagnitude : ∀ point index, 0 < magnitude point index)
    (point : EffectiveQuotient period hPeriod) :
    signature 0 / magnitude point 0 < 0 := by
  rw [show signature 0 = (-1 : Real) by simp [signature]]
  exact div_neg_of_neg_of_pos (by norm_num) (hMagnitude point 0)

/-- Positive data for the maximal elementary sector supported by the current
formalization: fields with vanishing time-frame derivative. -/
structure PositiveStaticGlobalScalarData where
  formData : GlobalHolonomicScalarFormData period hPeriod
  magnitude_pos : ∀ point index,
    0 < formData.magnitude point index
  massSquared_pos : 0 < formData.massSquared
  finiteMeasure : IsFiniteMeasure formData.measure
  openPosMeasure : Measure.IsOpenPosMeasure formData.measure

theorem diagonalMetricVolumeDensity_pos
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    0 < diagonalMetricVolumeDensity period hPeriod
      data.formData.magnitude point := by
  unfold diagonalMetricVolumeDensity
  apply Real.sqrt_pos.2
  exact Finset.prod_pos fun index _ => data.magnitude_pos point index

theorem holonomicCovectorComponent_zero
    (point : EffectiveQuotient period hPeriod) (index : Fin 4) :
    holonomicCovectorComponent period hPeriod
        (0 : GlobalScalarTestSpace period hPeriod) point index = 0 := by
  have h := holonomicCovectorComponent_smul period hPeriod 0
    (0 : GlobalScalarTestSpace period hPeriod) point index
  simpa using h

/-- Tagged smooth form domain with zero derivative in the negative Lorentzian
time direction. -/
structure StaticGlobalScalarTest
    (_data : PositiveStaticGlobalScalarData period hPeriod) where
  toField : GlobalScalarTestSpace period hPeriod
  time_static : ∀ point,
    holonomicCovectorComponent period hPeriod toField point 0 = 0

@[ext]
theorem StaticGlobalScalarTest.ext
    {data : PositiveStaticGlobalScalarData period hPeriod}
    {first second : StaticGlobalScalarTest period hPeriod data}
    (h : first.toField = second.toField) : first = second := by
  cases first
  cases second
  congr

instance (data : PositiveStaticGlobalScalarData period hPeriod) :
    Zero (StaticGlobalScalarTest period hPeriod data) where
  zero := ⟨0, fun point =>
    holonomicCovectorComponent_zero period hPeriod point 0⟩

instance (data : PositiveStaticGlobalScalarData period hPeriod) :
    Add (StaticGlobalScalarTest period hPeriod data) where
  add first second :=
    ⟨first.toField + second.toField, fun point => by
      rw [holonomicCovectorComponent_add period hPeriod,
        first.time_static point, second.time_static point, add_zero]⟩

instance (data : PositiveStaticGlobalScalarData period hPeriod) :
    Neg (StaticGlobalScalarTest period hPeriod data) where
  neg field :=
    ⟨-field.toField, fun point => by
      simpa [field.time_static point] using
        (holonomicCovectorComponent_smul period hPeriod (-1)
          field.toField point 0)⟩

instance (data : PositiveStaticGlobalScalarData period hPeriod) :
    Sub (StaticGlobalScalarTest period hPeriod data) where
  sub first second := first + -second

instance (data : PositiveStaticGlobalScalarData period hPeriod) :
    AddCommGroup (StaticGlobalScalarTest period hPeriod data) where
  add_assoc first second third := by
    apply StaticGlobalScalarTest.ext
    exact add_assoc _ _ _
  zero_add field := by
    apply StaticGlobalScalarTest.ext
    exact zero_add _
  add_zero field := by
    apply StaticGlobalScalarTest.ext
    exact add_zero _
  nsmul := nsmulRec
  add_comm first second := by
    apply StaticGlobalScalarTest.ext
    exact add_comm _ _
  neg_add_cancel field := by
    apply StaticGlobalScalarTest.ext
    exact neg_add_cancel _
  sub_eq_add_neg first second := rfl
  zsmul := zsmulRec

instance (data : PositiveStaticGlobalScalarData period hPeriod) :
    SMul Real (StaticGlobalScalarTest period hPeriod data) where
  smul scalar field :=
    ⟨scalar • field.toField, fun point => by
      rw [holonomicCovectorComponent_smul period hPeriod,
        field.time_static point, mul_zero]⟩

instance (data : PositiveStaticGlobalScalarData period hPeriod) :
    Module Real (StaticGlobalScalarTest period hPeriod data) where
  one_smul field := by
    apply StaticGlobalScalarTest.ext
    exact one_smul Real field.toField
  mul_smul first second field := by
    apply StaticGlobalScalarTest.ext
    exact mul_smul first second field.toField
  smul_add scalar first second := by
    apply StaticGlobalScalarTest.ext
    exact smul_add scalar first.toField second.toField
  smul_zero scalar := by
    apply StaticGlobalScalarTest.ext
    exact smul_zero scalar
  add_smul first second field := by
    apply StaticGlobalScalarTest.ext
    exact add_smul first second field.toField
  zero_smul field := by
    apply StaticGlobalScalarTest.ext
    exact zero_smul Real field.toField

theorem staticHolonomicKineticSum_nonneg
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data)
    (point : EffectiveQuotient period hPeriod) :
    0 ≤ ∑ index : Fin 4,
      signature index / data.formData.magnitude point index *
        holonomicCovectorComponent period hPeriod field.toField point index *
        holonomicCovectorComponent period hPeriod field.toField point index := by
  apply Finset.sum_nonneg
  intro index _
  by_cases hIndex : index = 0
  · subst index
    rw [field.time_static point]
    simp
  · rw [show signature index = (1 : Real) by simp [signature, hIndex]]
    have hCoefficient : 0 < (1 : Real) /
        data.formData.magnitude point index :=
      one_div_pos.mpr (data.magnitude_pos point index)
    nlinarith [sq_nonneg
      (holonomicCovectorComponent period hPeriod field.toField point index)]

def staticScalarMassDensity
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data)
    (point : EffectiveQuotient period hPeriod) : Real :=
  diagonalMetricVolumeDensity period hPeriod data.formData.magnitude point *
    data.formData.massSquared * field.toField point ^ 2

theorem staticScalarMassDensity_continuous
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data) :
    Continuous (staticScalarMassDensity period hPeriod data field) := by
  unfold staticScalarMassDensity
  exact ((diagonalMetricVolumeDensity_continuous period hPeriod
    data.formData.magnitude).mul continuous_const).mul
      (field.toField.contMDiff_toFun.continuous.pow 2)

theorem staticScalarMassDensity_nonneg
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data)
    (point : EffectiveQuotient period hPeriod) :
    0 ≤ staticScalarMassDensity period hPeriod data field point := by
  unfold staticScalarMassDensity
  exact mul_nonneg
    (mul_nonneg (diagonalMetricVolumeDensity_pos period hPeriod data point).le
      data.massSquared_pos.le) (sq_nonneg _)

theorem staticScalarMassDensity_le_jacobi
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data)
    (point : EffectiveQuotient period hPeriod) :
    staticScalarMassDensity period hPeriod data field point ≤
      globalHolonomicScalarJacobiDensity period hPeriod
        data.formData.massSquared data.formData.magnitude
        field.toField field.toField point := by
  unfold staticScalarMassDensity globalHolonomicScalarJacobiDensity
    globalHolonomicScalarFirstVariationDensity
  have hVolume := diagonalMetricVolumeDensity_pos period hPeriod data point
  have hKinetic := staticHolonomicKineticSum_nonneg period hPeriod data field point
  nlinarith

theorem staticGlobalHolonomicScalarJacobiForm_self_pos
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data)
    (hField : field ≠ 0) :
    0 < globalHolonomicScalarJacobiForm period hPeriod data.formData
      field.toField field.toField := by
  letI : IsFiniteMeasure data.formData.measure := data.finiteMeasure
  letI : Measure.IsOpenPosMeasure data.formData.measure := data.openPosMeasure
  have hExists : ∃ point, field.toField point ≠ 0 := by
    by_contra h
    apply hField
    apply StaticGlobalScalarTest.ext
    apply SmoothQuotientField.ext period hPeriod Real
    intro point
    by_contra hPoint
    exact h ⟨point, hPoint⟩
  rcases hExists with ⟨point, hPoint⟩
  have hMassIntegrable : Integrable
      (staticScalarMassDensity period hPeriod data field)
      data.formData.measure :=
    (staticScalarMassDensity_continuous period hPeriod data field).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hMassPoint : staticScalarMassDensity period hPeriod data field point ≠ 0 := by
    unfold staticScalarMassDensity
    exact (mul_pos
      (mul_pos (diagonalMetricVolumeDensity_pos period hPeriod data point)
        data.massSquared_pos)
      (sq_pos_of_ne_zero hPoint)).ne'
  have hMassPositive : 0 < ∫ point,
      staticScalarMassDensity period hPeriod data field point
      ∂data.formData.measure :=
    integral_pos_of_integrable_nonneg_nonzero
      (staticScalarMassDensity_continuous period hPeriod data field)
      hMassIntegrable
      (staticScalarMassDensity_nonneg period hPeriod data field) hMassPoint
  have hLe := integral_mono hMassIntegrable
    (data.formData.pair_integrable field.toField field.toField)
    (staticScalarMassDensity_le_jacobi period hPeriod data field)
  unfold globalHolonomicScalarJacobiForm
  linarith

@[implicit_reducible]
noncomputable def staticScalarEnergyPreCore
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    PreInnerProductSpace.Core Real
      (StaticGlobalScalarTest period hPeriod data) := by
  letI : IsFiniteMeasure data.formData.measure := data.finiteMeasure
  refine
    { inner := fun first second =>
        globalHolonomicScalarJacobiForm period hPeriod data.formData
          first.toField second.toField
      conj_inner_symm := ?_
      re_inner_nonneg := ?_
      add_left := ?_
      smul_left := ?_ }
  · intro first second
    simpa using globalHolonomicScalarJacobiForm_comm period hPeriod
      data.formData second.toField first.toField
  · intro field
    by_cases hField : field = 0
    · subst field
      change 0 ≤ globalHolonomicScalarJacobiForm period hPeriod data.formData 0 0
      rw [← weakGlobalHolonomicScalarJacobiOperator_apply]
      simp
    · exact (staticGlobalHolonomicScalarJacobiForm_self_pos period hPeriod
        data field hField).le
  · intro first second third
    exact globalHolonomicScalarJacobiForm_add_left period hPeriod data.formData
      first.toField second.toField third.toField
  · intro first second scalar
    exact globalHolonomicScalarJacobiForm_smul_left period hPeriod data.formData
      first.toField second.toField scalar

@[implicit_reducible]
noncomputable def staticScalarEnergyCore
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    InnerProductSpace.Core Real
      (StaticGlobalScalarTest period hPeriod data) :=
  { __ := staticScalarEnergyPreCore period hPeriod data
    definite := by
      intro field hZero
      by_contra hField
      have hPos := staticGlobalHolonomicScalarJacobiForm_self_pos period hPeriod
        data field hField
      change globalHolonomicScalarJacobiForm period hPeriod data.formData
        field.toField field.toField = 0 at hZero
      linarith }

noncomputable instance staticScalarEnergyNormedAddCommGroup
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    NormedAddCommGroup (StaticGlobalScalarTest period hPeriod data) :=
  InnerProductSpace.Core.toNormedAddCommGroup
    (cd := staticScalarEnergyCore period hPeriod data)

noncomputable instance staticScalarEnergyInnerProductSpace
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    InnerProductSpace Real (StaticGlobalScalarTest period hPeriod data) :=
  InnerProductSpace.ofCore (staticScalarEnergyPreCore period hPeriod data)

abbrev StaticScalarEnergyH1
    (data : PositiveStaticGlobalScalarData period hPeriod) :=
  UniformSpace.Completion (StaticGlobalScalarTest period hPeriod data)

def staticScalarEnergyEmbedding
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    StaticGlobalScalarTest period hPeriod data →L[Real]
      StaticScalarEnergyH1 period hPeriod data :=
  UniformSpace.Completion.toComplL

theorem staticScalarEnergyEmbedding_denseRange
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    DenseRange (staticScalarEnergyEmbedding period hPeriod data) := by
  change DenseRange ((↑) : StaticGlobalScalarTest period hPeriod data →
    StaticScalarEnergyH1 period hPeriod data)
  exact UniformSpace.Completion.denseRange_coe

def weakStaticScalarJacobiExtension
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data) :
    StaticScalarEnergyH1 period hPeriod data →L[Real] Real :=
  InnerProductSpace.toDualMap Real (StaticScalarEnergyH1 period hPeriod data)
    (staticScalarEnergyEmbedding period hPeriod data field)

def strongStaticScalarJacobiRiesz
    (data : PositiveStaticGlobalScalarData period hPeriod) :
    StaticGlobalScalarTest period hPeriod data →L[Real]
      StaticScalarEnergyH1 period hPeriod data :=
  staticScalarEnergyEmbedding period hPeriod data

theorem strongStaticScalarJacobiRiesz_represents
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data)
    (test : StaticScalarEnergyH1 period hPeriod data) :
    inner Real (strongStaticScalarJacobiRiesz period hPeriod data field) test =
      weakStaticScalarJacobiExtension period hPeriod data field test :=
  rfl

theorem strongStaticScalarJacobiRiesz_smooth_pairing
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (first second : StaticGlobalScalarTest period hPeriod data) :
    inner Real
        (strongStaticScalarJacobiRiesz period hPeriod data first)
        (staticScalarEnergyEmbedding period hPeriod data second) =
      globalHolonomicScalarJacobiForm period hPeriod data.formData
        first.toField second.toField := by
  change inner Real
    (first : StaticScalarEnergyH1 period hPeriod data)
    (second : StaticScalarEnergyH1 period hPeriod data) = _
  rw [UniformSpace.Completion.inner_coe]
  rfl

theorem strongStaticScalarJacobiRiesz_kernel
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data) :
    strongStaticScalarJacobiRiesz period hPeriod data field = 0 ↔ field = 0 := by
  change (field : StaticScalarEnergyH1 period hPeriod data) = 0 ↔ field = 0
  rw [← UniformSpace.Completion.coe_zero]
  exact UniformSpace.Completion.coe_inj

/-- Weak matter equation in the honest positive time-static sector. -/
def SatisfiesWeakStaticGlobalScalarEquation
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data) : Prop :=
  ∀ test : StaticGlobalScalarTest period hPeriod data,
    weakGlobalHolonomicScalarEulerOperator period hPeriod data.formData
      field.toField test.toField = 0

/-- Stationarity of the unchanged action along the same time-static fields. -/
def StaticGlobalScalarStationary
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data) : Prop :=
  ∀ variation : StaticGlobalScalarTest period hPeriod data,
    HasDerivAt
      (fun epsilon : Real =>
        globalHolonomicScalarAction period hPeriod data.formData.massSquared
          data.formData.magnitude
          (scalarAffineCurve period hPeriod field.toField
            variation.toField epsilon) data.formData.measure)
      0 0

theorem staticGlobalScalarStationary_iff_weak
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data) :
    StaticGlobalScalarStationary period hPeriod data field ↔
      SatisfiesWeakStaticGlobalScalarEquation period hPeriod data field := by
  constructor
  · intro hStationary variation
    exact (globalHolonomicScalarAction_hasDerivAt_weakEuler period hPeriod
      data.formData field.toField variation.toField).unique
        (hStationary variation)
  · intro hWeak variation
    simpa [hWeak variation] using
      (globalHolonomicScalarAction_hasDerivAt_weakEuler period hPeriod
        data.formData field.toField variation.toField)

theorem satisfiesWeakStaticGlobalScalarEquation_iff_zero
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data) :
    SatisfiesWeakStaticGlobalScalarEquation period hPeriod data field ↔
      field = 0 := by
  constructor
  · intro hWeak
    by_contra hField
    have hPositive := staticGlobalHolonomicScalarJacobiForm_self_pos
      period hPeriod data field hField
    have hZero := hWeak field
    change globalHolonomicScalarJacobiForm period hPeriod data.formData
      field.toField field.toField = 0 at hZero
    linarith
  · intro hField
    subst field
    intro test
    change globalHolonomicScalarJacobiForm period hPeriod data.formData
      0 test.toField = 0
    rw [← weakGlobalHolonomicScalarJacobiOperator_apply]
    simp

/-- Exact weak/strong-Riesz equivalence for the matter equation. -/
theorem satisfiesWeakStaticGlobalScalarEquation_iff_strongRiesz
    (data : PositiveStaticGlobalScalarData period hPeriod)
    (field : StaticGlobalScalarTest period hPeriod data) :
    SatisfiesWeakStaticGlobalScalarEquation period hPeriod data field ↔
      strongStaticScalarJacobiRiesz period hPeriod data field = 0 := by
  rw [satisfiesWeakStaticGlobalScalarEquation_iff_zero period hPeriod,
    strongStaticScalarJacobiRiesz_kernel period hPeriod]

end

end P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
end JanusFormal
