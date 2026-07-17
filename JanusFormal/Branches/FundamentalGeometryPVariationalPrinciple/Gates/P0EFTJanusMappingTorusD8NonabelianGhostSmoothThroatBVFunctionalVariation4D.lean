import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVMaster4D

/-!
# Integrated variation and ultralocal BV bracket on the smooth throat

The fibrewise finite BV master density admits an exact quadratic expansion
along every smooth throat-field line.  Integration against the canonical
finite throat volume therefore gives its actual directional derivative without
an interchange-of-limit hypothesis.

We also define the canonical integrated odd bracket on analytic ultralocal
functionals whose fibre is the existing finite BV phase.  This is not a claim
about a bracket on arbitrary nonlocal functionals or a completed field space.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVFunctionalVariation4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal BigOperators
open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusD8NonabelianGhostPositiveMetricThroatBV4D
open P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVMaster4D

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

private def finiteMetricCEDifferentialContinuous :
    FiniteMetricCEField →L[Real] FiniteMetricCEField :=
  LinearMap.toContinuousLinearMap finiteMetricCEDifferential

private def finiteMetricCETransposeContinuous :
    FiniteMetricCEField →L[Real] FiniteMetricCEField :=
  LinearMap.toContinuousLinearMap finiteMetricCETranspose

private theorem finiteMetricDot_contDiff :
    ContDiff Real ω (fun pair : FiniteMetricCEField × FiniteMetricCEField =>
      finiteMetricDot pair.1 pair.2) := by
  unfold finiteMetricDot
  apply ContDiff.sum
  intro coordinate _
  apply ContDiff.sum
  intro slot _
  exact ((contDiff_apply Real Real (coordinate, slot)).comp contDiff_fst).mul
    ((contDiff_apply Real Real (coordinate, slot)).comp contDiff_snd)

private theorem finiteMetricBVMasterAction_contDiff :
    ContDiff Real ω finiteMetricBVMasterAction := by
  exact finiteMetricDot_contDiff.comp
    (contDiff_snd.prodMk
      (finiteMetricCEDifferentialContinuous.contDiff.comp contDiff_fst))

/-! ## Exact integrated first variation -/

/-- The canonical first variation of the finite master Hamiltonian. -/
def finiteMetricBVMasterFirstVariation
    (phase variation : FiniteMetricBVPhase) : Real :=
  finiteMetricDot
      (finiteMetricBVMasterObservable.fieldGradient phase) variation.1 +
    finiteMetricDot
      (finiteMetricBVMasterObservable.antifieldGradient phase) variation.2

theorem finiteMetricBVMasterFirstVariation_coordinate_expansion
    (phase variation : FiniteMetricBVPhase) :
    finiteMetricBVMasterFirstVariation phase variation =
      (∑ coordinate : PositiveMetricCoordinate,
        phase.2 (coordinate, 1) * variation.1 (coordinate, 0)) +
      ∑ coordinate : PositiveMetricCoordinate,
        phase.1 (coordinate, 0) * variation.2 (coordinate, 1) := by
  simp [finiteMetricBVMasterFirstVariation, finiteMetricBVMasterObservable,
    finiteMetricDot, finiteMetricCETranspose, finiteMetricCEDifferential,
    Fin.sum_univ_two]

private theorem contMDiff_fintype_sum
    {Index : Type*} [Fintype Index]
    (summand : Index → EffectiveThroat period hPeriod → Real)
    (hSummand : ∀ index, ContMDiff throatCoverModelWithCorners
      𝓘(Real, Real) ω (summand index)) :
    ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ω
      (fun point => ∑ index, summand index point) := by
  classical
  suffices hFinite : ∀ indices : Finset Index,
      ContMDiff throatCoverModelWithCorners 𝓘(Real, Real) ω
        (fun point => ∑ index ∈ indices, summand index point) by
    simpa using hFinite Finset.univ
  intro indices
  induction indices using Finset.induction_on with
  | empty => simpa using
      (contMDiff_const : ContMDiff throatCoverModelWithCorners
        𝓘(Real, Real) ω (fun _ : EffectiveThroat period hPeriod => (0 : Real)))
  | @insert index indices hIndex hInduction =>
      apply ((hSummand index).add hInduction).congr
      intro point
      simp [Finset.sum_insert, hIndex, Pi.add_apply]

theorem finiteMetricBVMasterFirstVariation_eq_BRST
    (phase variation : FiniteMetricBVPhase) :
    finiteMetricBVMasterFirstVariation phase variation =
      finiteMetricDot (finiteMetricBVBRST phase).2 variation.1 +
        finiteMetricDot (finiteMetricBVBRST phase).1 variation.2 :=
  rfl

/-- Smooth pointwise first-variation density. -/
def smoothThroatBVMasterFirstVariationDensity
    (field variation : SmoothFiniteMetricBVField period hPeriod) :
    SmoothThroatField period hPeriod Real where
  toFun point :=
    (∑ coordinate : PositiveMetricCoordinate,
      (field point).2 (coordinate, 1) *
        (variation point).1 (coordinate, 0)) +
    ∑ coordinate : PositiveMetricCoordinate,
      (field point).1 (coordinate, 0) *
        (variation point).2 (coordinate, 1)
  contMDiff_toFun := by
    have hFieldParts :=
      (contMDiff_prod_module_iff field.toFun).1 field.contMDiff_toFun
    have hVariationParts :=
      (contMDiff_prod_module_iff variation.toFun).1 variation.contMDiff_toFun
    have hFieldFirst := contMDiff_pi_space.mp hFieldParts.1
    have hFieldSecond := contMDiff_pi_space.mp hFieldParts.2
    have hVariationFirst := contMDiff_pi_space.mp hVariationParts.1
    have hVariationSecond := contMDiff_pi_space.mp hVariationParts.2
    exact (contMDiff_fintype_sum period hPeriod _ fun coordinate =>
      (hFieldSecond (coordinate, 1)).mul
        (hVariationFirst (coordinate, 0))).add
      (contMDiff_fintype_sum period hPeriod _ fun coordinate =>
        (hFieldFirst (coordinate, 0)).mul
          (hVariationSecond (coordinate, 1)))

@[simp]
theorem smoothThroatBVMasterFirstVariationDensity_apply
    (field variation : SmoothFiniteMetricBVField period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    smoothThroatBVMasterFirstVariationDensity period hPeriod
        field variation point =
      finiteMetricBVMasterFirstVariation (field point) (variation point) :=
  by
    exact (finiteMetricBVMasterFirstVariation_coordinate_expansion
      (field point) (variation point)).symm

theorem smoothThroatBVMasterFirstVariationDensity_eq_BRST
    (field variation : SmoothFiniteMetricBVField period hPeriod)
    (point : EffectiveThroat period hPeriod) :
    smoothThroatBVMasterFirstVariationDensity period hPeriod
        field variation point =
      finiteMetricDot (smoothThroatBVBRST period hPeriod field point).2
          (variation point).1 +
        finiteMetricDot (smoothThroatBVBRST period hPeriod field point).1
          (variation point).2 :=
  by
    rw [smoothThroatBVMasterFirstVariationDensity_apply,
      smoothThroatBVBRST_apply]
    exact finiteMetricBVMasterFirstVariation_eq_BRST
      (field point) (variation point)

/-- Integrated first variation against the canonical physical throat volume. -/
def canonicalSmoothThroatBVMasterFirstVariation
    (field variation : SmoothFiniteMetricBVField period hPeriod) : Real :=
  ∫ point, smoothThroatBVMasterFirstVariationDensity period hPeriod
      field variation point
    ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)

theorem smoothThroatBVMasterFirstVariationDensity_integrable
    (field variation : SmoothFiniteMetricBVField period hPeriod) :
    Integrable (smoothThroatBVMasterFirstVariationDensity period hPeriod
      field variation) (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  exact (smoothThroatBVMasterFirstVariationDensity period hPeriod
      field variation).contMDiff_toFun.continuous
    |>.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace
        (smoothThroatBVMasterFirstVariationDensity period hPeriod
          field variation))

/-- Affine line in the smooth BV field space. -/
def smoothThroatBVFieldLine
    (field variation : SmoothFiniteMetricBVField period hPeriod)
    (epsilon : Real) : SmoothFiniteMetricBVField period hPeriod :=
  field + epsilon • variation

@[simp]
theorem smoothThroatBVFieldLine_apply
    (field variation : SmoothFiniteMetricBVField period hPeriod)
    (epsilon : Real) (point : EffectiveThroat period hPeriod) :
    smoothThroatBVFieldLine period hPeriod field variation epsilon point =
      field point + epsilon • variation point :=
  rfl

theorem smoothThroatBVMasterDensity_line_expansion
    (field variation : SmoothFiniteMetricBVField period hPeriod)
    (epsilon : Real) (point : EffectiveThroat period hPeriod) :
    smoothThroatBVMasterDensity period hPeriod
        (smoothThroatBVFieldLine period hPeriod field variation epsilon) point =
      smoothThroatBVMasterDensity period hPeriod field point +
        epsilon * smoothThroatBVMasterFirstVariationDensity period hPeriod
          field variation point +
        epsilon ^ 2 * smoothThroatBVMasterDensity period hPeriod variation point := by
  rw [smoothThroatBVMasterDensity_apply,
    smoothThroatBVFieldLine_apply,
    finiteMetricBVMasterAction_first_variation]
  simp [finiteMetricBVMasterFirstVariation, finiteMetricBVMasterObservable,
    finiteMetricBVMasterAction, finiteMetricDot]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  have hFirst :
      (∑ coordinate : PositiveMetricCoordinate,
        (field point).2 (coordinate, 1) *
          (epsilon * (variation point).1 (coordinate, 0))) =
      ∑ coordinate : PositiveMetricCoordinate,
        epsilon * ((field point).2 (coordinate, 1) *
          (variation point).1 (coordinate, 0)) := by
    apply Finset.sum_congr rfl
    intro coordinate _
    ring
  have hSecond :
      (∑ coordinate : PositiveMetricCoordinate,
        (field point).1 (coordinate, 0) *
          (epsilon * (variation point).2 (coordinate, 1))) =
      ∑ coordinate : PositiveMetricCoordinate,
        epsilon * ((field point).1 (coordinate, 0) *
          (variation point).2 (coordinate, 1)) := by
    apply Finset.sum_congr rfl
    intro coordinate _
    ring
  have hRemainder :
      (∑ coordinate : PositiveMetricCoordinate,
        epsilon * (variation point).2 (coordinate, 1) *
          (epsilon * (variation point).1 (coordinate, 0))) =
      ∑ coordinate : PositiveMetricCoordinate,
        epsilon ^ 2 * ((variation point).2 (coordinate, 1) *
          (variation point).1 (coordinate, 0)) := by
    apply Finset.sum_congr rfl
    intro coordinate _
    ring
  rw [hFirst, hSecond, hRemainder]
  ring

/-- Exact integrated quadratic expansion of the canonical master action. -/
theorem canonicalSmoothThroatBVMasterAction_line_expansion
    (field variation : SmoothFiniteMetricBVField period hPeriod)
    (epsilon : Real) :
    canonicalSmoothThroatBVMasterAction period hPeriod
        (smoothThroatBVFieldLine period hPeriod field variation epsilon) =
      canonicalSmoothThroatBVMasterAction period hPeriod field +
        epsilon * canonicalSmoothThroatBVMasterFirstVariation period hPeriod
          field variation +
        epsilon ^ 2 * canonicalSmoothThroatBVMasterAction period hPeriod
          variation := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  have hBase := smoothThroatBVMasterDensity_integrable period hPeriod field
  have hFirst := smoothThroatBVMasterFirstVariationDensity_integrable
    period hPeriod field variation
  have hRemainder := smoothThroatBVMasterDensity_integrable
    period hPeriod variation
  unfold canonicalSmoothThroatBVMasterAction
    canonicalSmoothThroatBVMasterFirstVariation
  simp_rw [smoothThroatBVMasterDensity_line_expansion period hPeriod
    field variation epsilon]
  calc
    ∫ point,
        smoothThroatBVMasterDensity period hPeriod field point +
          epsilon * smoothThroatBVMasterFirstVariationDensity period hPeriod
            field variation point +
          epsilon ^ 2 * smoothThroatBVMasterDensity period hPeriod variation point
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) =
      ∫ point,
        smoothThroatBVMasterDensity period hPeriod field point +
          (epsilon * smoothThroatBVMasterFirstVariationDensity period hPeriod
              field variation point +
            epsilon ^ 2 * smoothThroatBVMasterDensity period hPeriod variation point)
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
          congr 1
          funext point
          ring
    _ =
      (∫ point, smoothThroatBVMasterDensity period hPeriod field point
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) +
      ∫ point,
          epsilon * smoothThroatBVMasterFirstVariationDensity period hPeriod
              field variation point +
            epsilon ^ 2 * smoothThroatBVMasterDensity period hPeriod variation point
        ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
          exact integral_add hBase
            ((hFirst.const_mul epsilon).add
              (hRemainder.const_mul (epsilon ^ 2)))
    _ = _ := by
      rw [integral_add (hFirst.const_mul epsilon)
        (hRemainder.const_mul (epsilon ^ 2)),
        integral_const_mul, integral_const_mul]
      ring

/-- The integrated pointwise gradient formula is the actual directional
derivative of the canonical master action. -/
theorem canonicalSmoothThroatBVMasterAction_line_hasDerivAt
    (field variation : SmoothFiniteMetricBVField period hPeriod) :
    HasDerivAt
      (fun epsilon : Real => canonicalSmoothThroatBVMasterAction period hPeriod
        (smoothThroatBVFieldLine period hPeriod field variation epsilon))
      (canonicalSmoothThroatBVMasterFirstVariation period hPeriod
        field variation) 0 := by
  rw [show (fun epsilon : Real =>
      canonicalSmoothThroatBVMasterAction period hPeriod
        (smoothThroatBVFieldLine period hPeriod field variation epsilon)) =
      (fun epsilon : Real =>
        canonicalSmoothThroatBVMasterAction period hPeriod field +
          epsilon * canonicalSmoothThroatBVMasterFirstVariation period hPeriod
            field variation +
          epsilon ^ 2 * canonicalSmoothThroatBVMasterAction period hPeriod
            variation) by
      funext epsilon
      exact canonicalSmoothThroatBVMasterAction_line_expansion period hPeriod
        field variation epsilon]
  have hLinear := ((hasDerivAt_id (𝕜 := Real) 0).mul_const
    (canonicalSmoothThroatBVMasterFirstVariation period hPeriod field variation))
      |>.const_add (canonicalSmoothThroatBVMasterAction period hPeriod field)
  have hQuadratic := ((hasDerivAt_id (𝕜 := Real) 0).pow 2).mul_const
    (canonicalSmoothThroatBVMasterAction period hPeriod variation)
  change HasDerivAt
    ((fun epsilon : Real =>
        canonicalSmoothThroatBVMasterAction period hPeriod field +
          epsilon * canonicalSmoothThroatBVMasterFirstVariation period hPeriod
            field variation) +
      (fun epsilon : Real => epsilon ^ 2 *
        canonicalSmoothThroatBVMasterAction period hPeriod variation)) _ 0
  exact (hLinear.add hQuadratic).congr_deriv (by norm_num)

/-! ## Canonical bracket on analytic ultralocal functionals -/

/-- An ultralocal functional is represented by a finite BV observable whose
value and canonical gradients are analytic on the finite phase. -/
structure SmoothUltralocalBVFunctional where
  observable : FiniteBVObservable
  value_contDiff : ContDiff Real ω observable.value
  fieldGradient_contDiff : ContDiff Real ω observable.fieldGradient
  antifieldGradient_contDiff : ContDiff Real ω observable.antifieldGradient

/-- Evaluation of an ultralocal functional on a smooth throat field. -/
def canonicalUltralocalBVFunctionalValue
    (functional : SmoothUltralocalBVFunctional)
    (field : SmoothFiniteMetricBVField period hPeriod) : Real :=
  ∫ point, functional.observable.value (field point)
    ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)

theorem canonicalUltralocalBVFunctionalDensity_integrable
    (functional : SmoothUltralocalBVFunctional)
    (field : SmoothFiniteMetricBVField period hPeriod) :
    Integrable (fun point => functional.observable.value (field point))
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  exact (functional.value_contDiff.contMDiff.comp field.contMDiff_toFun).continuous
    |>.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace
        (fun point => functional.observable.value (field point)))

private theorem smoothUltralocalBVOddBracket_contDiff
    (first second : SmoothUltralocalBVFunctional) :
    ContDiff Real ω (finiteBVOddAntibracket first.observable
      second.observable) := by
  unfold finiteBVOddAntibracket
  exact (finiteMetricDot_contDiff.comp
      (first.fieldGradient_contDiff.prodMk
        second.antifieldGradient_contDiff)).sub
    (contDiff_const.mul
      (finiteMetricDot_contDiff.comp
        (second.fieldGradient_contDiff.prodMk
          first.antifieldGradient_contDiff)))

/-- Canonical functional odd bracket on represented analytic ultralocal
densities, using the canonical throat volume pairing. -/
def canonicalUltralocalBVOddAntibracket
    (first second : SmoothUltralocalBVFunctional)
    (field : SmoothFiniteMetricBVField period hPeriod) : Real :=
  ∫ point, finiteBVOddAntibracket first.observable second.observable
      (field point)
    ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)

theorem canonicalUltralocalBVOddAntibracket_integrable
    (first second : SmoothUltralocalBVFunctional)
    (field : SmoothFiniteMetricBVField period hPeriod) :
    Integrable (fun point => finiteBVOddAntibracket first.observable
      second.observable (field point))
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
    intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod
  exact (smoothUltralocalBVOddBracket_contDiff first second |>.contMDiff.comp
      field.contMDiff_toFun).continuous
    |>.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace
        (fun point => finiteBVOddAntibracket first.observable
          second.observable (field point)))

/-- The finite master density as an analytic ultralocal functional. -/
def smoothThroatBVMasterUltralocalFunctional :
    SmoothUltralocalBVFunctional where
  observable := finiteMetricBVMasterObservable
  value_contDiff := finiteMetricBVMasterAction_contDiff
  fieldGradient_contDiff :=
    finiteMetricCETransposeContinuous.contDiff.comp contDiff_snd
  antifieldGradient_contDiff :=
    finiteMetricCEDifferentialContinuous.contDiff.comp contDiff_fst

theorem smoothThroatBVMasterUltralocalFunctional_value
    (field : SmoothFiniteMetricBVField period hPeriod) :
    canonicalUltralocalBVFunctionalValue period hPeriod
        smoothThroatBVMasterUltralocalFunctional field =
      canonicalSmoothThroatBVMasterAction period hPeriod field :=
  rfl

/-- Integrated classical master equation on the represented ultralocal
functional class. -/
theorem canonicalSmoothThroatBV_integrated_classical_master_equation
    (field : SmoothFiniteMetricBVField period hPeriod) :
    canonicalUltralocalBVOddAntibracket period hPeriod
        smoothThroatBVMasterUltralocalFunctional
        smoothThroatBVMasterUltralocalFunctional field = 0 := by
  change (∫ point, finiteBVOddAntibracket finiteMetricBVMasterObservable
      finiteMetricBVMasterObservable (field point)
    ∂(intrinsicCanonicalThroatVolumeMeasure period hPeriod)) = 0
  simp only [finiteMetricBV_classical_master_equation, integral_zero]

end
end P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVFunctionalVariation4D
end JanusFormal
