import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVMaster4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVFunctionalVariation4D

/-!
# Functional variation of the smooth spacetime BV master action

The finite BV master Hamiltonian has an exact quadratic expansion along every
smooth spacetime-field line.  Its canonical Lorentz-volume integral therefore
has the stated directional derivative without an interchange-of-limit
hypothesis.  We also install the canonical odd bracket on represented analytic
ultralocal functionals and prove the corresponding integrated CME.

This remains the constant finite BV phase bundle.  No bracket on arbitrary
nonlocal functionals, completed field spaces, or general tensor metrics is
asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVFunctionalVariation4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff ENNReal BigOperators
open MeasureTheory Set
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusD8NonabelianGhostPositiveMetricThroatBV4D
open P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVMaster4D
open P0EFTJanusMappingTorusD8NonabelianGhostSmoothThroatBVFunctionalVariation4D

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

private theorem contMDiff_fintype_sum
    {Index : Type*} [Fintype Index]
    (summand : Index → EffectiveQuotient period hPeriod → Real)
    (hSummand : ∀ index, ContMDiff coverModelWithCorners
      𝓘(Real, Real) ω (summand index)) :
    ContMDiff coverModelWithCorners 𝓘(Real, Real) ω
      (fun point => ∑ index, summand index point) := by
  classical
  suffices hFinite : ∀ indices : Finset Index,
      ContMDiff coverModelWithCorners 𝓘(Real, Real) ω
        (fun point => ∑ index ∈ indices, summand index point) by
    simpa using hFinite Finset.univ
  intro indices
  induction indices using Finset.induction_on with
  | empty => simpa using
      (contMDiff_const : ContMDiff coverModelWithCorners
        𝓘(Real, Real) ω (fun _ : EffectiveQuotient period hPeriod => (0 : Real)))
  | @insert index indices hIndex hInduction =>
      apply ((hSummand index).add hInduction).congr
      intro point
      simp [Finset.sum_insert, hIndex, Pi.add_apply]

/-! ## Exact integrated first variation -/

/-- Smooth fibrewise first-variation density on the spacetime quotient. -/
def smoothSpacetimeBVMasterFirstVariationDensity
    (field variation : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    SmoothQuotientField period hPeriod Real where
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
theorem smoothSpacetimeBVMasterFirstVariationDensity_apply
    (field variation : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothSpacetimeBVMasterFirstVariationDensity period hPeriod
        field variation point =
      finiteMetricBVMasterFirstVariation (field point) (variation point) :=
  by
    exact (finiteMetricBVMasterFirstVariation_coordinate_expansion
      (field point) (variation point)).symm

theorem smoothSpacetimeBVMasterFirstVariationDensity_eq_BRST
    (field variation : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothSpacetimeBVMasterFirstVariationDensity period hPeriod
        field variation point =
      finiteMetricDot (smoothSpacetimeBVBRST period hPeriod field point).2
          (variation point).1 +
        finiteMetricDot (smoothSpacetimeBVBRST period hPeriod field point).1
          (variation point).2 := by
  rw [smoothSpacetimeBVMasterFirstVariationDensity_apply,
    smoothSpacetimeBVBRST_apply]
  exact finiteMetricBVMasterFirstVariation_eq_BRST
    (field point) (variation point)

/-- Integrated first variation against canonical spacetime Lorentz volume. -/
def canonicalSmoothSpacetimeBVMasterFirstVariation
    (field variation : SmoothFiniteMetricBVSpacetimeField period hPeriod) : Real :=
  ∫ point, smoothSpacetimeBVMasterFirstVariationDensity period hPeriod
      field variation point
    ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

theorem smoothSpacetimeBVMasterFirstVariationDensity_integrable
    (field variation : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    Integrable (smoothSpacetimeBVMasterFirstVariationDensity period hPeriod
      field variation) (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  exact (smoothSpacetimeBVMasterFirstVariationDensity period hPeriod
      field variation).contMDiff_toFun.continuous
    |>.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace
        (smoothSpacetimeBVMasterFirstVariationDensity period hPeriod
          field variation))

/-- Affine line in the smooth spacetime BV field space. -/
def smoothSpacetimeBVFieldLine
    (field variation : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (epsilon : Real) : SmoothFiniteMetricBVSpacetimeField period hPeriod :=
  field + epsilon • variation

@[simp]
theorem smoothSpacetimeBVFieldLine_apply
    (field variation : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (epsilon : Real) (point : EffectiveQuotient period hPeriod) :
    smoothSpacetimeBVFieldLine period hPeriod field variation epsilon point =
      field point + epsilon • variation point :=
  rfl

private theorem finiteMetricBVMasterAction_line_expansion
    (phase variation : FiniteMetricBVPhase) (epsilon : Real) :
    finiteMetricBVMasterAction (phase + epsilon • variation) =
      finiteMetricBVMasterAction phase +
        epsilon * finiteMetricBVMasterFirstVariation phase variation +
        epsilon ^ 2 * finiteMetricBVMasterAction variation := by
  rw [finiteMetricBVMasterAction_first_variation]
  simp [finiteMetricBVMasterFirstVariation, finiteMetricBVMasterObservable,
    finiteMetricBVMasterAction, finiteMetricDot]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  have hFirst :
      (∑ coordinate : PositiveMetricCoordinate,
        phase.2 (coordinate, 1) *
          (epsilon * variation.1 (coordinate, 0))) =
      ∑ coordinate : PositiveMetricCoordinate,
        epsilon * (phase.2 (coordinate, 1) *
          variation.1 (coordinate, 0)) := by
    apply Finset.sum_congr rfl
    intro coordinate _
    ring
  have hSecond :
      (∑ coordinate : PositiveMetricCoordinate,
        phase.1 (coordinate, 0) *
          (epsilon * variation.2 (coordinate, 1))) =
      ∑ coordinate : PositiveMetricCoordinate,
        epsilon * (phase.1 (coordinate, 0) *
          variation.2 (coordinate, 1)) := by
    apply Finset.sum_congr rfl
    intro coordinate _
    ring
  have hRemainder :
      (∑ coordinate : PositiveMetricCoordinate,
        epsilon * variation.2 (coordinate, 1) *
          (epsilon * variation.1 (coordinate, 0))) =
      ∑ coordinate : PositiveMetricCoordinate,
        epsilon ^ 2 * (variation.2 (coordinate, 1) *
          variation.1 (coordinate, 0)) := by
    apply Finset.sum_congr rfl
    intro coordinate _
    ring
  rw [hFirst, hSecond, hRemainder]
  ring

theorem smoothSpacetimeBVMasterDensity_line_expansion
    (field variation : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (epsilon : Real) (point : EffectiveQuotient period hPeriod) :
    smoothSpacetimeBVMasterDensity period hPeriod
        (smoothSpacetimeBVFieldLine period hPeriod field variation epsilon) point =
      smoothSpacetimeBVMasterDensity period hPeriod field point +
        epsilon * smoothSpacetimeBVMasterFirstVariationDensity period hPeriod
          field variation point +
        epsilon ^ 2 * smoothSpacetimeBVMasterDensity period hPeriod variation point := by
  rw [smoothSpacetimeBVMasterDensity_apply,
    smoothSpacetimeBVFieldLine_apply,
    smoothSpacetimeBVMasterFirstVariationDensity_apply,
    smoothSpacetimeBVMasterDensity_apply,
    smoothSpacetimeBVMasterDensity_apply]
  exact finiteMetricBVMasterAction_line_expansion (field point)
    (variation point) epsilon

/-- Exact integrated quadratic expansion of the spacetime master action. -/
theorem canonicalSmoothSpacetimeBVMasterAction_line_expansion
    (field variation : SmoothFiniteMetricBVSpacetimeField period hPeriod)
    (epsilon : Real) :
    canonicalSmoothSpacetimeBVMasterAction period hPeriod
        (smoothSpacetimeBVFieldLine period hPeriod field variation epsilon) =
      canonicalSmoothSpacetimeBVMasterAction period hPeriod field +
        epsilon * canonicalSmoothSpacetimeBVMasterFirstVariation period hPeriod
          field variation +
        epsilon ^ 2 * canonicalSmoothSpacetimeBVMasterAction period hPeriod
          variation := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  have hBase := smoothSpacetimeBVMasterDensity_integrable period hPeriod field
  have hFirst := smoothSpacetimeBVMasterFirstVariationDensity_integrable
    period hPeriod field variation
  have hRemainder := smoothSpacetimeBVMasterDensity_integrable
    period hPeriod variation
  unfold canonicalSmoothSpacetimeBVMasterAction
    canonicalSmoothSpacetimeBVMasterFirstVariation
  simp_rw [smoothSpacetimeBVMasterDensity_line_expansion period hPeriod
    field variation epsilon]
  calc
    ∫ point,
        smoothSpacetimeBVMasterDensity period hPeriod field point +
          epsilon * smoothSpacetimeBVMasterFirstVariationDensity period hPeriod
            field variation point +
          epsilon ^ 2 * smoothSpacetimeBVMasterDensity period hPeriod variation point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      ∫ point,
        smoothSpacetimeBVMasterDensity period hPeriod field point +
          (epsilon * smoothSpacetimeBVMasterFirstVariationDensity period hPeriod
              field variation point +
            epsilon ^ 2 * smoothSpacetimeBVMasterDensity period hPeriod variation point)
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
          congr 1
          funext point
          ring
    _ =
      (∫ point, smoothSpacetimeBVMasterDensity period hPeriod field point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) +
      ∫ point,
          epsilon * smoothSpacetimeBVMasterFirstVariationDensity period hPeriod
              field variation point +
            epsilon ^ 2 * smoothSpacetimeBVMasterDensity period hPeriod variation point
        ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
          exact integral_add hBase
            ((hFirst.const_mul epsilon).add
              (hRemainder.const_mul (epsilon ^ 2)))
    _ = _ := by
      rw [integral_add (hFirst.const_mul epsilon)
        (hRemainder.const_mul (epsilon ^ 2)),
        integral_const_mul, integral_const_mul]
      ring

/-- The integrated gradient is the actual directional derivative. -/
theorem canonicalSmoothSpacetimeBVMasterAction_line_hasDerivAt
    (field variation : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    HasDerivAt
      (fun epsilon : Real => canonicalSmoothSpacetimeBVMasterAction period hPeriod
        (smoothSpacetimeBVFieldLine period hPeriod field variation epsilon))
      (canonicalSmoothSpacetimeBVMasterFirstVariation period hPeriod
        field variation) 0 := by
  rw [show (fun epsilon : Real =>
      canonicalSmoothSpacetimeBVMasterAction period hPeriod
        (smoothSpacetimeBVFieldLine period hPeriod field variation epsilon)) =
      (fun epsilon : Real =>
        canonicalSmoothSpacetimeBVMasterAction period hPeriod field +
          epsilon * canonicalSmoothSpacetimeBVMasterFirstVariation period hPeriod
            field variation +
          epsilon ^ 2 * canonicalSmoothSpacetimeBVMasterAction period hPeriod
            variation) by
      funext epsilon
      exact canonicalSmoothSpacetimeBVMasterAction_line_expansion period hPeriod
        field variation epsilon]
  have hLinear := ((hasDerivAt_id (𝕜 := Real) 0).mul_const
    (canonicalSmoothSpacetimeBVMasterFirstVariation period hPeriod field variation))
      |>.const_add (canonicalSmoothSpacetimeBVMasterAction period hPeriod field)
  have hQuadratic := ((hasDerivAt_id (𝕜 := Real) 0).pow 2).mul_const
    (canonicalSmoothSpacetimeBVMasterAction period hPeriod variation)
  change HasDerivAt
    ((fun epsilon : Real =>
        canonicalSmoothSpacetimeBVMasterAction period hPeriod field +
          epsilon * canonicalSmoothSpacetimeBVMasterFirstVariation period hPeriod
            field variation) +
      (fun epsilon : Real => epsilon ^ 2 *
        canonicalSmoothSpacetimeBVMasterAction period hPeriod variation)) _ 0
  exact (hLinear.add hQuadratic).congr_deriv (by norm_num)

/-! ## Canonical bracket on represented analytic ultralocal functionals -/

/-- Evaluation of a represented ultralocal functional on a spacetime field. -/
def canonicalSpacetimeUltralocalBVFunctionalValue
    (functional : SmoothUltralocalBVFunctional)
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) : Real :=
  ∫ point, functional.observable.value (field point)
    ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

theorem canonicalSpacetimeUltralocalBVFunctionalDensity_integrable
    (functional : SmoothUltralocalBVFunctional)
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    Integrable (fun point => functional.observable.value (field point))
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
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

/-- Canonical spacetime odd bracket for represented analytic ultralocal
functionals. -/
def canonicalSpacetimeUltralocalBVOddAntibracket
    (first second : SmoothUltralocalBVFunctional)
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) : Real :=
  ∫ point, finiteBVOddAntibracket first.observable second.observable
      (field point)
    ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)

theorem canonicalSpacetimeUltralocalBVOddAntibracket_integrable
    (first second : SmoothUltralocalBVFunctional)
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    Integrable (fun point => finiteBVOddAntibracket first.observable
      second.observable (field point))
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) := by
  letI : IsFiniteMeasure
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
    intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod
  exact (smoothUltralocalBVOddBracket_contDiff first second |>.contMDiff.comp
      field.contMDiff_toFun).continuous
    |>.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace
        (fun point => finiteBVOddAntibracket first.observable
          second.observable (field point)))

/-- The finite master density as a spacetime ultralocal functional. -/
def smoothSpacetimeBVMasterUltralocalFunctional :
    SmoothUltralocalBVFunctional :=
  smoothThroatBVMasterUltralocalFunctional

theorem smoothSpacetimeBVMasterUltralocalFunctional_value
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    canonicalSpacetimeUltralocalBVFunctionalValue period hPeriod
        smoothSpacetimeBVMasterUltralocalFunctional field =
      canonicalSmoothSpacetimeBVMasterAction period hPeriod field :=
  rfl

/-- Integrated CME for the represented spacetime ultralocal functional. -/
theorem canonicalSmoothSpacetimeBV_ultralocal_integrated_classical_master_equation
    (field : SmoothFiniteMetricBVSpacetimeField period hPeriod) :
    canonicalSpacetimeUltralocalBVOddAntibracket period hPeriod
        smoothSpacetimeBVMasterUltralocalFunctional
        smoothSpacetimeBVMasterUltralocalFunctional field = 0 := by
  change (∫ point, finiteBVOddAntibracket finiteMetricBVMasterObservable
      finiteMetricBVMasterObservable (field point)
    ∂(intrinsicCanonicalLorentzVolumeMeasure period hPeriod)) = 0
  simp only [finiteMetricBV_classical_master_equation, integral_zero]

end
end P0EFTJanusMappingTorusD8NonabelianGhostSmoothSpacetimeBVFunctionalVariation4D
end JanusFormal
