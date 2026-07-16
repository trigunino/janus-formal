import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothFieldLinearSpace4D

/-!
# Functional chain of the global induced-field package

Every independent coefficient sector follows one smooth affine curve, while
the positive diagonal metrics follow the global exponential curve.  The two
metric matrices, the principal root and both matter traces are then varied
only through `induce`; no second independent copy of an induced field is used.
The resulting five pointwise derivatives are exact on the actual D8 quotient
and throat.  This remains the selected fixed-frame diagonal sector.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusInducedFieldVariation4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Frobenius
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusGlobalDiagonalLorentzRoot4D

variable (period : Real) (hPeriod : Not (period = 0))

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Fix the normed real module selected by derivative composition. -/
local instance realNormedModule : Module Real Real :=
  (RCLike.toInnerProductSpaceReal : InnerProductSpace Real Real).toModule

/-- Directions for every independent field. Only metrics and matter feed the
induced package, while the remaining directions certify zero cross-response. -/
structure IndependentFieldVariation where
  metrics : SmoothDiagonalMetricVariation period hPeriod
  matter : SmoothQuotientField period hPeriod MatterFiber ×
    SmoothQuotientField period hPeriod MatterFiber
  gauge : SmoothQuotientField period hPeriod GaugeFiber ×
    SmoothQuotientField period hPeriod GaugeFiber
  ghosts : SmoothQuotientField period hPeriod GhostFiber ×
    SmoothQuotientField period hPeriod GhostFiber
  auxiliaries : SmoothQuotientField period hPeriod AuxiliaryFiber ×
    SmoothQuotientField period hPeriod AuxiliaryFiber
  llAuxMetric : SmoothThroatField period hPeriod LLMetricFiber
  llMeasure : SmoothThroatField period hPeriod Real
  llField : SmoothThroatField period hPeriod LLFieldFiber

/-- One simultaneous curve of all independent fields. -/
def independentFieldCurve
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (parameter : Real) : IndependentFields period hPeriod where
  metrics := metricCurve period hPeriod fields.metrics variation.metrics parameter
  matter :=
    (fields.matter.1 + parameter • variation.matter.1,
      fields.matter.2 + parameter • variation.matter.2)
  gauge :=
    (fields.gauge.1 + parameter • variation.gauge.1,
      fields.gauge.2 + parameter • variation.gauge.2)
  ghosts :=
    (fields.ghosts.1 + parameter • variation.ghosts.1,
      fields.ghosts.2 + parameter • variation.ghosts.2)
  auxiliaries :=
    (fields.auxiliaries.1 + parameter • variation.auxiliaries.1,
      fields.auxiliaries.2 + parameter • variation.auxiliaries.2)
  llAuxMetric := fields.llAuxMetric + parameter • variation.llAuxMetric
  llMeasure := fields.llMeasure + parameter • variation.llMeasure
  llField := fields.llField + parameter • variation.llField

@[simp]
theorem independentFieldCurve_zero
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod) :
    independentFieldCurve period hPeriod fields variation 0 = fields := by
  cases fields
  simp [independentFieldCurve, metricCurve_zero]

/-- Velocity of the two independent metric-magnitude fields. -/
def metricMagnitudeVelocityAt
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    CoefficientPair :=
  (fun i => 2 *
      (metricCurve period hPeriod fields.metrics variation.metrics parameter).plusMagnitude
        point i * variation.metrics.plusLogDirection point i,
    fun i => 2 *
      (metricCurve period hPeriod fields.metrics variation.metrics parameter).minusMagnitude
        point i * variation.metrics.minusLogDirection point i)

theorem plusMagnitude_curve_hasDerivAt
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied =>
        (independentFieldCurve period hPeriod fields variation varied).metrics.plusMagnitude point)
      (metricMagnitudeVelocityAt period hPeriod fields variation parameter point).1
      parameter := by
  rw [hasDerivAt_pi]
  intro i
  have hScale := positiveScaleCurve_hasDerivAt period hPeriod
    (plusScaleField period hPeriod fields.metrics)
    variation.metrics.plusLogDirection parameter point
  have hCoordinate := (hasDerivAt_pi.mp hScale) i
  have hSquared :
      HasDerivAt
        (fun varied => (positiveScaleCurve period hPeriod
          (plusScaleField period hPeriod fields.metrics)
          variation.metrics.plusLogDirection varied point i) ^ 2)
        (2 * (positiveScaleCurve period hPeriod
          (plusScaleField period hPeriod fields.metrics)
          variation.metrics.plusLogDirection parameter point i) ^ 2 *
            variation.metrics.plusLogDirection point i)
        parameter := by
    convert hCoordinate.pow 2 using 1 <;> try rfl
    ring
  simpa [independentFieldCurve, metricCurve, squaredMagnitudeField,
    metricMagnitudeVelocityAt] using hSquared

theorem minusMagnitude_curve_hasDerivAt
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied =>
        (independentFieldCurve period hPeriod fields variation varied).metrics.minusMagnitude point)
      (metricMagnitudeVelocityAt period hPeriod fields variation parameter point).2
      parameter := by
  rw [hasDerivAt_pi]
  intro i
  have hScale := positiveScaleCurve_hasDerivAt period hPeriod
    (minusScaleField period hPeriod fields.metrics)
    variation.metrics.minusLogDirection parameter point
  have hCoordinate := (hasDerivAt_pi.mp hScale) i
  have hSquared :
      HasDerivAt
        (fun varied => (positiveScaleCurve period hPeriod
          (minusScaleField period hPeriod fields.metrics)
          variation.metrics.minusLogDirection varied point i) ^ 2)
        (2 * (positiveScaleCurve period hPeriod
          (minusScaleField period hPeriod fields.metrics)
          variation.metrics.minusLogDirection parameter point i) ^ 2 *
            variation.metrics.minusLogDirection point i)
        parameter := by
    convert hCoordinate.pow 2 using 1 <;> try rfl
    ring
  simpa [independentFieldCurve, metricCurve, squaredMagnitudeField,
    metricMagnitudeVelocityAt] using hSquared

theorem coefficientPair_curve_hasDerivAt
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied => coefficientPairAt period hPeriod
        (independentFieldCurve period hPeriod fields variation varied).metrics point)
      (metricMagnitudeVelocityAt period hPeriod fields variation parameter point)
      parameter := by
  exact (plusMagnitude_curve_hasDerivAt period hPeriod fields variation parameter point).prodMk
    (minusMagnitude_curve_hasDerivAt period hPeriod fields variation parameter point)

/-- Exact componentwise derivative of the induced plus metric matrix. -/
theorem induced_plusMetricEntry_curve_hasDerivAt
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) (i j : Fin 4) :
    HasDerivAt
      (fun varied => (induce period hPeriod
        (independentFieldCurve period hPeriod fields variation varied)).plusMetric point i j)
      (lorentzMetric
        (metricMagnitudeVelocityAt period hPeriod fields variation parameter point).1 i j)
      parameter := by
  by_cases hij : i = j
  · subst j
    have hCoordinate := (hasDerivAt_pi.mp
      (plusMagnitude_curve_hasDerivAt period hPeriod fields variation parameter point)) i
    simpa [induce, lorentzMetric] using hCoordinate.const_mul (signature i)
  · have hConstant :
        (fun varied => (induce period hPeriod
          (independentFieldCurve period hPeriod fields variation varied)).plusMetric point i j) =
          (fun _ : Real => 0) := by
        funext varied
        simp [induce, lorentzMetric, hij]
    rw [hConstant]
    simpa [lorentzMetric, hij] using hasDerivAt_const (x := parameter) (c := (0 : Real))

/-- Exact componentwise derivative of the induced minus metric matrix. -/
theorem induced_minusMetricEntry_curve_hasDerivAt
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) (i j : Fin 4) :
    HasDerivAt
      (fun varied => (induce period hPeriod
        (independentFieldCurve period hPeriod fields variation varied)).minusMetric point i j)
      (lorentzMetric
        (metricMagnitudeVelocityAt period hPeriod fields variation parameter point).2 i j)
      parameter := by
  by_cases hij : i = j
  · subst j
    have hCoordinate := (hasDerivAt_pi.mp
      (minusMagnitude_curve_hasDerivAt period hPeriod fields variation parameter point)) i
    simpa [induce, lorentzMetric] using hCoordinate.const_mul (signature i)
  · have hConstant :
        (fun varied => (induce period hPeriod
          (independentFieldCurve period hPeriod fields variation varied)).minusMetric point i j) =
          (fun _ : Real => 0) := by
        funext varied
        simp [induce, lorentzMetric, hij]
    rw [hConstant]
    simpa [lorentzMetric, hij] using hasDerivAt_const (x := parameter) (c := (0 : Real))

/-- Matrix-entry evaluation for the Frobenius norm. -/
def matrixEntryCLM (i j : Fin 4) : Matrix4 →L[Real] Real :=
  LinearMap.toContinuousLinearMap
    { toFun := fun matrix => matrix i j
      map_add' := by intro first second; rfl
      map_smul' := by intro scalar matrix; rfl }

@[simp]
theorem matrixEntryCLM_apply (i j : Fin 4) (matrix : Matrix4) :
    matrixEntryCLM i j matrix = matrix i j := rfl

/-- The induced root entry is definitionally the global principal-root entry
along the same metric curve. -/
theorem induced_principalRootEntry_curve_eq
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) (i j : Fin 4) :
    (induce period hPeriod
      (independentFieldCurve period hPeriod fields variation parameter)).principalRoot point i j =
      principalRoot (coefficientPairAt period hPeriod
        (independentFieldCurve period hPeriod fields variation parameter).metrics point) i j := by
  rfl

/-- Exact derivative of every entry of the unique induced principal root,
written through the entry continuous-linear map to fix the normed instances. -/
theorem induced_principalRootEntryComposite_curve_hasDerivAt
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (parameter : Real) (point : EffectiveQuotient period hPeriod) (i j : Fin 4) :
    HasDerivAt
      ((matrixEntryCLM i j) ∘ principalRoot ∘
        fun varied => coefficientPairAt period hPeriod
          (independentFieldCurve period hPeriod fields variation varied).metrics point)
      ((matrixEntryCLM i j) ((principalRootVariation
          (coefficientPairAt period hPeriod
            (independentFieldCurve period hPeriod fields variation parameter).metrics point))
        (metricMagnitudeVelocityAt period hPeriod fields variation parameter point)))
      parameter := by
  have hPair := coefficientPair_curve_hasDerivAt period hPeriod fields variation parameter point
  have hDomain := coefficientPairAt_mem_domain period hPeriod
    (independentFieldCurve period hPeriod fields variation parameter).metrics point
  have hRoot := (principalRoot_hasFDerivAt _ hDomain).comp_hasDerivAt parameter hPair
  exact (matrixEntryCLM i j).hasFDerivAt.comp_hasDerivAt parameter hRoot

/-- The plus matter trace has the exact affine response of the plus matter
field and no response to any other independent direction. -/
theorem induced_plusMatterTraceEntry_curve_eq
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (parameter : Real) (point : EffectiveThroat period hPeriod) (i : Fin 4) :
    (induce period hPeriod
      (independentFieldCurve period hPeriod fields variation parameter)).plusMatterTrace point i =
      fields.matter.1 (fixedThroatQuotientInclusion period hPeriod point) i +
        parameter * variation.matter.1
          (fixedThroatQuotientInclusion period hPeriod point) i := by
  rfl

/-- The minus matter trace has the exact affine response of the minus matter
field and no response to any other independent direction. -/
theorem induced_minusMatterTraceEntry_curve_eq
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (parameter : Real) (point : EffectiveThroat period hPeriod) (i : Fin 4) :
    (induce period hPeriod
      (independentFieldCurve period hPeriod fields variation parameter)).minusMatterTrace point i =
      fields.matter.2 (fixedThroatQuotientInclusion period hPeriod point) i +
        parameter * variation.matter.2
          (fixedThroatQuotientInclusion period hPeriod point) i := by
  rfl

/-- Varying gauge, ghost, auxiliary or LL fields cannot change the induced
package when the metric and matter directions vanish. -/
theorem induced_cross_response_zero
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (hMetricPlus : variation.metrics.plusLogDirection = 0)
    (hMetricMinus : variation.metrics.minusLogDirection = 0)
    (hMatterPlus : variation.matter.1 = 0)
    (hMatterMinus : variation.matter.2 = 0)
    (parameter : Real) :
    induce period hPeriod (independentFieldCurve period hPeriod fields variation parameter) =
      induce period hPeriod fields := by
  have hMetrics :
      metricCurve period hPeriod fields.metrics variation.metrics parameter =
        fields.metrics := by
    apply SmoothPositiveDiagonalMetricPair.ext
    · apply SmoothQuotientField.ext period hPeriod Coefficients4
      intro point
      funext i
      change (positiveScaleCurve period hPeriod
        (plusScaleField period hPeriod fields.metrics)
        variation.metrics.plusLogDirection parameter point i) ^ 2 =
          fields.metrics.plusMagnitude point i
      rw [hMetricPlus]
      change (Real.sqrt (fields.metrics.plusMagnitude point i) *
        Real.exp (parameter * (0 : Real))) ^ 2 = fields.metrics.plusMagnitude point i
      rw [mul_zero, Real.exp_zero, mul_one,
        Real.sq_sqrt (le_of_lt (fields.metrics.plus_pos point i))]
    · apply SmoothQuotientField.ext period hPeriod Coefficients4
      intro point
      funext i
      change (positiveScaleCurve period hPeriod
        (minusScaleField period hPeriod fields.metrics)
        variation.metrics.minusLogDirection parameter point i) ^ 2 =
          fields.metrics.minusMagnitude point i
      rw [hMetricMinus]
      change (Real.sqrt (fields.metrics.minusMagnitude point i) *
        Real.exp (parameter * (0 : Real))) ^ 2 = fields.metrics.minusMagnitude point i
      rw [mul_zero, Real.exp_zero, mul_one,
        Real.sq_sqrt (le_of_lt (fields.metrics.minus_pos point i))]
  unfold induce
  dsimp only [independentFieldCurve]
  rw [hMetrics, hMatterPlus, hMatterMinus]
  simp

end

end P0EFTJanusMappingTorusInducedFieldVariation4D
end JanusFormal
