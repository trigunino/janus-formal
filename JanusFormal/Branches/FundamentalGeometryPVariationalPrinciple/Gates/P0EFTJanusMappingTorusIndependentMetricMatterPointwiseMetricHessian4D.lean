import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIndependentMetricMatterPointwiseMixedHessian4D

/-!
# Pointwise pure metric Hessian of the scalar matter action

For each of the eight scalar components, the sector metric is written in its
four-dimensional positive scale chart.  The scalar density is explicitly
`C²` there, so its second Fréchet derivative is a genuine symmetric Hessian.
The base first variation is identified with the derivative of the existing
metric-coupled Program-P density; no derivative identity is assumed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIndependentMetricMatterPointwiseMetricHessian4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusSmoothDiagonalInteraction4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMetricD9Variation4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D
open P0EFTJanusIndependentMatterMetricActionData4D
open P0EFTJanusMappingTorusIndependentMetricMatterPointwiseVariation4D
open P0EFTJanusMappingTorusIndependentMetricMatterIntegratedVariation4D
open P0EFTJanusMappingTorusIndependentMetricMatterPointwiseMixedHessian4D
open P0EFTJanusGlobalDiagonalLorentzRoot4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Use the canonical real scalar action throughout this gate. -/
local instance realNormedModule : Module Real Real := Semiring.toModule

/-- Metric-only direction embedded in the Robin-complete Program-P tangent. -/
def metricOnlyRobinCompleteVariation
    (direction : SmoothDiagonalMetricVariation period hPeriod) :
    ProgramPRobinCompleteVariation4D period hPeriod :=
  includeCompleteVariation period hPeriod
    (independentCompleteVariation period hPeriod
      (metricOnlyIndependentVariation period hPeriod direction))

/-- Positive four-scale point selected by the matter sector. -/
def independentMatterScale
    (fields : IndependentFields period hPeriod) (sector : Fin 2)
    (point : EffectiveQuotient period hPeriod) : Coefficients4 :=
  if sector = 0 then plusScaleField period hPeriod fields.metrics point
  else minusScaleField period hPeriod fields.metrics point

theorem independentMatterScale_pos
    (fields : IndependentFields period hPeriod) (sector : Fin 2)
    (point : EffectiveQuotient period hPeriod) (index : Fin 4) :
    0 < independentMatterScale period hPeriod fields sector point index := by
  by_cases hSector : sector = 0
  · simp [independentMatterScale, hSector,
      plusScaleField_pos period hPeriod fields.metrics point index]
  · simp [independentMatterScale, hSector,
      minusScaleField_pos period hPeriod fields.metrics point index]

/-- Tangent in the same scale chart induced by a logarithmic metric
direction. -/
def independentMatterScaleDirection
    (fields : IndependentFields period hPeriod)
    (direction : SmoothDiagonalMetricVariation period hPeriod)
    (sector : Fin 2) (point : EffectiveQuotient period hPeriod) :
    Coefficients4 :=
  if sector = 0 then
    (scaleVelocityAt period hPeriod fields.metrics direction 0 point).1
  else
    (scaleVelocityAt period hPeriod fields.metrics direction 0 point).2

/-- Finite-dimensional scalar density as a function of the four positive
metric scales, with the scalar jet held fixed. -/
def independentMatterScaleDensity
    (massSquared fieldValue : Real) (covector scale : Coefficients4) : Real :=
  (∏ index : Fin 4, scale index) *
    ((1 / 2 : Real) * ∑ index : Fin 4,
        signature index / scale index ^ 2 * covector index ^ 2 +
      massSquared / 2 * fieldValue ^ 2)

/-- The local scale-density function attached to one actual scalar component
and one spacetime point. -/
def independentMatterScaleDensityFunction
    (massSquared : Real) (fields : IndependentFields period hPeriod)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod) : Coefficients4 → Real :=
  independentMatterScaleDensity
    massSquared
    (independentMatterComponentFamily period hPeriod fields component point)
    (fun index => holonomicCovectorComponent period hPeriod
      (independentMatterComponentFamily period hPeriod fields component)
      point index)

/-- The finite-dimensional scale density is `C²` at every positive scale. -/
theorem independentMatterScaleDensity_contDiffAt
    (massSquared fieldValue : Real) (covector scale : Coefficients4)
    (hScale : ∀ index, scale index ≠ 0) :
    ContDiffAt Real 2
      (independentMatterScaleDensity massSquared fieldValue covector) scale := by
  unfold independentMatterScaleDensity
  apply ContDiffAt.mul
  · apply contDiffAt_prod
    intro index _
    exact contDiffAt_apply Real Real index scale
  · apply ContDiffAt.add
    · apply ContDiffAt.mul
      · exact contDiffAt_const
      · apply ContDiffAt.sum
        intro index _
        apply ContDiffAt.mul
        · apply ContDiffAt.div
          · exact contDiffAt_const
          · exact (contDiffAt_apply Real Real index scale).pow 2
          · exact pow_ne_zero 2 (hScale index)
        · exact contDiffAt_const
    · exact contDiffAt_const

/-- The original scalar density is exactly the positive-scale density at the
sector scale selected from the same configuration. -/
theorem globalHolonomicScalarDensity_eq_independentMatterScaleDensity
    (massSquared : Real) (fields : IndependentFields period hPeriod)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod) :
    globalHolonomicScalarDensity period hPeriod massSquared
        (independentMatterMagnitude period hPeriod fields component.1)
        (independentMatterComponentFamily period hPeriod fields component)
        point =
      independentMatterScaleDensityFunction period hPeriod massSquared fields
        component point
        (independentMatterScale period hPeriod fields component.1 point) := by
  have hVolume :
      Real.sqrt (∏ index : Fin 4,
        independentMatterMagnitude period hPeriod fields component.1 point index) =
        ∏ index : Fin 4,
          independentMatterScale period hPeriod fields component.1 point index := by
    rw [Real.sqrt_prod Finset.univ]
    · apply Finset.prod_congr rfl
      intro index _
      by_cases hSector : component.1 = 0
      · simp [independentMatterMagnitude, independentMatterScale, hSector,
          plusScaleField, positiveSquareRootField]
      · simp [independentMatterMagnitude, independentMatterScale, hSector,
          minusScaleField, positiveSquareRootField]
    · intro index _
      exact le_of_lt
        (independentMatterMagnitude_pos period hPeriod fields component.1 point
          index)
  have hScaleSq (index : Fin 4) :
      independentMatterScale period hPeriod fields component.1 point index ^ 2 =
        independentMatterMagnitude period hPeriod fields component.1 point
          index := by
    by_cases hSector : component.1 = 0
    · simp [independentMatterMagnitude, independentMatterScale, hSector,
        plusScaleField, positiveSquareRootField,
        Real.sq_sqrt (le_of_lt (fields.metrics.plus_pos point index))]
    · simp [independentMatterMagnitude, independentMatterScale, hSector,
        minusScaleField, positiveSquareRootField,
        Real.sq_sqrt (le_of_lt (fields.metrics.minus_pos point index))]
  unfold globalHolonomicScalarDensity diagonalMetricVolumeDensity
    diagonalHolonomicKineticDensity independentMatterScaleDensityFunction
    independentMatterScaleDensity
  rw [hVolume]
  simp_rw [hScaleSq]

/-- The genuine exponential metric curve has the expected tangent in the
positive scale chart. -/
theorem independentMatterScale_metricOnlyCurve_hasDerivAt
    (fields : IndependentFields period hPeriod)
    (direction : SmoothDiagonalMetricVariation period hPeriod)
    (sector : Fin 2) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun parameter =>
        independentMatterScale period hPeriod
          (independentFieldCurve period hPeriod fields
            (metricOnlyIndependentVariation period hPeriod direction) parameter)
          sector point)
      (independentMatterScaleDirection period hPeriod fields direction sector
        point)
      0 := by
  by_cases hSector : sector = 0
  · have hCurve :
        (fun parameter =>
          independentMatterScale period hPeriod
            (independentFieldCurve period hPeriod fields
              (metricOnlyIndependentVariation period hPeriod direction) parameter)
            sector point) =
          (fun parameter =>
            positiveScaleCurve period hPeriod
              (plusScaleField period hPeriod fields.metrics)
              direction.plusLogDirection parameter point) := by
        funext parameter
        have hPair := scalePairField_metricCurve period hPeriod fields.metrics
          direction parameter point
        simpa [independentMatterScale, hSector, independentFieldCurve,
          metricOnlyIndependentVariation, scalePairField] using
          congrArg Prod.fst hPair
    rw [hCurve]
    simpa [independentMatterScaleDirection, hSector, scaleVelocityAt] using
      positiveScaleCurve_hasDerivAt period hPeriod
        (plusScaleField period hPeriod fields.metrics)
        direction.plusLogDirection 0 point
  · have hCurve :
        (fun parameter =>
          independentMatterScale period hPeriod
            (independentFieldCurve period hPeriod fields
              (metricOnlyIndependentVariation period hPeriod direction) parameter)
            sector point) =
          (fun parameter =>
            positiveScaleCurve period hPeriod
              (minusScaleField period hPeriod fields.metrics)
              direction.minusLogDirection parameter point) := by
        funext parameter
        have hPair := scalePairField_metricCurve period hPeriod fields.metrics
          direction parameter point
        simpa [independentMatterScale, hSector, independentFieldCurve,
          metricOnlyIndependentVariation, scalePairField] using
          congrArg Prod.snd hPair
    rw [hCurve]
    simpa [independentMatterScaleDirection, hSector, scaleVelocityAt] using
      positiveScaleCurve_hasDerivAt period hPeriod
        (minusScaleField period hPeriod fields.metrics)
        direction.minusLogDirection 0 point

/-- Affine curve in the positive scale chart generated by the second metric
direction. -/
def independentMatterMetricScaleCurve
    (fields : IndependentFields period hPeriod)
    (direction : SmoothDiagonalMetricVariation period hPeriod)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod)
    (parameter : Real) : Coefficients4 :=
  independentMatterScale period hPeriod fields component.1 point +
    parameter • independentMatterScaleDirection period hPeriod fields direction
      component.1 point

@[simp] theorem independentMatterMetricScaleCurve_zero
    (fields : IndependentFields period hPeriod)
    (direction : SmoothDiagonalMetricVariation period hPeriod)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod) :
    independentMatterMetricScaleCurve period hPeriod fields direction component
        point 0 =
      independentMatterScale period hPeriod fields component.1 point := by
  simp [independentMatterMetricScaleCurve]

/-- First scale-chart derivative in one metric direction. -/
def independentMatterMetricScaleFirstVariation
    (massSquared : Real) (fields : IndependentFields period hPeriod)
    (direction : SmoothDiagonalMetricVariation period hPeriod)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod) : Real :=
  fderiv Real
      (independentMatterScaleDensityFunction period hPeriod massSquared fields
        component point)
      (independentMatterScale period hPeriod fields component.1 point)
      (independentMatterScaleDirection period hPeriod fields direction
        component.1 point)

/-- The scale-chart first variation is the metric-only derivative of the
existing Program-P scalar density. -/
theorem independentMetricMatterFirstVariationDensity_metricOnly_eq_scaleFirstVariation
    (massSquared : Real) (fields : IndependentFields period hPeriod)
    (direction : SmoothDiagonalMetricVariation period hPeriod)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod) :
    independentMetricMatterFirstVariationDensity period hPeriod massSquared fields
        (metricOnlyIndependentVariation period hPeriod direction) component point =
      independentMatterMetricScaleFirstVariation period hPeriod massSquared fields
        direction component point := by
  have hActual :=
    programPMetricMatterDensityCurve_hasDerivAt period hPeriod massSquared fields
      (metricOnlyRobinCompleteVariation period hPeriod direction) component point
  have hC2 : ContDiffAt Real 2
      (independentMatterScaleDensityFunction period hPeriod massSquared fields
        component point)
      (independentMatterScale period hPeriod fields component.1 point) :=
    independentMatterScaleDensity_contDiffAt
      (massSquared := massSquared)
      (fieldValue := independentMatterComponentFamily period hPeriod fields
        component point)
      (covector := fun index => holonomicCovectorComponent period hPeriod
        (independentMatterComponentFamily period hPeriod fields component)
        point index)
      (scale := independentMatterScale period hPeriod fields component.1 point)
      (fun index => ne_of_gt
        (independentMatterScale_pos period hPeriod fields component.1 point index))
  have hDensity : HasFDerivAt
      (independentMatterScaleDensityFunction period hPeriod massSquared fields
        component point)
      (fderiv Real
        (independentMatterScaleDensityFunction period hPeriod massSquared fields
          component point)
        (independentMatterScale period hPeriod fields component.1 point))
      (independentMatterScale period hPeriod fields component.1 point) :=
    (hC2.differentiableAt (by norm_num)).hasFDerivAt
  have hScale := independentMatterScale_metricOnlyCurve_hasDerivAt period hPeriod
    fields direction component.1 point
  have hDensityAtCurve : HasFDerivAt
      (independentMatterScaleDensityFunction period hPeriod massSquared fields
        component point)
      (fderiv Real
        (independentMatterScaleDensityFunction period hPeriod massSquared fields
          component point)
        (independentMatterScale period hPeriod fields component.1 point))
      (independentMatterScale period hPeriod
        (independentFieldCurve period hPeriod fields
          (metricOnlyIndependentVariation period hPeriod direction) 0)
        component.1 point) := by
    simpa only [independentFieldCurve_zero] using hDensity
  have hComposed := hDensityAtCurve.comp_hasDerivAt 0 hScale
  have hCurve :
      programPMetricMatterDensityCurve period hPeriod massSquared fields
          (metricOnlyRobinCompleteVariation period hPeriod direction) component
          point =
        fun parameter =>
          independentMatterScaleDensityFunction period hPeriod massSquared fields
            component point
            (independentMatterScale period hPeriod
              (independentFieldCurve period hPeriod fields
                (metricOnlyIndependentVariation period hPeriod direction)
                parameter)
              component.1 point) := by
    funext parameter
    unfold programPMetricMatterDensityCurve
    simp only [metricOnlyRobinCompleteVariation,
      includeCompleteVariation_complete, independentCompleteVariation_independent]
    rw [globalHolonomicScalarDensity_eq_independentMatterScaleDensity]
    unfold independentMatterScaleDensityFunction
    rw [independentMatterComponent_metricOnlyCurve]
  rw [hCurve] at hActual
  change HasDerivAt
    (fun parameter =>
      independentMatterScaleDensityFunction period hPeriod massSquared fields
        component point
        (independentMatterScale period hPeriod
          (independentFieldCurve period hPeriod fields
            (metricOnlyIndependentVariation period hPeriod direction) parameter)
          component.1 point))
    _ 0 at hComposed
  have hMapEquality := hActual.hasFDerivAt.unique hComposed.hasFDerivAt
  have hAtOne := congrArg
    (fun linearMap : Real →L[Real] Real => linearMap 1) hMapEquality
  simpa only [ContinuousLinearMap.toSpanSingleton_apply_one,
    metricOnlyRobinCompleteVariation, includeCompleteVariation_complete,
    independentCompleteVariation_independent,
    independentMatterMetricScaleFirstVariation] using hAtOne

/-- First derivative in the first direction evaluated along the affine scale
curve generated by the second direction. -/
def independentMatterMetricFirstVariationAlongSecond
    (massSquared : Real) (fields : IndependentFields period hPeriod)
    (first second : SmoothDiagonalMetricVariation period hPeriod)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod)
    (parameter : Real) : Real :=
  fderiv Real
      (independentMatterScaleDensityFunction period hPeriod massSquared fields
        component point)
      (independentMatterMetricScaleCurve period hPeriod fields second component
        point parameter)
      (independentMatterScaleDirection period hPeriod fields first component.1
        point)

@[simp] theorem independentMatterMetricFirstVariationAlongSecond_zero
    (massSquared : Real) (fields : IndependentFields period hPeriod)
    (first second : SmoothDiagonalMetricVariation period hPeriod)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod) :
    independentMatterMetricFirstVariationAlongSecond period hPeriod massSquared
        fields first second component point 0 =
      independentMatterMetricScaleFirstVariation period hPeriod massSquared
        fields first component point := by
  simp [independentMatterMetricFirstVariationAlongSecond,
    independentMatterMetricScaleFirstVariation]

/-- Genuine pure metric--metric Hessian density of the scalar matter action
in the same positive scale chart as Candidate A. -/
def independentMatterMetricHessianDensity
    (massSquared : Real) (fields : IndependentFields period hPeriod)
    (first second : SmoothDiagonalMetricVariation period hPeriod)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod) : Real :=
  fderiv Real
      (fderiv Real
        (independentMatterScaleDensityFunction period hPeriod massSquared fields
          component point))
      (independentMatterScale period hPeriod fields component.1 point)
      (independentMatterScaleDirection period hPeriod fields second component.1
        point)
      (independentMatterScaleDirection period hPeriod fields first component.1
        point)

/-- The pointwise pure metric Hessian is symmetric by `C²` regularity of the
explicit scalar density. -/
theorem independentMatterMetricHessianDensity_symmetric
    (massSquared : Real) (fields : IndependentFields period hPeriod)
    (first second : SmoothDiagonalMetricVariation period hPeriod)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod) :
    independentMatterMetricHessianDensity period hPeriod massSquared fields
        first second component point =
      independentMatterMetricHessianDensity period hPeriod massSquared fields
        second first component point := by
  have hC2 : ContDiffAt Real 2
      (independentMatterScaleDensityFunction period hPeriod massSquared fields
        component point)
      (independentMatterScale period hPeriod fields component.1 point) :=
    independentMatterScaleDensity_contDiffAt
      (massSquared := massSquared)
      (fieldValue := independentMatterComponentFamily period hPeriod fields
        component point)
      (covector := fun index => holonomicCovectorComponent period hPeriod
        (independentMatterComponentFamily period hPeriod fields component)
        point index)
      (scale := independentMatterScale period hPeriod fields component.1 point)
      (fun index => ne_of_gt
        (independentMatterScale_pos period hPeriod fields component.1 point
          index))
  exact (hC2.isSymmSndFDerivAt (by norm_num)).eq
    (independentMatterScaleDirection period hPeriod fields second component.1
      point)
    (independentMatterScaleDirection period hPeriod fields first component.1
      point)

/-- The first scale-chart variation differentiates to the displayed pure
metric Hessian whenever the affine scale curve remains positive. -/
theorem independentMatterMetricFirstVariationAlongSecond_hasDerivAt
    (massSquared : Real) (fields : IndependentFields period hPeriod)
    (first second : SmoothDiagonalMetricVariation period hPeriod)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod)
    (parameter : Real)
    (hCurve : independentMatterMetricScaleCurve period hPeriod fields second
      component point parameter ∈ positiveMagnitudeDomain) :
    HasDerivAt
      (fun varied =>
        (fderiv Real
          (independentMatterScaleDensityFunction period hPeriod massSquared fields
            component point)
          (independentMatterMetricScaleCurve period hPeriod fields second
            component point varied))
          (independentMatterScaleDirection period hPeriod fields first
            component.1 point))
      (fderiv Real
        (fderiv Real
          (independentMatterScaleDensityFunction period hPeriod massSquared
            fields component point))
        (independentMatterMetricScaleCurve period hPeriod fields second component
          point parameter)
        (independentMatterScaleDirection period hPeriod fields second component.1
          point)
        (independentMatterScaleDirection period hPeriod fields first component.1
          point))
      parameter := by
  have hC2 : ContDiffAt Real 2
      (independentMatterScaleDensityFunction period hPeriod massSquared fields
        component point)
      (independentMatterMetricScaleCurve period hPeriod fields second component
        point parameter) :=
    independentMatterScaleDensity_contDiffAt
      (massSquared := massSquared)
      (fieldValue := independentMatterComponentFamily period hPeriod fields
        component point)
      (covector := fun index => holonomicCovectorComponent period hPeriod
        (independentMatterComponentFamily period hPeriod fields component)
        point index)
      (scale := independentMatterMetricScaleCurve period hPeriod fields second
        component point parameter)
      (fun index => ne_of_gt (hCurve index))
  have hGradientC1 : ContDiffAt Real 1
      (fderiv Real
        (independentMatterScaleDensityFunction period hPeriod massSquared fields
          component point))
      (independentMatterMetricScaleCurve period hPeriod fields second component
        point parameter) :=
    hC2.fderiv_right (by norm_num)
  have hGradient : HasFDerivAt
      (fderiv Real
        (independentMatterScaleDensityFunction period hPeriod massSquared fields
          component point))
      (fderiv Real
        (fderiv Real
          (independentMatterScaleDensityFunction period hPeriod massSquared fields
            component point))
        (independentMatterMetricScaleCurve period hPeriod fields second component
          point parameter))
      (independentMatterMetricScaleCurve period hPeriod fields second component
        point parameter) :=
    (hGradientC1.differentiableAt (by norm_num)).hasFDerivAt
  have hScaleCurve : HasDerivAt
      (independentMatterMetricScaleCurve period hPeriod fields second component
        point)
      (independentMatterScaleDirection period hPeriod fields second component.1
        point)
      parameter := by
    change HasDerivAt
      (fun varied =>
        independentMatterScale period hPeriod fields component.1 point +
          varied • independentMatterScaleDirection period hPeriod fields second
            component.1 point)
      (independentMatterScaleDirection period hPeriod fields second component.1
        point) parameter
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id (x := parameter)).smul_const
        (independentMatterScaleDirection period hPeriod fields second component.1
          point)).const_add
        (independentMatterScale period hPeriod fields component.1 point)
  have hComposite := hGradient.comp_hasDerivAt parameter hScaleCurve
  have hApplied := hComposite.clm_apply
    (hasDerivAt_const (x := parameter)
      (independentMatterScaleDirection period hPeriod fields first component.1
        point))
  simpa only [Function.comp_apply, map_zero, add_zero] using hApplied

/-- At the base scale, the preceding derivative is exactly the symmetric
pure metric Hessian density. -/
theorem independentMatterMetricFirstVariationAlongSecond_hasDerivAt_zero
    (massSquared : Real) (fields : IndependentFields period hPeriod)
    (first second : SmoothDiagonalMetricVariation period hPeriod)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun varied =>
        (fderiv Real
          (independentMatterScaleDensityFunction period hPeriod massSquared fields
            component point)
          (independentMatterMetricScaleCurve period hPeriod fields second
            component point varied))
          (independentMatterScaleDirection period hPeriod fields first
            component.1 point))
      (independentMatterMetricHessianDensity period hPeriod massSquared fields
        first second component point)
      0 := by
  have hDerivative :=
    independentMatterMetricFirstVariationAlongSecond_hasDerivAt period hPeriod
      massSquared fields first second component point 0 (by
        intro index
        simpa using independentMatterScale_pos period hPeriod fields component.1
          point index)
  simpa only [independentMatterMetricScaleCurve_zero,
    independentMatterMetricHessianDensity] using hDerivative

end

end P0EFTJanusMappingTorusIndependentMetricMatterPointwiseMetricHessian4D
end JanusFormal
