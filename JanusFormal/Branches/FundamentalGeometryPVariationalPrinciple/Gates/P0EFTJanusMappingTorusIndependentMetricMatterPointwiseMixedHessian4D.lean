import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIndependentMetricMatterIntegratedVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusCommonMetricD9Variation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIndependentCompleteVariationEmbedding4D

/-!
# Pointwise metric--matter mixed second variation on the common fields

For one of the eight actual scalar components, this gate first identifies the
matter-only Euler density with the derivative of the existing simultaneous
Program-P density.  It then differentiates that Euler density along the
genuine exponential diagonal-metric curve and obtains an explicit mixed term.

Thus the final statement is a true iterated derivative of the same pointwise
density.  It is not an integrated Hessian: differentiation under the integral,
the Candidate-A metric interaction, EH, Maxwell and ghosts remain absent.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIndependentMetricMatterPointwiseMixedHessian4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCandidateAFunctionalVariation4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarVariation4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarWeakJacobiRiesz4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusCommonMetricD9Variation4D
open P0EFTJanusProgramPCommonLLActionVariation4D
open P0EFTJanusIndependentMatterMetricActionData4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusIndependentCompleteVariationEmbedding4D
open P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D
open P0EFTJanusMappingTorusIndependentMetricMatterPointwiseVariation4D
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

/-- Matter-only direction embedded in the Robin-complete Program-P tangent. -/
def matterOnlyRobinCompleteVariation
    (direction : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber) :
    ProgramPRobinCompleteVariation4D period hPeriod :=
  includeCompleteVariation period hPeriod
    (independentCompleteVariation period hPeriod
      (matterOnlyIndependentVariation period hPeriod direction))

/-- Pointwise matter Euler integrand at a fixed sector-selected metric. -/
def independentMatterEulerLagrangian
    (massSquared : Real)
    (fields : IndependentFields period hPeriod)
    (matterDirection : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod) : Real :=
  (1 / 2 : Real) * (∑ index : Fin 4,
      (signature index /
          independentMatterMagnitude period hPeriod fields component.1 point index) *
        (2 * holonomicCovectorComponent period hPeriod
            (independentMatterComponentFamily period hPeriod fields component)
            point index *
          holonomicCovectorComponent period hPeriod
            (matterVariationComponentFamily period hPeriod matterDirection component)
            point index)) +
    massSquared *
      independentMatterComponentFamily period hPeriod fields component point *
      matterVariationComponentFamily period hPeriod matterDirection component point

/-- The exact matter-only first variation of the actual pointwise density. -/
def independentMatterEulerDensity
    (massSquared : Real)
    (fields : IndependentFields period hPeriod)
    (matterDirection : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod) : Real :=
  diagonalMetricVolumeDensity period hPeriod
      (independentMatterMagnitude period hPeriod fields component.1) point *
    independentMatterEulerLagrangian period hPeriod massSquared fields
      matterDirection component point

/-- A matter-only common direction reduces the simultaneous first-variation
formula to the usual matter Euler density, with the metric held fixed. -/
theorem independentMetricMatterFirstVariationDensity_matterOnly
    (massSquared : Real)
    (fields : IndependentFields period hPeriod)
    (matterDirection : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod) :
    independentMetricMatterFirstVariationDensity period hPeriod massSquared fields
        (matterOnlyIndependentVariation period hPeriod matterDirection)
        component point =
      independentMatterEulerDensity period hPeriod massSquared fields
        matterDirection component point := by
  have hMagnitudeVelocity (sector : Fin 2) (index : Fin 4) :
      independentMatterMagnitudeVelocityAt period hPeriod fields
          (matterOnlyIndependentVariation period hPeriod matterDirection)
          sector point index = 0 := by
    by_cases hSector : sector = 0
    · simp [independentMatterMagnitudeVelocityAt, hSector,
        metricMagnitudeVelocityAt, matterOnlyIndependentVariation,
        zeroSmoothDiagonalMetricVariation]
      right
      rfl
    · simp [independentMatterMagnitudeVelocityAt, hSector,
        metricMagnitudeVelocityAt, matterOnlyIndependentVariation,
        zeroSmoothDiagonalMetricVariation]
      right
      rfl
  simp only [independentMetricMatterFirstVariationDensity,
    independentMatterEulerDensity, independentMatterEulerLagrangian,
    independentMatterVolumeVelocity, independentMatterMagnitudeProductVelocity,
    independentMatterKineticVelocity]
  simp_rw [hMagnitudeVelocity]
  simp [matterOnlyIndependentVariation]

/-- The Euler density above is genuinely the first derivative of the same
pointwise Program-P metric--matter density along a matter-only direction. -/
theorem programPMetricMatterDensityCurve_matterOnly_hasDerivAt
    (massSquared : Real)
    (fields : IndependentFields period hPeriod)
    (matterDirection : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (programPMetricMatterDensityCurve period hPeriod massSquared fields
        (matterOnlyRobinCompleteVariation period hPeriod matterDirection)
        component point)
      (independentMatterEulerDensity period hPeriod massSquared fields
        matterDirection component point) 0 := by
  have hDerivative :=
    programPMetricMatterDensityCurve_hasDerivAt period hPeriod massSquared fields
      (matterOnlyRobinCompleteVariation period hPeriod matterDirection)
      component point
  simpa [matterOnlyRobinCompleteVariation,
    independentMetricMatterFirstVariationDensity_matterOnly] using hDerivative

/-- Metric response of the kinetic part of the matter Euler integrand. -/
def independentMetricMatterKineticMixedResponse
    (fields : IndependentFields period hPeriod)
    (metricDirection : SmoothDiagonalMetricVariation period hPeriod)
    (matterDirection : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod) : Real :=
  (1 / 2 : Real) * ∑ index : Fin 4,
    (-(signature index *
          independentMatterMagnitudeVelocityAt period hPeriod fields
            (metricOnlyIndependentVariation period hPeriod metricDirection)
            component.1 point index) /
        (independentMatterMagnitude period hPeriod fields component.1 point index) ^ 2) *
      (2 * holonomicCovectorComponent period hPeriod
          (independentMatterComponentFamily period hPeriod fields component)
          point index *
        holonomicCovectorComponent period hPeriod
          (matterVariationComponentFamily period hPeriod matterDirection component)
          point index)

/-- Explicit pointwise mixed metric--matter second-variation density. -/
def independentMetricMatterMixedDensity
    (massSquared : Real)
    (fields : IndependentFields period hPeriod)
    (metricDirection : SmoothDiagonalMetricVariation period hPeriod)
    (matterDirection : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod) : Real :=
  independentMatterVolumeVelocity period hPeriod fields
      (metricOnlyIndependentVariation period hPeriod metricDirection)
      component.1 point *
    independentMatterEulerLagrangian period hPeriod massSquared fields
      matterDirection component point +
  diagonalMetricVolumeDensity period hPeriod
      (independentMatterMagnitude period hPeriod fields component.1) point *
    independentMetricMatterKineticMixedResponse period hPeriod fields
      metricDirection matterDirection component point

private theorem independentMatterVolume_metricOnlyCurve_hasDerivAt
    (fields : IndependentFields period hPeriod)
    (metricDirection : SmoothDiagonalMetricVariation period hPeriod)
    (sector : Fin 2) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun parameter ↦
        diagonalMetricVolumeDensity period hPeriod
          (independentMatterMagnitude period hPeriod
            (independentFieldCurve period hPeriod fields
              (metricOnlyIndependentVariation period hPeriod metricDirection)
              parameter) sector) point)
      (independentMatterVolumeVelocity period hPeriod fields
        (metricOnlyIndependentVariation period hPeriod metricDirection)
        sector point) 0 := by
  let variation := metricOnlyIndependentVariation period hPeriod metricDirection
  have hProduct : HasDerivAt
      (fun parameter ↦ ∏ index : Fin 4,
        independentMatterMagnitude period hPeriod
          (independentFieldCurve period hPeriod fields variation parameter)
          sector point index)
      (independentMatterMagnitudeProductVelocity period hPeriod fields variation
        sector point) 0 := by
    have hRaw := HasDerivAt.fun_finsetProd (u := Finset.univ)
      (f := fun index parameter ↦
        independentMatterMagnitude period hPeriod
          (independentFieldCurve period hPeriod fields variation parameter)
          sector point index)
      (f' := fun index ↦
        independentMatterMagnitudeVelocityAt period hPeriod fields variation
          sector point index)
      (fun index _ ↦ (hasDerivAt_pi.mp
        (independentMatterMagnitude_curve_hasDerivAt period hPeriod fields
          variation sector point)) index)
    simpa [independentMatterMagnitudeProductVelocity,
      independentFieldCurve_zero] using hRaw
  have hProductPos : 0 < ∏ index : Fin 4,
      independentMatterMagnitude period hPeriod fields sector point index :=
    Finset.prod_pos fun index _ ↦
      independentMatterMagnitude_pos period hPeriod fields sector point index
  have hSqrt := hProduct.sqrt (by
    simpa [independentFieldCurve_zero] using ne_of_gt hProductPos)
  simpa [diagonalMetricVolumeDensity, independentMatterVolumeVelocity,
    variation, independentFieldCurve_zero] using hSqrt

/-- Metric-only curves leave every actual matter component fixed. -/
theorem independentMatterComponent_metricOnlyCurve
    (fields : IndependentFields period hPeriod)
    (metricDirection : SmoothDiagonalMetricVariation period hPeriod)
    (component : MatterComponentIndex) (parameter : Real) :
    independentMatterComponentFamily period hPeriod
        (independentFieldCurve period hPeriod fields
          (metricOnlyIndependentVariation period hPeriod metricDirection)
          parameter) component =
      independentMatterComponentFamily period hPeriod fields component := by
  have hMatterVariation :
      matterVariationComponentFamily period hPeriod
          (metricOnlyIndependentVariation period hPeriod metricDirection).matter =
        0 := by
    change matterVariationComponentFamily period hPeriod
      (0 : SmoothQuotientField period hPeriod MatterFiber ×
        SmoothQuotientField period hPeriod MatterFiber) = 0
    funext currentComponent
    apply SmoothQuotientField.ext period hPeriod Real
    intro currentPoint
    unfold matterVariationComponentFamily
    by_cases hSector : currentComponent.1 = 0
    · simp only [hSector, if_true]
      exact map_zero (EuclideanSpace.proj currentComponent.2)
    · simp only [hSector, if_false]
      exact map_zero (EuclideanSpace.proj currentComponent.2)
  rw [independentMatterComponent_curve_eq_affine]
  rw [hMatterVariation]
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  simp [scalarAffineCurve]

/-- The pointwise matter Euler density has the displayed derivative along the
true exponential diagonal-metric curve. -/
theorem independentMatterEulerDensity_metricOnlyCurve_hasDerivAt
    (massSquared : Real)
    (fields : IndependentFields period hPeriod)
    (metricDirection : SmoothDiagonalMetricVariation period hPeriod)
    (matterDirection : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun parameter ↦
        independentMatterEulerDensity period hPeriod massSquared
          (independentFieldCurve period hPeriod fields
            (metricOnlyIndependentVariation period hPeriod metricDirection)
            parameter)
          matterDirection component point)
      (independentMetricMatterMixedDensity period hPeriod massSquared fields
        metricDirection matterDirection component point) 0 := by
  let variation := metricOnlyIndependentVariation period hPeriod metricDirection
  let field := independentMatterComponentFamily period hPeriod fields component
  let test := matterVariationComponentFamily period hPeriod matterDirection component
  have hVolume := independentMatterVolume_metricOnlyCurve_hasDerivAt period hPeriod
    fields metricDirection component.1 point
  have hKinetic : HasDerivAt
      (fun parameter ↦ (1 / 2 : Real) * ∑ index : Fin 4,
        (signature index /
            independentMatterMagnitude period hPeriod
              (independentFieldCurve period hPeriod fields variation parameter)
              component.1 point index) *
          (2 * holonomicCovectorComponent period hPeriod
              (independentMatterComponentFamily period hPeriod
                (independentFieldCurve period hPeriod fields variation parameter)
                component) point index *
            holonomicCovectorComponent period hPeriod test point index))
      (independentMetricMatterKineticMixedResponse period hPeriod fields
        metricDirection matterDirection component point) 0 := by
    have hSum : HasDerivAt
        (fun parameter ↦ ∑ index : Fin 4,
          (signature index /
              independentMatterMagnitude period hPeriod
                (independentFieldCurve period hPeriod fields variation parameter)
                component.1 point index) *
            (2 * holonomicCovectorComponent period hPeriod
                (independentMatterComponentFamily period hPeriod
                  (independentFieldCurve period hPeriod fields variation parameter)
                  component) point index *
              holonomicCovectorComponent period hPeriod test point index))
        (∑ index : Fin 4,
          (-(signature index *
                independentMatterMagnitudeVelocityAt period hPeriod fields
                  variation component.1 point index) /
              (independentMatterMagnitude period hPeriod fields component.1 point
                index) ^ 2) *
            (2 * holonomicCovectorComponent period hPeriod field point index *
              holonomicCovectorComponent period hPeriod test point index)) 0 := by
      apply HasDerivAt.fun_sum
      intro index _
      have hMagnitude := (hasDerivAt_pi.mp
        (independentMatterMagnitude_curve_hasDerivAt period hPeriod fields
          variation component.1 point)) index
      have hMagnitudeNe :
          independentMatterMagnitude period hPeriod fields component.1 point index ≠
            0 := ne_of_gt (independentMatterMagnitude_pos period hPeriod fields
              component.1 point index)
      have hCoefficient :=
        (hasDerivAt_const (x := (0 : Real)) (c := signature index)).div hMagnitude
          (by simpa [independentFieldCurve_zero] using hMagnitudeNe)
      have hCovector : HasDerivAt
          (fun parameter ↦ holonomicCovectorComponent period hPeriod
            (independentMatterComponentFamily period hPeriod
              (independentFieldCurve period hPeriod fields variation parameter)
              component) point index) 0 0 := by
        have hCurve :
            (fun parameter ↦ holonomicCovectorComponent period hPeriod
              (independentMatterComponentFamily period hPeriod
                (independentFieldCurve period hPeriod fields variation parameter)
                component) point index) =
              (fun _ : Real ↦ holonomicCovectorComponent period hPeriod field
                point index) := by
          funext parameter
          rw [independentMatterComponent_metricOnlyCurve]
        rw [hCurve]
        exact hasDerivAt_const (x := (0 : Real))
          (c := holonomicCovectorComponent period hPeriod field point index)
      have hTerm := hCoefficient.mul
        ((hCovector.const_mul 2).mul_const
          (holonomicCovectorComponent period hPeriod test point index))
      refine hTerm.congr_deriv ?_
      simp [field, variation, independentFieldCurve_zero]
    simpa [independentMetricMatterKineticMixedResponse, variation, field, test]
      using hSum.const_mul (1 / 2 : Real)
  have hPotential : HasDerivAt
      (fun parameter ↦ massSquared *
        independentMatterComponentFamily period hPeriod
          (independentFieldCurve period hPeriod fields variation parameter)
          component point * test point) 0 0 := by
    have hCurve :
        (fun parameter ↦ massSquared *
          independentMatterComponentFamily period hPeriod
            (independentFieldCurve period hPeriod fields variation parameter)
            component point * test point) =
          (fun _ : Real ↦ massSquared * field point * test point) := by
      funext parameter
      rw [independentMatterComponent_metricOnlyCurve]
    rw [hCurve]
    exact hasDerivAt_const (x := (0 : Real))
      (c := massSquared * field point * test point)
  have hLagrangian := hKinetic.add hPotential
  have hDensity := hVolume.mul hLagrangian
  have hCurve :
      (fun parameter ↦
        independentMatterEulerDensity period hPeriod massSquared
          (independentFieldCurve period hPeriod fields
            (metricOnlyIndependentVariation period hPeriod metricDirection)
            parameter)
          matterDirection component point) =
        (fun parameter ↦
          diagonalMetricVolumeDensity period hPeriod
            (independentMatterMagnitude period hPeriod
              (independentFieldCurve period hPeriod fields variation parameter)
              component.1) point) *
          ((fun parameter ↦ (1 / 2 : Real) * ∑ index : Fin 4,
            (signature index /
                independentMatterMagnitude period hPeriod
                  (independentFieldCurve period hPeriod fields variation parameter)
                  component.1 point index) *
              (2 * holonomicCovectorComponent period hPeriod
                  (independentMatterComponentFamily period hPeriod
                    (independentFieldCurve period hPeriod fields variation parameter)
                    component) point index *
                holonomicCovectorComponent period hPeriod test point index)) +
            (fun parameter ↦ massSquared *
              independentMatterComponentFamily period hPeriod
                (independentFieldCurve period hPeriod fields variation parameter)
                component point * test point)) := by
    funext parameter
    rfl
  rw [hCurve]
  simpa [independentMatterEulerLagrangian,
    independentMetricMatterMixedDensity, variation, field, test,
    independentFieldCurve_zero] using hDensity

/-- Outer metric curve of the derivative, in a matter direction, of the same
actual pointwise density. -/
def programPMetricMatterPointwiseMixedDerivativeCurve
    (massSquared : Real)
    (fields : IndependentFields period hPeriod)
    (metricDirection : SmoothDiagonalMetricVariation period hPeriod)
    (matterDirection : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod)
    (metricParameter : Real) : Real :=
  deriv
    (programPMetricMatterDensityCurve period hPeriod massSquared
      (independentFieldCurve period hPeriod fields
        (metricOnlyIndependentVariation period hPeriod metricDirection)
        metricParameter)
      (matterOnlyRobinCompleteVariation period hPeriod matterDirection)
      component point) 0

/-- Genuine pointwise mixed second variation of the same metric--matter
density: first in matter, then in the diagonal metric. -/
theorem programPMetricMatterPointwiseMixedDerivativeCurve_hasDerivAt
    (massSquared : Real)
    (fields : IndependentFields period hPeriod)
    (metricDirection : SmoothDiagonalMetricVariation period hPeriod)
    (matterDirection : SmoothQuotientField period hPeriod MatterFiber ×
      SmoothQuotientField period hPeriod MatterFiber)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (programPMetricMatterPointwiseMixedDerivativeCurve period hPeriod
        massSquared fields metricDirection matterDirection component point)
      (independentMetricMatterMixedDensity period hPeriod massSquared fields
        metricDirection matterDirection component point) 0 := by
  have hCurve :
      programPMetricMatterPointwiseMixedDerivativeCurve period hPeriod
          massSquared fields metricDirection matterDirection component point =
        (fun metricParameter ↦
          independentMatterEulerDensity period hPeriod massSquared
            (independentFieldCurve period hPeriod fields
              (metricOnlyIndependentVariation period hPeriod metricDirection)
              metricParameter)
            matterDirection component point) := by
    funext metricParameter
    exact (programPMetricMatterDensityCurve_matterOnly_hasDerivAt period hPeriod
      massSquared
      (independentFieldCurve period hPeriod fields
        (metricOnlyIndependentVariation period hPeriod metricDirection)
        metricParameter)
      matterDirection component point).deriv
  rw [hCurve]
  exact independentMatterEulerDensity_metricOnlyCurve_hasDerivAt period hPeriod
    massSquared fields metricDirection matterDirection component point

end

end P0EFTJanusMappingTorusIndependentMetricMatterPointwiseMixedHessian4D
end JanusFormal
