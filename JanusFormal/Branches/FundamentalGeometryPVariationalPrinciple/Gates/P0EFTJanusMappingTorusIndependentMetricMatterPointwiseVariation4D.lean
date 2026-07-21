import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Sqrt
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusIndependentMatterMetricActionData4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D

/-!
# Pointwise metric--matter variation on the actual Program-P fields

This gate varies one of the eight global scalar densities along the same
`IndependentFields` curve as its sector metric.  The metric magnitudes follow
the existing positive exponential curve, the scalar follows its actual affine
matter direction, and every fixed-frame covector component is the manifold
differential of that same scalar field.

The resulting formula is pointwise on the genuine D8 quotient and is exposed
for a `ProgramPRobinCompleteVariation4D`.  No differentiation under the
integral, covariant stress decomposition, general-metric extension, or mixed
Hessian statement is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusIndependentMetricMatterPointwiseVariation4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusInducedFieldVariation4D
open P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarVariation4D
open P0EFTJanusMappingTorusScalarDiffeomorphismNoetherOperator4D
open P0EFTJanusGlobalMatterMultipletActualEulerHessian4D
open P0EFTJanusCommonMatterActionVariation4D
open P0EFTJanusIndependentMatterMetricActionData4D
open P0EFTJanusRobinExtendedCompleteVariationReducedFredholm4D
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

/-- Velocity of the positive metric magnitudes selected by one matter sector. -/
def independentMatterMagnitudeVelocityAt
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Fin 2) (point : EffectiveQuotient period hPeriod) :
    Fin 4 → Real :=
  if sector = 0 then
    (metricMagnitudeVelocityAt period hPeriod fields variation 0 point).1
  else
    (metricMagnitudeVelocityAt period hPeriod fields variation 0 point).2

/-- The selected metric magnitude follows the actual exponential metric curve. -/
theorem independentMatterMagnitude_curve_hasDerivAt
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Fin 2) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun parameter =>
        independentMatterMagnitude period hPeriod
          (independentFieldCurve period hPeriod fields variation parameter)
          sector point)
      (independentMatterMagnitudeVelocityAt period hPeriod fields variation
        sector point) 0 := by
  by_cases hSector : sector = 0
  · simp only [independentMatterMagnitude, independentMatterMagnitudeVelocityAt,
      hSector, if_true]
    exact plusMagnitude_curve_hasDerivAt period hPeriod fields variation 0 point
  · simp only [independentMatterMagnitude, independentMatterMagnitudeVelocityAt,
      hSector, if_false]
    exact minusMagnitude_curve_hasDerivAt period hPeriod fields variation 0 point

/-- Extracting matter coordinates from an arbitrary simultaneous independent
curve gives their exact componentwise affine curve. -/
theorem independentMatterComponentFamily_independentFieldCurve
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (parameter : Real) :
    independentMatterComponentFamily period hPeriod
        (independentFieldCurve period hPeriod fields variation parameter) =
      matterMultipletAffineCurve period hPeriod
        (independentMatterComponentFamily period hPeriod fields)
        (matterVariationComponentFamily period hPeriod variation.matter)
        parameter := by
  funext component
  apply SmoothQuotientField.ext period hPeriod Real
  intro point
  rcases component with ⟨sector, component⟩
  fin_cases sector <;>
    simp [independentMatterComponentFamily, independentMatterScalar,
      selectMatterField, independentFieldCurve, matterMultipletAffineCurve,
      matterVariationComponentFamily, scalarAffineCurve] <;> rfl

/-- One extracted scalar on the simultaneous curve is the affine curve of its
actual matter component. -/
theorem independentMatterComponent_curve_eq_affine
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (component : MatterComponentIndex) (parameter : Real) :
    independentMatterComponentFamily period hPeriod
        (independentFieldCurve period hPeriod fields variation parameter)
        component =
      scalarAffineCurve period hPeriod
        (independentMatterComponentFamily period hPeriod fields component)
        (matterVariationComponentFamily period hPeriod variation.matter component)
        parameter := by
  rw [independentMatterComponentFamily_independentFieldCurve]
  rfl

/-- The corresponding fixed-frame covector velocity is the differential of
the same matter variation, not an independent jet slot. -/
theorem independentMatterCovector_curve_hasDerivAt
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod) (index : Fin 4) :
    HasDerivAt
      (fun parameter =>
        holonomicCovectorComponent period hPeriod
          (independentMatterComponentFamily period hPeriod
            (independentFieldCurve period hPeriod fields variation parameter)
            component) point index)
      (holonomicCovectorComponent period hPeriod
        (matterVariationComponentFamily period hPeriod variation.matter component)
        point index) 0 := by
  have hCurve :
      (fun parameter =>
        holonomicCovectorComponent period hPeriod
          (independentMatterComponentFamily period hPeriod
            (independentFieldCurve period hPeriod fields variation parameter)
            component) point index) =
      (fun parameter =>
        holonomicCovectorComponent period hPeriod
          (scalarAffineCurve period hPeriod
            (independentMatterComponentFamily period hPeriod fields component)
            (matterVariationComponentFamily period hPeriod variation.matter
              component) parameter) point index) := by
    funext parameter
    rw [independentMatterComponent_curve_eq_affine]
  rw [hCurve]
  have hAffine :
      (fun parameter =>
        holonomicCovectorComponent period hPeriod
          (scalarAffineCurve period hPeriod
            (independentMatterComponentFamily period hPeriod fields component)
            (matterVariationComponentFamily period hPeriod variation.matter
              component) parameter) point index) =
      (fun parameter =>
        holonomicCovectorComponent period hPeriod
            (independentMatterComponentFamily period hPeriod fields component)
            point index +
          parameter * holonomicCovectorComponent period hPeriod
            (matterVariationComponentFamily period hPeriod variation.matter
              component) point index) := by
    funext parameter
    exact holonomicCovectorComponent_affine period hPeriod _ _ parameter point index
  rw [hAffine]
  simpa using
    (((hasDerivAt_id (0 : Real)).mul_const
      (holonomicCovectorComponent period hPeriod
        (matterVariationComponentFamily period hPeriod variation.matter component)
        point index)).const_add
      (holonomicCovectorComponent period hPeriod
        (independentMatterComponentFamily period hPeriod fields component)
        point index))

/-- Derivative of the finite product of the four selected magnitudes. -/
def independentMatterMagnitudeProductVelocity
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Fin 2) (point : EffectiveQuotient period hPeriod) : Real :=
  ∑ index ∈ Finset.univ,
    (∏ other ∈ Finset.univ.erase index,
      independentMatterMagnitude period hPeriod fields sector point other) *
      independentMatterMagnitudeVelocityAt period hPeriod fields variation sector
        point index

/-- Derivative of the metric volume supplied by that same sector metric. -/
def independentMatterVolumeVelocity
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Fin 2) (point : EffectiveQuotient period hPeriod) : Real :=
  independentMatterMagnitudeProductVelocity period hPeriod fields variation sector
      point /
    (2 * Real.sqrt (∏ index : Fin 4,
      independentMatterMagnitude period hPeriod fields sector point index))

/-- Pointwise velocity of the diagonal kinetic density.  Both the inverse
metric coefficients and `dφ` vary along the same independent-field curve. -/
def independentMatterKineticVelocity
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod) : Real :=
  (1 / 2 : Real) * ∑ index : Fin 4, (
    (-(signature index *
          independentMatterMagnitudeVelocityAt period hPeriod fields variation
            component.1 point index) /
        (independentMatterMagnitude period hPeriod fields component.1 point index) ^ 2) *
        holonomicCovectorComponent period hPeriod
          (independentMatterComponentFamily period hPeriod fields component)
          point index ^ 2 +
      (signature index /
        independentMatterMagnitude period hPeriod fields component.1 point index) *
        (2 * holonomicCovectorComponent period hPeriod
          (independentMatterComponentFamily period hPeriod fields component)
          point index *
          holonomicCovectorComponent period hPeriod
            (matterVariationComponentFamily period hPeriod variation.matter component)
            point index))

/-- The exact pointwise first variation of one sector-selected global scalar
density along a simultaneous independent-field direction. -/
def independentMetricMatterFirstVariationDensity
    (massSquared : Real)
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod) : Real :=
  let magnitude :=
    independentMatterMagnitude period hPeriod fields component.1
  let field :=
    independentMatterComponentFamily period hPeriod fields component
  let fieldVariation :=
    matterVariationComponentFamily period hPeriod variation.matter component
  independentMatterVolumeVelocity period hPeriod fields variation component.1
      point *
      (diagonalHolonomicKineticDensity period hPeriod magnitude field point +
        massSquared / 2 * field point ^ 2) +
    diagonalMetricVolumeDensity period hPeriod magnitude point *
      (independentMatterKineticVelocity period hPeriod fields variation component
          point +
        massSquared * field point * fieldVariation point)

/-- Actual pointwise density curve using the varying metric and matter fields
from one `ProgramPRobinCompleteVariation4D`. -/
def programPMetricMatterDensityCurve
    (massSquared : Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod) (parameter : Real) : Real :=
  let variedFields := independentFieldCurve period hPeriod fields
    direction.complete.independent parameter
  globalHolonomicScalarDensity period hPeriod massSquared
    (independentMatterMagnitude period hPeriod variedFields component.1)
    (independentMatterComponentFamily period hPeriod variedFields component)
    point

private theorem independentMatterVolume_curve_hasDerivAt
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (sector : Fin 2) (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun parameter =>
        diagonalMetricVolumeDensity period hPeriod
          (independentMatterMagnitude period hPeriod
            (independentFieldCurve period hPeriod fields variation parameter)
            sector) point)
      (independentMatterVolumeVelocity period hPeriod fields variation sector point)
      0 := by
  have hProduct : HasDerivAt
      (fun parameter => ∏ index : Fin 4,
        independentMatterMagnitude period hPeriod
          (independentFieldCurve period hPeriod fields variation parameter)
          sector point index)
      (independentMatterMagnitudeProductVelocity period hPeriod fields variation
        sector point) 0 := by
    have hRaw := HasDerivAt.fun_finsetProd (u := Finset.univ)
      (f := fun index parameter =>
        independentMatterMagnitude period hPeriod
          (independentFieldCurve period hPeriod fields variation parameter)
          sector point index)
      (f' := fun index =>
        independentMatterMagnitudeVelocityAt period hPeriod fields variation
          sector point index)
      (fun index _ => (hasDerivAt_pi.mp
        (independentMatterMagnitude_curve_hasDerivAt period hPeriod fields
          variation sector point)) index)
    simpa [independentMatterMagnitudeProductVelocity,
      independentFieldCurve_zero] using hRaw
  have hProductPos : 0 < ∏ index : Fin 4,
      independentMatterMagnitude period hPeriod fields sector point index :=
    Finset.prod_pos fun index _ =>
      independentMatterMagnitude_pos period hPeriod fields sector point index
  have hSqrt := hProduct.sqrt (by
    simpa [independentFieldCurve_zero] using ne_of_gt hProductPos)
  simpa [diagonalMetricVolumeDensity, independentMatterVolumeVelocity,
    independentFieldCurve_zero] using hSqrt

private theorem independentMatterKinetic_curve_hasDerivAt
    (fields : IndependentFields period hPeriod)
    (variation : IndependentFieldVariation period hPeriod)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun parameter =>
        diagonalHolonomicKineticDensity period hPeriod
          (independentMatterMagnitude period hPeriod
            (independentFieldCurve period hPeriod fields variation parameter)
            component.1)
          (independentMatterComponentFamily period hPeriod
            (independentFieldCurve period hPeriod fields variation parameter)
            component) point)
      (independentMatterKineticVelocity period hPeriod fields variation component
        point) 0 := by
  have hSum : HasDerivAt
      (fun parameter => ∑ index : Fin 4,
        signature index /
            independentMatterMagnitude period hPeriod
              (independentFieldCurve period hPeriod fields variation parameter)
              component.1 point index *
          holonomicCovectorComponent period hPeriod
            (independentMatterComponentFamily period hPeriod
              (independentFieldCurve period hPeriod fields variation parameter)
              component) point index ^ 2)
      (∑ index : Fin 4, (
        (-(signature index *
              independentMatterMagnitudeVelocityAt period hPeriod fields variation
                component.1 point index) /
            (independentMatterMagnitude period hPeriod fields component.1 point
              index) ^ 2) *
            holonomicCovectorComponent period hPeriod
              (independentMatterComponentFamily period hPeriod fields component)
              point index ^ 2 +
          (signature index /
            independentMatterMagnitude period hPeriod fields component.1 point
              index) *
            (2 * holonomicCovectorComponent period hPeriod
              (independentMatterComponentFamily period hPeriod fields component)
              point index *
              holonomicCovectorComponent period hPeriod
                (matterVariationComponentFamily period hPeriod variation.matter
                  component) point index))) 0 := by
    apply HasDerivAt.fun_sum
    intro index _
    have hMagnitude := (hasDerivAt_pi.mp
      (independentMatterMagnitude_curve_hasDerivAt period hPeriod fields variation
        component.1 point)) index
    have hMagnitudeNe :
        independentMatterMagnitude period hPeriod fields component.1 point index ≠
          0 := ne_of_gt (independentMatterMagnitude_pos period hPeriod fields
            component.1 point index)
    have hCoefficient :=
      (hasDerivAt_const (x := (0 : Real)) (c := signature index)).div hMagnitude
        (by simpa [independentFieldCurve_zero] using hMagnitudeNe)
    have hCovector := independentMatterCovector_curve_hasDerivAt period hPeriod
      fields variation component point index
    have hTerm := hCoefficient.mul (hCovector.pow 2)
    refine hTerm.congr_deriv ?_
    simp [independentFieldCurve_zero]
  simpa [diagonalHolonomicKineticDensity,
    independentMatterKineticVelocity] using hSum.const_mul (1 / 2 : Real)

/-- The displayed cross-variation is the genuine derivative of the actual
pointwise global scalar density on the common Program-P field curve. -/
theorem programPMetricMatterDensityCurve_hasDerivAt
    (massSquared : Real)
    (fields : IndependentFields period hPeriod)
    (direction : ProgramPRobinCompleteVariation4D period hPeriod)
    (component : MatterComponentIndex)
    (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (programPMetricMatterDensityCurve period hPeriod massSquared fields direction
        component point)
      (independentMetricMatterFirstVariationDensity period hPeriod massSquared fields
        direction.complete.independent component point) 0 := by
  let variation := direction.complete.independent
  let magnitude := independentMatterMagnitude period hPeriod fields component.1
  let field := independentMatterComponentFamily period hPeriod fields component
  let fieldVariation :=
    matterVariationComponentFamily period hPeriod variation.matter component
  have hVolume := independentMatterVolume_curve_hasDerivAt period hPeriod fields
    variation component.1 point
  have hKinetic := independentMatterKinetic_curve_hasDerivAt period hPeriod fields
    variation component point
  have hField : HasDerivAt
      (fun parameter =>
        independentMatterComponentFamily period hPeriod
          (independentFieldCurve period hPeriod fields variation parameter)
          component point)
      (fieldVariation point) 0 := by
    have hCurve :
        (fun parameter =>
          independentMatterComponentFamily period hPeriod
            (independentFieldCurve period hPeriod fields variation parameter)
            component point) =
        (fun parameter => scalarAffineCurve period hPeriod field fieldVariation
          parameter point) := by
      funext parameter
      rw [independentMatterComponent_curve_eq_affine]
    rw [hCurve]
    exact scalarAffineCurve_point_hasDerivAt period hPeriod field fieldVariation
      point 0
  have hPotential := (hField.pow 2).const_mul (massSquared / 2)
  have hPotentialCorrect : HasDerivAt
      (fun parameter => massSquared / 2 *
        (independentMatterComponentFamily period hPeriod
          (independentFieldCurve period hPeriod fields variation parameter)
          component point) ^ 2)
      (massSquared * field point * fieldVariation point) 0 := by
    refine hPotential.congr_deriv ?_
    simp [field, fieldVariation, independentFieldCurve_zero]
    ring
  have hDensity := hVolume.mul (hKinetic.add hPotentialCorrect)
  have hCurve :
      programPMetricMatterDensityCurve period hPeriod massSquared fields direction
          component point =
        (fun parameter =>
          diagonalMetricVolumeDensity period hPeriod
              (independentMatterMagnitude period hPeriod
                (independentFieldCurve period hPeriod fields variation parameter)
                component.1) point *
            (diagonalHolonomicKineticDensity period hPeriod
                (independentMatterMagnitude period hPeriod
                  (independentFieldCurve period hPeriod fields variation parameter)
                  component.1)
                (independentMatterComponentFamily period hPeriod
                  (independentFieldCurve period hPeriod fields variation parameter)
                  component) point +
              massSquared / 2 *
                (independentMatterComponentFamily period hPeriod
                  (independentFieldCurve period hPeriod fields variation parameter)
                  component point) ^ 2)) := by
    funext parameter
    rfl
  rw [hCurve]
  refine hDensity.congr_deriv ?_
  simp [independentMetricMatterFirstVariationDensity, variation, magnitude,
    field, fieldVariation, independentFieldCurve_zero]

end

end P0EFTJanusMappingTorusIndependentMetricMatterPointwiseVariation4D
end JanusFormal
