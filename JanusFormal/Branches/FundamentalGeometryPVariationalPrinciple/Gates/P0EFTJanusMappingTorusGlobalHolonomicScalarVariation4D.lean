import Mathlib.Analysis.Calculus.Deriv.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothFieldLinearSpace4D

/-!
# Global scalar variation on the actual D8 quotient

For one fixed positive diagonal metric and one fixed measure, this gate varies
the same global smooth scalar that enters the holonomic action.  The affine
curve has the exact manifold differential expected from linearity of
`mfderiv`; consequently the pointwise density and the integrated action have
exact quadratic expansions.  Differentiation under the integral is obtained
from those expansions under explicit integrability hypotheses.

No covariant Euler--flux decomposition is claimed: the current fixed-frame
action does not yet provide a global divergence operator or a divergence
theorem compatible with its measure.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGlobalHolonomicScalarVariation4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff BigOperators
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGlobalHolonomicScalar4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D

variable (period : Real) (hPeriod : Not (period = 0))

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- The affine curve through one global scalar in a global smooth direction. -/
def scalarAffineCurve
    (field variation : SmoothQuotientField period hPeriod Real)
    (epsilon : Real) : SmoothQuotientField period hPeriod Real :=
  field + epsilon • variation

@[simp]
theorem scalarAffineCurve_apply
    (field variation : SmoothQuotientField period hPeriod Real)
    (epsilon : Real) (point : EffectiveQuotient period hPeriod) :
    scalarAffineCurve period hPeriod field variation epsilon point =
      field point + epsilon * variation point := by
  rfl

/-- At every quotient point the affine scalar curve is a smooth real curve. -/
theorem scalarAffineCurve_point_contDiff
    (field variation : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    ContDiff Real ∞
      (fun epsilon : Real =>
        scalarAffineCurve period hPeriod field variation epsilon point) := by
  simp only [scalarAffineCurve_apply]
  fun_prop

/-- Its pointwise velocity is exactly the supplied global variation. -/
theorem scalarAffineCurve_point_hasDerivAt
    (field variation : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) (epsilon : Real) :
    HasDerivAt
      (fun parameter : Real =>
        scalarAffineCurve period hPeriod field variation parameter point)
      (variation point) epsilon := by
  change HasDerivAt
    (fun parameter : Real => field point + parameter * variation point)
    (variation point) epsilon
  simpa only [id_eq, one_mul] using
    (((hasDerivAt_id epsilon).mul_const (variation point)).const_add
      (field point))

/-- Exact linearity of the genuine manifold differential along the affine
curve. -/
theorem scalarDifferential_affine
    (field variation : SmoothQuotientField period hPeriod Real)
    (epsilon : Real) (point : EffectiveQuotient period hPeriod) :
    scalarDifferential period hPeriod
        (scalarAffineCurve period hPeriod field variation epsilon) point =
      scalarDifferential period hPeriod field point +
        epsilon • scalarDifferential period hPeriod variation point := by
  unfold scalarDifferential scalarAffineCurve
  change mfderiv coverModelWithCorners _
      (field.toFun + epsilon • variation.toFun) point = _
  rw [mfderiv_add (field.contMDiff_toFun.mdifferentiableAt (by simp))
      ((variation.contMDiff_toFun.mdifferentiableAt (by simp)).const_smul epsilon),
    const_smul_mfderiv
      (variation.contMDiff_toFun.mdifferentiableAt (by simp)) epsilon]
  ext tangent
  rfl

/-- Fixed-frame components inherit the exact affine `mfderiv` law. -/
theorem holonomicCovectorComponent_affine
    (field variation : SmoothQuotientField period hPeriod Real)
    (epsilon : Real) (point : EffectiveQuotient period hPeriod)
    (index : Fin 4) :
    holonomicCovectorComponent period hPeriod
        (scalarAffineCurve period hPeriod field variation epsilon) point index =
      holonomicCovectorComponent period hPeriod field point index +
        epsilon *
          holonomicCovectorComponent period hPeriod variation point index := by
  unfold holonomicCovectorComponent
  rw [scalarDifferential_affine]
  rfl

/-- The pointwise weak first-variation density of the global scalar action,
with metric and measure fixed. -/
def globalHolonomicScalarFirstVariationDensity
    (massSquared : Real)
    (magnitude : SmoothQuotientField period hPeriod (Fin 4 → Real))
    (field variation : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) : Real :=
  diagonalMetricVolumeDensity period hPeriod magnitude point *
    ((∑ index : Fin 4,
        P0EFTJanusGlobalDiagonalLorentzRoot4D.signature index /
            magnitude point index *
          holonomicCovectorComponent period hPeriod field point index *
          holonomicCovectorComponent period hPeriod variation point index) +
      massSquared * field point * variation point)

/-- Exact quadratic expansion of the pointwise density along the same global
affine scalar curve. -/
theorem globalHolonomicScalarDensity_affine
    (massSquared : Real)
    (magnitude : SmoothQuotientField period hPeriod (Fin 4 → Real))
    (field variation : SmoothQuotientField period hPeriod Real)
    (epsilon : Real) (point : EffectiveQuotient period hPeriod) :
    globalHolonomicScalarDensity period hPeriod massSquared magnitude
        (scalarAffineCurve period hPeriod field variation epsilon) point =
      globalHolonomicScalarDensity period hPeriod massSquared magnitude field point +
        epsilon * globalHolonomicScalarFirstVariationDensity period hPeriod
          massSquared magnitude field variation point +
        epsilon ^ 2 * globalHolonomicScalarDensity period hPeriod massSquared
          magnitude variation point := by
  have hKinetic :
      diagonalHolonomicKineticDensity period hPeriod magnitude
          (scalarAffineCurve period hPeriod field variation epsilon) point =
        diagonalHolonomicKineticDensity period hPeriod magnitude field point +
          epsilon *
            (∑ index : Fin 4,
              P0EFTJanusGlobalDiagonalLorentzRoot4D.signature index /
                  magnitude point index *
                holonomicCovectorComponent period hPeriod field point index *
                holonomicCovectorComponent period hPeriod variation point index) +
          epsilon ^ 2 *
            diagonalHolonomicKineticDensity period hPeriod magnitude variation point := by
    unfold diagonalHolonomicKineticDensity
    simp_rw [holonomicCovectorComponent_affine]
    rw [Finset.mul_sum]
    calc
      _ = ∑ index : Fin 4,
          ((1 / 2 : Real) *
              (P0EFTJanusGlobalDiagonalLorentzRoot4D.signature index /
                magnitude point index *
                holonomicCovectorComponent period hPeriod field point index ^ 2) +
            epsilon *
              (P0EFTJanusGlobalDiagonalLorentzRoot4D.signature index /
                magnitude point index *
                holonomicCovectorComponent period hPeriod field point index *
                holonomicCovectorComponent period hPeriod variation point index) +
            epsilon ^ 2 * ((1 / 2 : Real) *
              (P0EFTJanusGlobalDiagonalLorentzRoot4D.signature index /
                magnitude point index *
                holonomicCovectorComponent period hPeriod variation point index ^ 2))) := by
          apply Finset.sum_congr rfl
          intro index _
          ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
        simp only [Finset.mul_sum]
  rw [globalHolonomicScalarDensity, hKinetic]
  simp only [scalarAffineCurve_apply]
  unfold globalHolonomicScalarFirstVariationDensity
  rw [globalHolonomicScalarDensity, globalHolonomicScalarDensity]
  ring

/-- The pointwise density derivative is the displayed weak first variation. -/
theorem globalHolonomicScalarDensity_affine_hasDerivAt
    (massSquared : Real)
    (magnitude : SmoothQuotientField period hPeriod (Fin 4 → Real))
    (field variation : SmoothQuotientField period hPeriod Real)
    (point : EffectiveQuotient period hPeriod) :
    HasDerivAt
      (fun epsilon : Real =>
        globalHolonomicScalarDensity period hPeriod massSquared magnitude
          (scalarAffineCurve period hPeriod field variation epsilon) point)
      (globalHolonomicScalarFirstVariationDensity period hPeriod massSquared
        magnitude field variation point) 0 := by
  rw [show (fun epsilon : Real =>
      globalHolonomicScalarDensity period hPeriod massSquared magnitude
        (scalarAffineCurve period hPeriod field variation epsilon) point) =
      (fun epsilon : Real =>
        globalHolonomicScalarDensity period hPeriod massSquared magnitude field point +
          epsilon * globalHolonomicScalarFirstVariationDensity period hPeriod
            massSquared magnitude field variation point +
          epsilon ^ 2 * globalHolonomicScalarDensity period hPeriod massSquared
            magnitude variation point) from by
        funext epsilon
        exact globalHolonomicScalarDensity_affine period hPeriod massSquared
          magnitude field variation epsilon point]
  have hLinear := ((hasDerivAt_id (𝕜 := Real) 0).mul_const
    (globalHolonomicScalarFirstVariationDensity period hPeriod massSquared
      magnitude field variation point)).const_add
    (globalHolonomicScalarDensity period hPeriod massSquared magnitude field point)
  have hQuadratic := ((hasDerivAt_id (𝕜 := Real) 0).pow 2).mul_const
    (globalHolonomicScalarDensity period hPeriod massSquared magnitude variation point)
  change HasDerivAt
    ((fun epsilon : Real =>
        globalHolonomicScalarDensity period hPeriod massSquared magnitude field point +
          epsilon * globalHolonomicScalarFirstVariationDensity period hPeriod
            massSquared magnitude field variation point) +
      (fun epsilon : Real => epsilon ^ 2 *
        globalHolonomicScalarDensity period hPeriod massSquared magnitude variation point))
    _ 0
  exact (hLinear.add hQuadratic).congr_deriv (by norm_num)

/-- Integrability contract sufficient for the exact integrated variation. -/
structure GlobalScalarVariationContract
    (massSquared : Real)
    (magnitude : SmoothQuotientField period hPeriod (Fin 4 → Real))
    (field variation : SmoothQuotientField period hPeriod Real)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Prop where
  base_integrable : Integrable
    (globalHolonomicScalarDensity period hPeriod massSquared magnitude field)
    measure
  first_integrable : Integrable
    (globalHolonomicScalarFirstVariationDensity period hPeriod massSquared
      magnitude field variation) measure
  quadratic_integrable : Integrable
    (globalHolonomicScalarDensity period hPeriod massSquared magnitude variation)
    measure

/-- Integrated weak first variation. -/
def globalHolonomicScalarFirstVariation
    (massSquared : Real)
    (magnitude : SmoothQuotientField period hPeriod (Fin 4 → Real))
    (field variation : SmoothQuotientField period hPeriod Real)
    (measure : Measure (EffectiveQuotient period hPeriod)) : Real :=
  ∫ point, globalHolonomicScalarFirstVariationDensity period hPeriod
    massSquared magnitude field variation point ∂measure

/-- Under the explicit integrability contract, the global action has the same
exact quadratic expansion as its density. -/
theorem globalHolonomicScalarAction_affine
    (massSquared : Real)
    (magnitude : SmoothQuotientField period hPeriod (Fin 4 → Real))
    (field variation : SmoothQuotientField period hPeriod Real)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (contract : GlobalScalarVariationContract period hPeriod massSquared
      magnitude field variation measure)
    (epsilon : Real) :
    globalHolonomicScalarAction period hPeriod massSquared magnitude
        (scalarAffineCurve period hPeriod field variation epsilon) measure =
      globalHolonomicScalarAction period hPeriod massSquared magnitude field measure +
        epsilon * globalHolonomicScalarFirstVariation period hPeriod massSquared
          magnitude field variation measure +
        epsilon ^ 2 * globalHolonomicScalarAction period hPeriod massSquared
          magnitude variation measure := by
  unfold globalHolonomicScalarAction globalHolonomicScalarFirstVariation
  simp_rw [globalHolonomicScalarDensity_affine period hPeriod massSquared
    magnitude field variation epsilon]
  have hFirst := contract.first_integrable.const_mul epsilon
  have hQuadratic := contract.quadratic_integrable.const_mul (epsilon ^ 2)
  calc
    ∫ point,
          globalHolonomicScalarDensity period hPeriod massSquared magnitude field point +
              epsilon * globalHolonomicScalarFirstVariationDensity period hPeriod
                massSquared magnitude field variation point +
            epsilon ^ 2 * globalHolonomicScalarDensity period hPeriod massSquared
              magnitude variation point ∂measure =
        ∫ point,
          globalHolonomicScalarDensity period hPeriod massSquared magnitude field point +
            (epsilon * globalHolonomicScalarFirstVariationDensity period hPeriod
                massSquared magnitude field variation point +
              epsilon ^ 2 * globalHolonomicScalarDensity period hPeriod massSquared
                magnitude variation point) ∂measure := by
          congr 1
          funext point
          ring
    _ = (∫ point, globalHolonomicScalarDensity period hPeriod massSquared
          magnitude field point ∂measure) +
        ∫ point,
          epsilon * globalHolonomicScalarFirstVariationDensity period hPeriod
              massSquared magnitude field variation point +
            epsilon ^ 2 * globalHolonomicScalarDensity period hPeriod massSquared
              magnitude variation point ∂measure :=
      integral_add contract.base_integrable (hFirst.add hQuadratic)
    _ = _ := by
      rw [integral_add hFirst hQuadratic, integral_const_mul, integral_const_mul]
      ring

/-- The derivative of the actual integrated action is the integrated weak
first variation; no interchange theorem is hidden in the proof. -/
theorem globalHolonomicScalarAction_affine_hasDerivAt
    (massSquared : Real)
    (magnitude : SmoothQuotientField period hPeriod (Fin 4 → Real))
    (field variation : SmoothQuotientField period hPeriod Real)
    (measure : Measure (EffectiveQuotient period hPeriod))
    (contract : GlobalScalarVariationContract period hPeriod massSquared
      magnitude field variation measure) :
    HasDerivAt
      (fun epsilon : Real =>
        globalHolonomicScalarAction period hPeriod massSquared magnitude
          (scalarAffineCurve period hPeriod field variation epsilon) measure)
      (globalHolonomicScalarFirstVariation period hPeriod massSquared magnitude
        field variation measure) 0 := by
  rw [show (fun epsilon : Real =>
      globalHolonomicScalarAction period hPeriod massSquared magnitude
        (scalarAffineCurve period hPeriod field variation epsilon) measure) =
      (fun epsilon : Real =>
        globalHolonomicScalarAction period hPeriod massSquared magnitude field measure +
          epsilon * globalHolonomicScalarFirstVariation period hPeriod massSquared
            magnitude field variation measure +
          epsilon ^ 2 * globalHolonomicScalarAction period hPeriod massSquared
            magnitude variation measure) from by
        funext epsilon
        exact globalHolonomicScalarAction_affine period hPeriod massSquared
          magnitude field variation measure contract epsilon]
  have hLinear := ((hasDerivAt_id (𝕜 := Real) 0).mul_const
    (globalHolonomicScalarFirstVariation period hPeriod massSquared magnitude
      field variation measure)).const_add
    (globalHolonomicScalarAction period hPeriod massSquared magnitude field measure)
  have hQuadratic := ((hasDerivAt_id (𝕜 := Real) 0).pow 2).mul_const
    (globalHolonomicScalarAction period hPeriod massSquared magnitude variation measure)
  change HasDerivAt
    ((fun epsilon : Real =>
        globalHolonomicScalarAction period hPeriod massSquared magnitude field measure +
          epsilon * globalHolonomicScalarFirstVariation period hPeriod massSquared
            magnitude field variation measure) +
      (fun epsilon : Real => epsilon ^ 2 *
        globalHolonomicScalarAction period hPeriod massSquared magnitude variation measure))
    _ 0
  exact (hLinear.add hQuadratic).congr_deriv (by norm_num)

end

end P0EFTJanusMappingTorusGlobalHolonomicScalarVariation4D
end JanusFormal
