import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
import Mathlib.Analysis.Matrix.Normed

/-! Diagonal diffeomorphism action on the actual global D8 field package. -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open scoped Matrix.Norms.Frobenius
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothDiagonalLorentzFields4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D

variable (period : Real) (hPeriod : Not (period = 0))
private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
local instance effectiveQuotientChartedSpace : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance effectiveQuotientIsManifold : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance effectiveThroatChartedSpace : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) := fixedThroatQuotientChartedSpace period hPeriod
local instance effectiveThroatIsManifold : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) := fixedThroatQuotient_isManifold period hPeriod

universe u
variable (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
abbrev SpacetimeDiffeomorphism := EffectiveQuotient period hPeriod ≃ₘ^ω⟮coverModelWithCorners, coverModelWithCorners⟯ EffectiveQuotient period hPeriod
abbrev ThroatDiffeomorphism := EffectiveThroat period hPeriod ≃ₘ^ω⟮throatCoverModelWithCorners, throatCoverModelWithCorners⟯ EffectiveThroat period hPeriod

def pullbackSmoothField (d : SpacetimeDiffeomorphism period hPeriod) (f : SmoothQuotientField period hPeriod Fiber) : SmoothQuotientField period hPeriod Fiber where
  toFun := f.toFun ∘ d
  contMDiff_toFun := f.contMDiff_toFun.comp d.contMDiff

@[simp] theorem pullbackSmoothField_apply (d : SpacetimeDiffeomorphism period hPeriod) (f : SmoothQuotientField period hPeriod Fiber) (x : EffectiveQuotient period hPeriod) : pullbackSmoothField period hPeriod Fiber d f x = f (d x) := by simp [pullbackSmoothField]

@[simp] theorem pullbackSmoothField_refl (f : SmoothQuotientField period hPeriod Fiber) : pullbackSmoothField period hPeriod Fiber (Diffeomorph.refl coverModelWithCorners (EffectiveQuotient period hPeriod) ω) f = f := by ext x; simp [pullbackSmoothField]

theorem pullbackSmoothField_trans (a b : SpacetimeDiffeomorphism period hPeriod) (f : SmoothQuotientField period hPeriod Fiber) : pullbackSmoothField period hPeriod Fiber a (pullbackSmoothField period hPeriod Fiber b f) = pullbackSmoothField period hPeriod Fiber (a.trans b) f := by ext x; simp [pullbackSmoothField]

theorem pullbackSmoothField_symm (d : SpacetimeDiffeomorphism period hPeriod) (f : SmoothQuotientField period hPeriod Fiber) : pullbackSmoothField period hPeriod Fiber d.symm (pullbackSmoothField period hPeriod Fiber d f) = f := by ext x; simp [pullbackSmoothField]

def pullbackSmoothThroatField (d : ThroatDiffeomorphism period hPeriod) (f : SmoothThroatField period hPeriod Fiber) : SmoothThroatField period hPeriod Fiber where
  toFun := f.toFun ∘ d
  contMDiff_toFun := f.contMDiff_toFun.comp d.contMDiff

structure DiagonalDiffeomorphism where
  spacetime : SpacetimeDiffeomorphism period hPeriod
  throat : ThroatDiffeomorphism period hPeriod
  preservesThroat : ∀ x, fixedThroatQuotientInclusion period hPeriod (throat x) = spacetime (fixedThroatQuotientInclusion period hPeriod x)

def pullbackMetricPair (d : SpacetimeDiffeomorphism period hPeriod) (g : SmoothPositiveDiagonalMetricPair period hPeriod) : SmoothPositiveDiagonalMetricPair period hPeriod where
  plusMagnitude := pullbackSmoothField period hPeriod _ d g.plusMagnitude
  minusMagnitude := pullbackSmoothField period hPeriod _ d g.minusMagnitude
  plus_pos := fun x i => by simpa [pullbackSmoothField] using g.plus_pos (d x) i
  minus_pos := fun x i => by simpa [pullbackSmoothField] using g.minus_pos (d x) i

def pullbackIndependentFields (d : DiagonalDiffeomorphism period hPeriod) (f : IndependentFields period hPeriod) : IndependentFields period hPeriod where
  metrics := pullbackMetricPair period hPeriod d.spacetime f.metrics
  matter := (pullbackSmoothField period hPeriod _ d.spacetime f.matter.1, pullbackSmoothField period hPeriod _ d.spacetime f.matter.2)
  gauge := (pullbackSmoothField period hPeriod _ d.spacetime f.gauge.1, pullbackSmoothField period hPeriod _ d.spacetime f.gauge.2)
  ghosts := (pullbackSmoothField period hPeriod _ d.spacetime f.ghosts.1, pullbackSmoothField period hPeriod _ d.spacetime f.ghosts.2)
  auxiliaries := (pullbackSmoothField period hPeriod _ d.spacetime f.auxiliaries.1, pullbackSmoothField period hPeriod _ d.spacetime f.auxiliaries.2)
  llAuxMetric := pullbackSmoothThroatField period hPeriod _ d.throat f.llAuxMetric
  llMeasure := pullbackSmoothThroatField period hPeriod _ d.throat f.llMeasure
  llField := pullbackSmoothThroatField period hPeriod _ d.throat f.llField

theorem throatTrace_pullback (d : DiagonalDiffeomorphism period hPeriod) (f : SmoothQuotientField period hPeriod Fiber) : throatTrace period hPeriod Fiber (pullbackSmoothField period hPeriod Fiber d.spacetime f) = pullbackSmoothThroatField period hPeriod Fiber d.throat (throatTrace period hPeriod Fiber f) := by
  apply SmoothThroatField.ext period hPeriod Fiber
  intro x
  simpa [throatTrace, pullbackSmoothField, pullbackSmoothThroatField] using
    congrArg f.toFun (d.preservesThroat x).symm

theorem inducedPlusMatterTrace_pullback (d : DiagonalDiffeomorphism period hPeriod) (f : IndependentFields period hPeriod) : (induce period hPeriod (pullbackIndependentFields period hPeriod d f)).plusMatterTrace = pullbackSmoothThroatField period hPeriod _ d.throat (induce period hPeriod f).plusMatterTrace := throatTrace_pullback period hPeriod _ d f.matter.1

theorem inducedPlusMetric_pullback
    (d : DiagonalDiffeomorphism period hPeriod)
    (f : IndependentFields period hPeriod) :
    (induce period hPeriod
        (pullbackIndependentFields period hPeriod d f)).plusMetric =
      pullbackSmoothField period hPeriod _ d.spacetime
        (induce period hPeriod f).plusMetric := by
  apply SmoothQuotientField.ext period hPeriod _
  intro x
  rfl

theorem inducedMinusMetric_pullback
    (d : DiagonalDiffeomorphism period hPeriod)
    (f : IndependentFields period hPeriod) :
    (induce period hPeriod
        (pullbackIndependentFields period hPeriod d f)).minusMetric =
      pullbackSmoothField period hPeriod _ d.spacetime
        (induce period hPeriod f).minusMetric := by
  apply SmoothQuotientField.ext period hPeriod _
  intro x
  rfl

theorem inducedPrincipalRoot_pullback
    (d : DiagonalDiffeomorphism period hPeriod)
    (f : IndependentFields period hPeriod) :
    (induce period hPeriod
        (pullbackIndependentFields period hPeriod d f)).principalRoot =
      pullbackSmoothField period hPeriod _ d.spacetime
        (induce period hPeriod f).principalRoot := by
  apply SmoothQuotientField.ext period hPeriod _
  intro x
  rfl

theorem inducedMinusMatterTrace_pullback
    (d : DiagonalDiffeomorphism period hPeriod)
    (f : IndependentFields period hPeriod) :
    (induce period hPeriod
        (pullbackIndependentFields period hPeriod d f)).minusMatterTrace =
      pullbackSmoothThroatField period hPeriod _ d.throat
        (induce period hPeriod f).minusMatterTrace :=
  throatTrace_pullback period hPeriod _ d f.matter.2

structure SmoothSpacetimeOrbit (point : EffectiveQuotient period hPeriod) where
  orbit : Real → EffectiveQuotient period hPeriod
  smooth : ContMDiff 𝓘(Real, Real) coverModelWithCorners ω orbit
  atZero : orbit 0 = point

def infinitesimalGenerator {point : EffectiveQuotient period hPeriod} (flow : SmoothSpacetimeOrbit period hPeriod point) : TangentSpace coverModelWithCorners (flow.orbit 0) := mfderiv 𝓘(Real, Real) coverModelWithCorners flow.orbit 0 1

end
end P0EFTJanusMappingTorusDiagonalDiffeomorphismAction4D
end JanusFormal
