import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothDeckInvariantFields4D
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusSmoothQuotientManifold

/-!
# Smooth fields on the effective D8 quotient

The covering projection is now an analytic local diffeomorphism.  Consequently
every smooth deck-invariant coefficient field descends smoothly, not merely
continuously, and every smooth field on the quotient lifts to a smooth
deck-invariant field.  The two constructions are inverse.

This constructs genuine smooth coefficient-field spaces on the installed D8
four-manifold.  It does not provide Sobolev completions, tensor bundles, traces
or boundary conditions.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSmoothFieldDescent4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothDeckInvariantFields4D

variable (period : ℝ) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveCover := MappingTorusCover (sphereData period hPeriod)
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveCoverChartedSpace :
    ChartedSpace CoverModel (EffectiveCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

local instance effectiveCoverIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

universe u

variable (Fiber : Type u)
  [NormedAddCommGroup Fiber] [NormedSpace ℝ Fiber]

/-- Genuine smooth coefficient fields on the effective quotient manifold. -/
structure SmoothQuotientField where
  toFun : EffectiveQuotient period hPeriod → Fiber
  contMDiff_toFun :
    ContMDiff coverModelWithCorners 𝓘(ℝ, Fiber) ω toFun

instance : CoeFun (SmoothQuotientField period hPeriod Fiber)
    (fun _ => EffectiveQuotient period hPeriod → Fiber) :=
  ⟨SmoothQuotientField.toFun⟩

@[ext]
theorem SmoothQuotientField.ext
    {first second : SmoothQuotientField period hPeriod Fiber}
    (hEqual : ∀ point, first point = second point) : first = second := by
  cases first with
  | mk firstFun firstSmooth =>
    cases second with
    | mk secondFun secondSmooth =>
      have hFun : firstFun = secondFun := funext hEqual
      subst secondFun
      rfl

/-- Smooth descent follows locally by composing with a smooth local inverse of
the quotient projection. -/
theorem contMDiff_descend
    (field : SmoothDeckInvariantField period hPeriod Fiber) :
    ContMDiff coverModelWithCorners 𝓘(ℝ, Fiber) ω
      (descend period hPeriod Fiber field) := by
  intro quotientPoint
  obtain ⟨coverPoint, rfl⟩ :=
    mappingTorusMk_surjective (sphereData period hPeriod) quotientPoint
  have hProjection :
      IsLocalDiffeomorph coverModelWithCorners coverModelWithCorners ω
        (mappingTorusMk (sphereData period hPeriod)) :=
    reflectedSphere_projection_isLocalDiffeomorph period hPeriod
  have hAt := hProjection coverPoint
  have hLocal :
      ContMDiffAt coverModelWithCorners 𝓘(ℝ, Fiber) ω
        (field.toFun ∘ hAt.localInverse)
        (mappingTorusMk (sphereData period hPeriod) coverPoint) :=
    field.contMDiff_toFun.contMDiffAt.comp _
      hAt.localInverse_contMDiffAt
  apply hLocal.congr_of_eventuallyEq
  filter_upwards [hAt.localInverse_eventuallyEq_right] with point hPoint
  change descend period hPeriod Fiber field point =
    field (hAt.localInverse point)
  have hPoint' :
      mappingTorusMk (sphereData period hPeriod) (hAt.localInverse point) =
        point := by
    simpa [Function.comp_def] using hPoint
  calc
    descend period hPeriod Fiber field point =
        descend period hPeriod Fiber field
          (mappingTorusMk (sphereData period hPeriod)
            (hAt.localInverse point)) := congrArg _ hPoint'.symm
    _ = field (hAt.localInverse point) :=
      descend_mk period hPeriod Fiber field (hAt.localInverse point)

/-- Smooth descent as a map between the two field spaces. -/
def descendSmooth
    (field : SmoothDeckInvariantField period hPeriod Fiber) :
    SmoothQuotientField period hPeriod Fiber where
  toFun := descend period hPeriod Fiber field
  contMDiff_toFun := contMDiff_descend period hPeriod Fiber field

/-- Pullback of a smooth quotient field along the analytic covering map. -/
def liftSmooth
    (field : SmoothQuotientField period hPeriod Fiber) :
    SmoothDeckInvariantField period hPeriod Fiber where
  toFun := field ∘ mappingTorusMk (sphereData period hPeriod)
  contMDiff_toFun := by
    have hProjection :
        ContMDiff coverModelWithCorners coverModelWithCorners ω
          (mappingTorusMk (sphereData period hPeriod)) :=
      (reflectedSphere_projection_isLocalDiffeomorph period hPeriod).contMDiff
    exact field.contMDiff_toFun.comp hProjection
  deck_invariant := by
    intro winding point
    apply congrArg field.toFun
    apply (mappingTorusMk_eq_iff_exists_vadd
      (sphereData period hPeriod) _ _).2
    exact ⟨winding, rfl⟩

@[simp]
theorem liftSmooth_apply
    (field : SmoothQuotientField period hPeriod Fiber)
    (point : EffectiveCover period hPeriod) :
    liftSmooth period hPeriod Fiber field point =
      field (mappingTorusMk (sphereData period hPeriod) point) :=
  rfl

/-- Smooth descent and pullback are inverse field-space constructions. -/
def smoothDeckInvariantEquivSmoothQuotient :
    SmoothDeckInvariantField period hPeriod Fiber ≃
      SmoothQuotientField period hPeriod Fiber where
  toFun := descendSmooth period hPeriod Fiber
  invFun := liftSmooth period hPeriod Fiber
  left_inv := by
    intro field
    apply SmoothDeckInvariantField.ext period hPeriod Fiber
    intro point
    rfl
  right_inv := by
    intro field
    apply SmoothQuotientField.ext period hPeriod Fiber
    intro quotientPoint
    obtain ⟨coverPoint, rfl⟩ :=
      mappingTorusMk_surjective (sphereData period hPeriod) quotientPoint
    rfl

/-- The flat two-metric/two-scalar/root witness therefore lives on the actual
smooth quotient, not only on its cover. -/
def flatSmoothQuotientConfiguration :
    (SmoothQuotientField period hPeriod
      (EuclideanSpace ℝ (Fin 4 × Fin 4))) ×
    (SmoothQuotientField period hPeriod
      (EuclideanSpace ℝ (Fin 4 × Fin 4))) ×
    SmoothQuotientField period hPeriod ℝ ×
    SmoothQuotientField period hPeriod ℝ ×
    SmoothQuotientField period hPeriod
      (EuclideanSpace ℝ (Fin 4 × Fin 4)) :=
  let configuration := flatSmoothConfiguration period hPeriod
  (descendSmooth period hPeriod _ configuration.gPlus,
    descendSmooth period hPeriod _ configuration.gMinus,
    descendSmooth period hPeriod _ configuration.psiPlus,
    descendSmooth period hPeriod _ configuration.psiMinus,
    descendSmooth period hPeriod _ configuration.root)

end

end P0EFTJanusMappingTorusSmoothFieldDescent4D
end JanusFormal
