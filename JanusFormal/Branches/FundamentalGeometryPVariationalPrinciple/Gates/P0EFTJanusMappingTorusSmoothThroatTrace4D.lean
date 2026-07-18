import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothPTFieldAction4D

/-!
# Smooth throat trace on the effective D8 quotient

Restriction along the actual smooth closed throat inclusion gives a genuine
trace of smooth quotient coefficient fields. It is PT-equivariant and supplies
nonempty exact Dirichlet conditions. This is not a Sobolev trace theorem.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSmoothThroatTrace4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusPTInvolution
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothPTInvolution
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothPTFieldAction4D

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

universe u

variable (Fiber : Type u)
  [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

/-- Genuine smooth coefficient fields on the three-dimensional throat. -/
structure SmoothThroatField where
  toFun : EffectiveThroat period hPeriod -> Fiber
  contMDiff_toFun :
    ContMDiff throatCoverModelWithCorners 𝓘(Real, Fiber) ∞ toFun

instance : CoeFun (SmoothThroatField period hPeriod Fiber)
    (fun _ => EffectiveThroat period hPeriod -> Fiber) :=
  ⟨SmoothThroatField.toFun⟩

@[ext]
theorem SmoothThroatField.ext
    {first second : SmoothThroatField period hPeriod Fiber}
    (hEqual : forall point, first point = second point) : first = second := by
  cases first with
  | mk firstFun firstSmooth =>
    cases second with
    | mk secondFun secondSmooth =>
      have hFun : firstFun = secondFun := funext hEqual
      subst secondFun
      rfl

/-- Restriction of a smooth spacetime field to the actual embedded throat. -/
def throatTrace
    (field : SmoothQuotientField period hPeriod Fiber) :
    SmoothThroatField period hPeriod Fiber where
  toFun := field.toFun ∘ fixedThroatQuotientInclusion period hPeriod
  contMDiff_toFun := field.contMDiff_toFun.comp
    ((fixedThroatQuotientInclusion_contMDiff period hPeriod).of_le (by simp))

@[simp]
theorem throatTrace_apply
    (field : SmoothQuotientField period hPeriod Fiber)
    (point : EffectiveThroat period hPeriod) :
    throatTrace period hPeriod Fiber field point =
      field (fixedThroatQuotientInclusion period hPeriod point) :=
  rfl

/-- PT pullback on smooth throat fields. -/
def throatPTPullback
    (field : SmoothThroatField period hPeriod Fiber) :
    SmoothThroatField period hPeriod Fiber where
  toFun := field.toFun ∘ fixedThroatPT period hPeriod
  contMDiff_toFun := field.contMDiff_toFun.comp
    ((fixedThroatPT_contMDiff period hPeriod).of_le (by simp))

@[simp]
theorem throatPTPullback_apply
    (field : SmoothThroatField period hPeriod Fiber)
    (point : EffectiveThroat period hPeriod) :
    throatPTPullback period hPeriod Fiber field point =
      field (fixedThroatPT period hPeriod point) :=
  rfl

theorem throatPTPullback_involutive
    (field : SmoothThroatField period hPeriod Fiber) :
    throatPTPullback period hPeriod Fiber
      (throatPTPullback period hPeriod Fiber field) = field := by
  apply SmoothThroatField.ext period hPeriod Fiber
  intro point
  simp [throatPTPullback_apply, fixedThroatPT_involutive]

/-- Smooth restriction commutes exactly with the global PT involutions. -/
theorem throatTrace_pt_equivariant
    (field : SmoothQuotientField period hPeriod Fiber) :
    throatTrace period hPeriod Fiber
        (ptPullback period hPeriod Fiber field) =
      throatPTPullback period hPeriod Fiber
        (throatTrace period hPeriod Fiber field) := by
  apply SmoothThroatField.ext period hPeriod Fiber
  intro point
  simp only [throatTrace_apply, ptPullback_apply, throatPTPullback_apply]
  rw [fixedThroatQuotientInclusion_pt_equivariant]

/-- Exact smooth Dirichlet data on the embedded throat. -/
def SatisfiesDirichlet
    (boundary : SmoothThroatField period hPeriod Fiber)
    (field : SmoothQuotientField period hPeriod Fiber) : Prop :=
  throatTrace period hPeriod Fiber field = boundary

theorem satisfiesDirichlet_pt
    {boundary : SmoothThroatField period hPeriod Fiber}
    {field : SmoothQuotientField period hPeriod Fiber}
    (hBoundary : SatisfiesDirichlet period hPeriod Fiber boundary field) :
    SatisfiesDirichlet period hPeriod Fiber
      (throatPTPullback period hPeriod Fiber boundary)
      (ptPullback period hPeriod Fiber field) := by
  unfold SatisfiesDirichlet at hBoundary ⊢
  rw [throatTrace_pt_equivariant, hBoundary]

/-- Every global smooth field gives an admissible, hence nonempty, exact
Dirichlet pair on the same quotient and throat. -/
def inducedDirichletPair
    (field : SmoothQuotientField period hPeriod Fiber) :
    SmoothThroatField period hPeriod Fiber ×
      SmoothQuotientField period hPeriod Fiber :=
  (throatTrace period hPeriod Fiber field, field)

theorem inducedDirichletPair_satisfies
    (field : SmoothQuotientField period hPeriod Fiber) :
    SatisfiesDirichlet period hPeriod Fiber
      (inducedDirichletPair period hPeriod Fiber field).1
      (inducedDirichletPair period hPeriod Fiber field).2 :=
  rfl

end

end P0EFTJanusMappingTorusSmoothThroatTrace4D
end JanusFormal
