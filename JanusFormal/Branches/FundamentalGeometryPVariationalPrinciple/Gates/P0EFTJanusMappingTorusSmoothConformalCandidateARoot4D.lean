import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

/-! # Smooth conformal Candidate-A root family -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSmoothConformalCandidateARoot4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusIntrinsicConformalCandidateARoot4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The positive relative conformal factor is a genuine smooth scalar field. -/
def conformalRelativeRatioField
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point) :
    SmoothScalarField period hPeriod where
  toFun := fun point => minus point / plus point
  contMDiff_toFun :=
    minus.contMDiff_toFun.div₀ plus.contMDiff_toFun
      (fun point => ne_of_gt (hPlus point))

theorem conformalRelativeRatioField_pos
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point) (point) :
    0 < conformalRelativeRatioField period hPeriod plus minus hPlus point :=
  div_pos (hMinus point) (hPlus point)

/-- Smooth scalar coefficient of the conformal principal-root family. -/
def smoothConformalCandidateARootScale
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point) :
    SmoothScalarField period hPeriod where
  toFun := fun point => Real.sqrt
    (conformalRelativeRatioField period hPeriod plus minus hPlus point)
  contMDiff_toFun := by
    intro point
    exact
      (Real.contDiffAt_sqrt (ne_of_gt
        (conformalRelativeRatioField_pos period hPeriod plus minus hPlus hMinus
          point))).contMDiffAt.comp point
        (conformalRelativeRatioField period hPeriod plus minus hPlus).contMDiff_toFun.contMDiffAt

@[simp] theorem smoothConformalCandidateARootScale_apply
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point) (point) :
    smoothConformalCandidateARootScale period hPeriod plus minus hPlus hMinus
        point =
      Real.sqrt (minus point / plus point) :=
  rfl

/-- The former pointwise root is exactly the smooth scalar family times the
identity endomorphism. -/
theorem conformalCandidateARootAt_eq_smooth_scale
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point) (point) :
    conformalCandidateARootAt period hPeriod plus minus point =
      smoothConformalCandidateARootScale period hPeriod plus minus hPlus hMinus
          point • ContinuousLinearMap.id Real _ :=
  rfl

theorem smoothConformalCandidateARootScale_square
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point) (point) :
    smoothConformalCandidateARootScale period hPeriod plus minus hPlus hMinus
          point ^ 2 =
      minus point / plus point := by
  rw [smoothConformalCandidateARootScale_apply, sq]
  exact Real.mul_self_sqrt
    (div_nonneg (le_of_lt (hMinus point)) (le_of_lt (hPlus point)))

/-- Smooth tangent sections of the effective D8 quotient. -/
abbrev SmoothAmbientTangentSection :=
  ContMDiffSection coverModelWithCorners CoverCoordinates ∞
    (fun point : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners point)

/-- The conformal root sends every smooth tangent section to a smooth tangent
section, which certifies the bundlewise smooth action of the root family. -/
def smoothConformalCandidateARootAction
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point)
    (vector : SmoothAmbientTangentSection period hPeriod) :
    SmoothAmbientTangentSection period hPeriod where
  toFun := fun point =>
    smoothConformalCandidateARootScale period hPeriod plus minus hPlus hMinus
      point • vector point
  contMDiff_toFun :=
    (smoothConformalCandidateARootScale period hPeriod plus minus hPlus hMinus).contMDiff_toFun.smul_section
      vector.contMDiff

@[simp] theorem smoothConformalCandidateARootAction_apply
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point)
    (vector : SmoothAmbientTangentSection period hPeriod) (point) :
    smoothConformalCandidateARootAction period hPeriod plus minus hPlus hMinus
        vector point =
      conformalCandidateARootAt period hPeriod plus minus point
        (vector point) := by
  change
    smoothConformalCandidateARootScale period hPeriod plus minus hPlus hMinus
        point • vector point =
      Real.sqrt (minus point / plus point) • vector point
  rw [smoothConformalCandidateARootScale_apply]

/-- The smooth root action is linear on global smooth tangent sections. -/
def smoothConformalCandidateARootOperator
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point) :
    SmoothAmbientTangentSection period hPeriod →ₗ[Real]
      SmoothAmbientTangentSection period hPeriod where
  toFun := smoothConformalCandidateARootAction period hPeriod plus minus hPlus hMinus
  map_add' := by
    intro first second
    ext point
    simp [smoothConformalCandidateARootAction, smul_add]
  map_smul' := by
    intro scalar vector
    ext point
    simp [smoothConformalCandidateARootAction, smul_smul, mul_comm]

/-- Smooth action of the genuine conformal relative endomorphism
`g₊⁻¹ g₋ = (b/a) id`. -/
def smoothConformalRelativeAction
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (vector : SmoothAmbientTangentSection period hPeriod) :
    SmoothAmbientTangentSection period hPeriod where
  toFun := fun point =>
    conformalRelativeRatioField period hPeriod plus minus hPlus point •
      vector point
  contMDiff_toFun :=
    (conformalRelativeRatioField period hPeriod plus minus hPlus).contMDiff_toFun.smul_section
      vector.contMDiff

/-- Global linear operator induced by the relative conformal endomorphism. -/
def smoothConformalRelativeOperator
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point) :
    SmoothAmbientTangentSection period hPeriod →ₗ[Real]
      SmoothAmbientTangentSection period hPeriod where
  toFun := smoothConformalRelativeAction period hPeriod plus minus hPlus
  map_add' := by
    intro first second
    ext point
    simp [smoothConformalRelativeAction, smul_add]
  map_smul' := by
    intro scalar vector
    ext point
    simp [smoothConformalRelativeAction, smul_smul, mul_comm]

/-- Exact square equation on the global space of smooth tangent sections. -/
theorem smoothConformalCandidateARootOperator_square
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point) :
    (smoothConformalCandidateARootOperator period hPeriod plus minus hPlus
      hMinus).comp
        (smoothConformalCandidateARootOperator period hPeriod plus minus hPlus
          hMinus) =
      smoothConformalRelativeOperator period hPeriod plus minus hPlus := by
  apply LinearMap.ext
  intro vector
  ext point
  change
    smoothConformalCandidateARootScale period hPeriod plus minus hPlus hMinus
        point •
        (smoothConformalCandidateARootScale period hPeriod plus minus hPlus
          hMinus point • vector point) =
      conformalRelativeRatioField period hPeriod plus minus hPlus point •
        vector point
  rw [smul_smul, ← sq,
    smoothConformalCandidateARootScale_square]
  rfl

end
end P0EFTJanusMappingTorusSmoothConformalCandidateARoot4D
end JanusFormal
