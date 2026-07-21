import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothConformalCandidateARoot4D

/-! # Smooth inverse of the conformal Candidate-A root family -/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSmoothConformalCandidateARootInverse4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusSmoothConformalCandidateARoot4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

theorem smoothConformalCandidateARootScale_pos
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point) (point) :
    0 < smoothConformalCandidateARootScale period hPeriod plus minus hPlus
      hMinus point := by
  rw [smoothConformalCandidateARootScale_apply]
  exact Real.sqrt_pos.2 (div_pos (hMinus point) (hPlus point))

/-- Swapping the two positive conformal factors gives the pointwise inverse
of the principal-root scale. -/
theorem smoothConformalCandidateARootScale_mul_swapped
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point) (point) :
    smoothConformalCandidateARootScale period hPeriod plus minus hPlus hMinus
        point *
      smoothConformalCandidateARootScale period hPeriod minus plus hMinus hPlus
        point = 1 := by
  have hSquare :
      (smoothConformalCandidateARootScale period hPeriod plus minus hPlus hMinus
          point *
        smoothConformalCandidateARootScale period hPeriod minus plus hMinus hPlus
          point) ^ 2 = 1 := by
    rw [mul_pow,
      smoothConformalCandidateARootScale_square period hPeriod plus minus hPlus
        hMinus point,
      smoothConformalCandidateARootScale_square period hPeriod minus plus hMinus
        hPlus point]
    field_simp [ne_of_gt (hPlus point), ne_of_gt (hMinus point)]
  have hPositive : 0 <
      smoothConformalCandidateARootScale period hPeriod plus minus hPlus hMinus
          point *
        smoothConformalCandidateARootScale period hPeriod minus plus hMinus hPlus
          point :=
    mul_pos
      (smoothConformalCandidateARootScale_pos period hPeriod plus minus hPlus
        hMinus point)
      (smoothConformalCandidateARootScale_pos period hPeriod minus plus hMinus
        hPlus point)
  nlinarith

/-- The inverse family is itself a smooth root action, with the factors
exchanged. -/
def smoothConformalCandidateARootInverseOperator
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point) :
    SmoothAmbientTangentSection period hPeriod →ₗ[Real]
      SmoothAmbientTangentSection period hPeriod :=
  smoothConformalCandidateARootOperator period hPeriod minus plus hMinus hPlus

theorem smoothConformalCandidateARootInverseOperator_left
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point) :
    (smoothConformalCandidateARootInverseOperator period hPeriod plus minus hPlus
      hMinus).comp
        (smoothConformalCandidateARootOperator period hPeriod plus minus hPlus
          hMinus) = LinearMap.id := by
  apply LinearMap.ext
  intro vector
  ext point
  change
    smoothConformalCandidateARootScale period hPeriod minus plus hMinus hPlus
        point •
      (smoothConformalCandidateARootScale period hPeriod plus minus hPlus hMinus
        point • vector point) = vector point
  rw [smul_smul, mul_comm,
    smoothConformalCandidateARootScale_mul_swapped, one_smul]

theorem smoothConformalCandidateARootInverseOperator_right
    (plus minus : SmoothScalarField period hPeriod)
    (hPlus : ∀ point, 0 < plus point)
    (hMinus : ∀ point, 0 < minus point) :
    (smoothConformalCandidateARootOperator period hPeriod plus minus hPlus
      hMinus).comp
        (smoothConformalCandidateARootInverseOperator period hPeriod plus minus
          hPlus hMinus) = LinearMap.id := by
  apply LinearMap.ext
  intro vector
  ext point
  change
    smoothConformalCandidateARootScale period hPeriod plus minus hPlus hMinus
        point •
      (smoothConformalCandidateARootScale period hPeriod minus plus hMinus hPlus
        point • vector point) = vector point
  rw [smul_smul, smoothConformalCandidateARootScale_mul_swapped, one_smul]

end
end P0EFTJanusMappingTorusSmoothConformalCandidateARootInverse4D
end JanusFormal
