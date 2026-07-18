import Mathlib.Geometry.Manifold.VectorField.LieBracket
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D

/-!
# Ordinary tangent ghosts do not realize nonlinear BRST

The existing diffeomorphism ghost is an ordinary real smooth tangent section.
For such a section the ungraded Lie bracket with itself vanishes identically,
so the formal expression `s c = -1/2 [c,c]` is zero.  A nontrivial nonlinear
diffeomorphism BRST differential therefore requires odd/graded coefficients;
it cannot be obtained by silently reusing the ordinary tangent section.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusOrdinaryGhostNonlinearBRSTNoGo4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- The intrinsic self-bracket of the currently implemented, ordinary real
tangent ghost. -/
def ordinaryGhostSelfBracket
    (ghost : SmoothDiffeomorphismGhost period hPeriod) :
    (point : EffectiveQuotient period hPeriod) →
      TangentSpace coverModelWithCorners point :=
  VectorField.mlieBracket coverModelWithCorners ghost ghost

@[simp]
theorem ordinaryGhostSelfBracket_eq_zero
    (ghost : SmoothDiffeomorphismGhost period hPeriod) :
    ordinaryGhostSelfBracket period hPeriod ghost = 0 := by
  exact VectorField.mlieBracket_self

/-- The ungraded interpretation of the usual quadratic ghost formula. -/
def ordinaryQuadraticGhostBRST
    (ghost : SmoothDiffeomorphismGhost period hPeriod) :
    (point : EffectiveQuotient period hPeriod) →
      TangentSpace coverModelWithCorners point :=
  fun point => (-((2 : Real)⁻¹)) •
    ordinaryGhostSelfBracket period hPeriod ghost point

@[simp]
theorem ordinaryQuadraticGhostBRST_eq_zero
    (ghost : SmoothDiffeomorphismGhost period hPeriod) :
    ordinaryQuadraticGhostBRST period hPeriod ghost = 0 := by
  funext point
  change (-((2 : Real)⁻¹)) •
      ordinaryGhostSelfBracket period hPeriod ghost point = 0
  rw [ordinaryGhostSelfBracket_eq_zero]
  simp

/-- Exact no-go: no ordinary real tangent ghost has a nonzero quadratic BRST
variation. -/
theorem no_nontrivial_ordinaryQuadraticGhostBRST :
    ¬ ∃ ghost : SmoothDiffeomorphismGhost period hPeriod,
      ordinaryQuadraticGhostBRST period hPeriod ghost ≠ 0 := by
  rintro ⟨ghost, hNonzero⟩
  exact hNonzero (ordinaryQuadraticGhostBRST_eq_zero period hPeriod ghost)

/-- The smooth section realizing the ungraded quadratic formula is exactly the
zero tangent section already used by the linearized complex. -/
def ordinaryQuadraticGhostBRSTSection
    (_ghost : SmoothDiffeomorphismGhost period hPeriod) :
    SmoothDiffeomorphismGhost period hPeriod :=
  0

theorem ordinaryQuadraticGhostBRSTSection_toFun
    (ghost : SmoothDiffeomorphismGhost period hPeriod) :
    (ordinaryQuadraticGhostBRSTSection period hPeriod ghost :
        (point : EffectiveQuotient period hPeriod) →
          TangentSpace coverModelWithCorners point) =
      ordinaryQuadraticGhostBRST period hPeriod ghost := by
  rw [ordinaryQuadraticGhostBRST_eq_zero]
  rfl

theorem ordinary_ghost_nonlinear_brst_noGo :
    (∀ ghost : SmoothDiffeomorphismGhost period hPeriod,
        ordinaryQuadraticGhostBRST period hPeriod ghost = 0) ∧
      ¬ ∃ ghost : SmoothDiffeomorphismGhost period hPeriod,
        ordinaryQuadraticGhostBRST period hPeriod ghost ≠ 0 :=
  ⟨ordinaryQuadraticGhostBRST_eq_zero period hPeriod,
    no_nontrivial_ordinaryQuadraticGhostBRST period hPeriod⟩

end

end P0EFTJanusMappingTorusOrdinaryGhostNonlinearBRSTNoGo4D
end JanusFormal
