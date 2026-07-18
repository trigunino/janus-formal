import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusOrdinaryGhostNonlinearBRSTNoGo4D

/-!
# Smooth diffeomorphism-ghost Lie bracket on the D8 quotient

The genuine analytic tangent ghosts downgrade canonically to `C∞` sections.
Those sections are closed under the intrinsic manifold Lie bracket.  This gate
records antisymmetry, bilinearity and Jacobi.  Odd coefficients and the
nonlinear BRST differential remain separate inputs.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D

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

/-- The `C∞` tangent-ghost space on the actual quotient. -/
abbrev CInfinityDiffeomorphismGhost :=
  ContMDiffSection coverModelWithCorners CoverCoordinates ∞
    (fun point : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners point)

/-- Every currently implemented analytic ghost is canonically a `C∞` ghost. -/
def smoothGhostToCInfinity
    (ghost : SmoothDiffeomorphismGhost period hPeriod) :
    CInfinityDiffeomorphismGhost period hPeriod where
  toFun := ghost
  contMDiff_toFun := ghost.contMDiff.of_le (by simp)

/-- The intrinsic Lie bracket, bundled as another genuine smooth tangent ghost. -/
def smoothGhostLieBracket
    (first second : CInfinityDiffeomorphismGhost period hPeriod) :
    CInfinityDiffeomorphismGhost period hPeriod where
  toFun := VectorField.mlieBracket coverModelWithCorners first second
  contMDiff_toFun := by
    exact ContDiff.mlieBracket_vectorField
      (I := coverModelWithCorners)
      (M := EffectiveQuotient period hPeriod)
      (U := fun point => first point) (V := fun point => second point)
      (m := ⊤) (n := ⊤) first.contMDiff second.contMDiff (by
        rw [minSmoothness_of_isRCLikeNormedField]
        rfl)

@[simp]
theorem smoothGhostLieBracket_apply
    (first second : CInfinityDiffeomorphismGhost period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    smoothGhostLieBracket period hPeriod first second point =
      VectorField.mlieBracket coverModelWithCorners first second point :=
  rfl

theorem smoothGhostLieBracket_swap
    (first second : CInfinityDiffeomorphismGhost period hPeriod) :
    smoothGhostLieBracket period hPeriod first second =
      -smoothGhostLieBracket period hPeriod second first := by
  apply ContMDiffSection.ext
  intro point
  exact VectorField.mlieBracket_swap_apply

@[simp]
theorem smoothGhostLieBracket_self
    (ghost : CInfinityDiffeomorphismGhost period hPeriod) :
    smoothGhostLieBracket period hPeriod ghost ghost = 0 := by
  apply ContMDiffSection.ext
  intro point
  exact congrFun (VectorField.mlieBracket_self
    (I := coverModelWithCorners) (V := fun x => ghost x)) point

theorem smoothGhostLieBracket_add_left
    (first second third : CInfinityDiffeomorphismGhost period hPeriod) :
    smoothGhostLieBracket period hPeriod (first + second) third =
      smoothGhostLieBracket period hPeriod first third +
        smoothGhostLieBracket period hPeriod second third := by
  apply ContMDiffSection.ext
  intro point
  exact VectorField.mlieBracket_add_left
    (first.contMDiff.mdifferentiableAt (by simp))
    (second.contMDiff.mdifferentiableAt (by simp))

theorem smoothGhostLieBracket_add_right
    (first second third : CInfinityDiffeomorphismGhost period hPeriod) :
    smoothGhostLieBracket period hPeriod first (second + third) =
      smoothGhostLieBracket period hPeriod first second +
        smoothGhostLieBracket period hPeriod first third := by
  apply ContMDiffSection.ext
  intro point
  exact VectorField.mlieBracket_add_right
    (second.contMDiff.mdifferentiableAt (by simp))
    (third.contMDiff.mdifferentiableAt (by simp))

/-- Jacobi in Leibniz form for the actual global smooth tangent ghosts. -/
theorem smoothGhostLieBracket_jacobi
    (first second third : CInfinityDiffeomorphismGhost period hPeriod) :
    smoothGhostLieBracket period hPeriod first
        (smoothGhostLieBracket period hPeriod second third) =
      smoothGhostLieBracket period hPeriod
          (smoothGhostLieBracket period hPeriod first second) third +
        smoothGhostLieBracket period hPeriod second
          (smoothGhostLieBracket period hPeriod first third) := by
  apply ContMDiffSection.ext
  intro point
  have hSmooth : minSmoothness ℝ 2 ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
    exact WithTop.coe_le_coe.mpr le_top
  exact VectorField.leibniz_identity_mlieBracket_apply
    ((first.contMDiff.of_le hSmooth) point)
    ((second.contMDiff.of_le hSmooth) point)
    ((third.contMDiff.of_le hSmooth) point)

theorem smooth_diffeomorphism_ghost_lie_bracket4D_closure
    (first second third : CInfinityDiffeomorphismGhost period hPeriod) :
    smoothGhostLieBracket period hPeriod first first = 0 ∧
      smoothGhostLieBracket period hPeriod first second =
        -smoothGhostLieBracket period hPeriod second first ∧
      smoothGhostLieBracket period hPeriod first
          (smoothGhostLieBracket period hPeriod second third) =
        smoothGhostLieBracket period hPeriod
            (smoothGhostLieBracket period hPeriod first second) third +
          smoothGhostLieBracket period hPeriod second
            (smoothGhostLieBracket period hPeriod first third) :=
  ⟨smoothGhostLieBracket_self period hPeriod first,
    smoothGhostLieBracket_swap period hPeriod first second,
    smoothGhostLieBracket_jacobi period hPeriod first second third⟩

end

end P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
end JanusFormal
