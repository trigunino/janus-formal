import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGradedScalarGhostAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D

/-!
# Scalar Chevalley--Eilenberg closure on the D8 quotient

The manifold Lie bracket acts on genuine global `C∞` scalar fields through
directional differentiation.  The representation identity is derived from
Mathlib's intrinsic `mlieBracket` Leibniz and Jacobi identities.  A finite
global spanning family cancels the auxiliary tangent vector without assuming
a global frame.  This closes `d¹ ∘ d⁰` on scalar fields.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGhostCEClosure4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusGradedScalarGhostAction4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Pointwise multiplication of a smooth scalar and a smooth tangent ghost. -/
def cInfinityScalarSmulGhost
    (scalar : CInfinityScalarField period hPeriod)
    (ghost : CInfinityDiffeomorphismGhost period hPeriod) :
    CInfinityDiffeomorphismGhost period hPeriod where
  toFun := fun point => scalar point • ghost point
  contMDiff_toFun := scalar.contMDiff.smul_section ghost.contMDiff

@[simp]
theorem cInfinityScalarSmulGhost_apply
    (scalar : CInfinityScalarField period hPeriod)
    (ghost : CInfinityDiffeomorphismGhost period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    cInfinityScalarSmulGhost period hPeriod scalar ghost point =
      scalar point • ghost point :=
  rfl

theorem cInfinityScalarSmulGhost_addGhost
    (scalar : CInfinityScalarField period hPeriod)
    (first second : CInfinityDiffeomorphismGhost period hPeriod) :
    cInfinityScalarSmulGhost period hPeriod scalar (first + second) =
      cInfinityScalarSmulGhost period hPeriod scalar first +
        cInfinityScalarSmulGhost period hPeriod scalar second := by
  apply ContMDiffSection.ext
  intro point
  exact smul_add _ _ _

/-- Intrinsic Leibniz rule `[X, fY] = (L_X f)Y + f[X,Y]`. -/
theorem smoothGhostLieBracket_scalarSmul_right
    (first second : CInfinityDiffeomorphismGhost period hPeriod)
    (scalar : CInfinityScalarField period hPeriod) :
    smoothGhostLieBracket period hPeriod first
        (cInfinityScalarSmulGhost period hPeriod scalar second) =
      cInfinityScalarSmulGhost period hPeriod
          (cInfinityScalarLieDerivative period hPeriod first scalar) second +
        cInfinityScalarSmulGhost period hPeriod scalar
          (smoothGhostLieBracket period hPeriod first second) := by
  apply ContMDiffSection.ext
  intro point
  exact VectorField.mlieBracket_smul_right
    (scalar.contMDiff.mdifferentiableAt (by simp))
    (second.contMDiff.mdifferentiableAt (by simp))

theorem smoothGhostLieBracket_smul_left
    (coefficient : Real)
    (first second : CInfinityDiffeomorphismGhost period hPeriod) :
    smoothGhostLieBracket period hPeriod (coefficient • first) second =
      coefficient • smoothGhostLieBracket period hPeriod first second := by
  apply ContMDiffSection.ext
  intro point
  exact VectorField.mlieBracket_const_smul_left
    (first.contMDiff.mdifferentiableAt (by simp))

theorem smoothGhostLieBracket_smul_right
    (coefficient : Real)
    (first second : CInfinityDiffeomorphismGhost period hPeriod) :
    smoothGhostLieBracket period hPeriod first (coefficient • second) =
      coefficient • smoothGhostLieBracket period hPeriod first second := by
  apply ContMDiffSection.ext
  intro point
  exact VectorField.mlieBracket_const_smul_right
    (second.contMDiff.mdifferentiableAt (by simp))

/-- The intrinsic smooth ghost bracket, bundled as a bilinear map. -/
def smoothGhostLieBracketBilinear :
    CInfinityDiffeomorphismGhost period hPeriod →ₗ[Real]
      (CInfinityDiffeomorphismGhost period hPeriod →ₗ[Real]
        CInfinityDiffeomorphismGhost period hPeriod) where
  toFun first :=
    { toFun := smoothGhostLieBracket period hPeriod first
      map_add' := smoothGhostLieBracket_add_right period hPeriod first
      map_smul' := fun coefficient second =>
        smoothGhostLieBracket_smul_right period hPeriod coefficient first second }
  map_add' first second := by
    apply LinearMap.ext
    intro third
    exact smoothGhostLieBracket_add_left period hPeriod first second third
  map_smul' coefficient first := by
    apply LinearMap.ext
    intro second
    exact smoothGhostLieBracket_smul_left period hPeriod coefficient first second

@[simp]
theorem smoothGhostLieBracketBilinear_apply
    (first second : CInfinityDiffeomorphismGhost period hPeriod) :
    smoothGhostLieBracketBilinear period hPeriod first second =
      smoothGhostLieBracket period hPeriod first second :=
  rfl

/-- Each member of the existing finite spanning family is a genuine `C∞`
ghost. -/
def finiteGeneratorCInfinityGhost
    (index : Fin (finiteSmoothTangentFrame period hPeriod).count) :
    CInfinityDiffeomorphismGhost period hPeriod where
  toFun := fun point =>
    (finiteSmoothTangentFrame period hPeriod).vectorAt point index
  contMDiff_toFun :=
    (finiteSmoothTangentFrame period hPeriod).contMDiff_vector index

private theorem exists_finiteGeneratorCInfinityGhost_ne_zero_at
    (point : EffectiveQuotient period hPeriod) :
    ∃ index : Fin (finiteSmoothTangentFrame period hPeriod).count,
      finiteGeneratorCInfinityGhost period hPeriod index point ≠ 0 := by
  by_contra hExists
  have hAllZero : ∀ index : Fin (finiteSmoothTangentFrame period hPeriod).count,
      (finiteSmoothTangentFrame period hPeriod).vectorAt point index = 0 := by
    intro index
    by_contra hNonzero
    exact hExists ⟨index, hNonzero⟩
  have hSpanLe : Submodule.span Real
      (Set.range ((finiteSmoothTangentFrame period hPeriod).vectorAt point)) ≤ ⊥ := by
    apply Submodule.span_le.mpr
    rintro vector ⟨index, rfl⟩
    rw [hAllZero index]
    exact Submodule.zero_mem ⊥
  have hTopLe : (⊤ : Submodule Real
      (TangentSpace coverModelWithCorners point)) ≤ ⊥ := by
    rw [← (finiteSmoothTangentFrame period hPeriod).spansAt point]
    exact hSpanLe
  let vertical : TangentSpace coverModelWithCorners point := (0, 1)
  have hVerticalNe : vertical ≠ 0 := by
    intro hZero
    have hSecond := congrArg
      (fun vector : TangentSpace coverModelWithCorners point => vector.2) hZero
    change (1 : Real) = 0 at hSecond
    norm_num at hSecond
  have hVerticalZero : vertical = 0 := by
    have hVerticalMem : vertical ∈ (⊥ : Submodule Real
        (TangentSpace coverModelWithCorners point)) :=
      hTopLe Submodule.mem_top
    simpa using hVerticalMem
  exact hVerticalNe hVerticalZero

/-- Directional differentiation is a representation of the actual intrinsic
Lie bracket on global smooth scalar fields. -/
theorem cInfinityScalarLieDerivative_bracket
    (first second : CInfinityDiffeomorphismGhost period hPeriod)
    (scalar : CInfinityScalarField period hPeriod) :
    cInfinityScalarLieDerivative period hPeriod
        (smoothGhostLieBracket period hPeriod first second) scalar =
      cInfinityScalarLieDerivative period hPeriod first
          (cInfinityScalarLieDerivative period hPeriod second scalar) -
        cInfinityScalarLieDerivative period hPeriod second
          (cInfinityScalarLieDerivative period hPeriod first scalar) := by
  apply ContMDiffMap.ext
  intro point
  obtain ⟨index, hIndex⟩ :=
    exists_finiteGeneratorCInfinityGhost_ne_zero_at period hPeriod point
  let third := finiteGeneratorCInfinityGhost period hPeriod index
  have hJacobi := smoothGhostLieBracket_jacobi period hPeriod first second
    (cInfinityScalarSmulGhost period hPeriod scalar third)
  rw [smoothGhostLieBracket_scalarSmul_right period hPeriod second third scalar,
    smoothGhostLieBracket_add_right period hPeriod,
    smoothGhostLieBracket_scalarSmul_right period hPeriod first third
      (cInfinityScalarLieDerivative period hPeriod second scalar),
    smoothGhostLieBracket_scalarSmul_right period hPeriod first
      (smoothGhostLieBracket period hPeriod second third) scalar,
    smoothGhostLieBracket_scalarSmul_right period hPeriod
      (smoothGhostLieBracket period hPeriod first second) third scalar,
    smoothGhostLieBracket_scalarSmul_right period hPeriod first third scalar,
    smoothGhostLieBracket_add_right period hPeriod,
    smoothGhostLieBracket_scalarSmul_right period hPeriod second third
      (cInfinityScalarLieDerivative period hPeriod first scalar),
    smoothGhostLieBracket_scalarSmul_right period hPeriod second
      (smoothGhostLieBracket period hPeriod first third) scalar,
    smoothGhostLieBracket_jacobi period hPeriod first second third,
    cInfinityScalarSmulGhost_addGhost] at hJacobi
  have hGhost :
      cInfinityScalarSmulGhost period hPeriod
          (cInfinityScalarLieDerivative period hPeriod first
            (cInfinityScalarLieDerivative period hPeriod second scalar)) third =
        cInfinityScalarSmulGhost period hPeriod
            (cInfinityScalarLieDerivative period hPeriod
              (smoothGhostLieBracket period hPeriod first second) scalar) third +
          cInfinityScalarSmulGhost period hPeriod
            (cInfinityScalarLieDerivative period hPeriod second
              (cInfinityScalarLieDerivative period hPeriod first scalar)) third := by
    let leading := cInfinityScalarSmulGhost period hPeriod
      (cInfinityScalarLieDerivative period hPeriod first
        (cInfinityScalarLieDerivative period hPeriod second scalar)) third
    let sharedFirst := cInfinityScalarSmulGhost period hPeriod
      (cInfinityScalarLieDerivative period hPeriod second scalar)
      (smoothGhostLieBracket period hPeriod first third)
    let sharedSecond := cInfinityScalarSmulGhost period hPeriod
      (cInfinityScalarLieDerivative period hPeriod first scalar)
      (smoothGhostLieBracket period hPeriod second third)
    let sharedThird := cInfinityScalarSmulGhost period hPeriod scalar
      (smoothGhostLieBracket period hPeriod
        (smoothGhostLieBracket period hPeriod first second) third)
    let sharedFourth := cInfinityScalarSmulGhost period hPeriod scalar
      (smoothGhostLieBracket period hPeriod second
        (smoothGhostLieBracket period hPeriod first third))
    let remainder := cInfinityScalarSmulGhost period hPeriod
        (cInfinityScalarLieDerivative period hPeriod
          (smoothGhostLieBracket period hPeriod first second) scalar) third +
      cInfinityScalarSmulGhost period hPeriod
        (cInfinityScalarLieDerivative period hPeriod second
          (cInfinityScalarLieDerivative period hPeriod first scalar)) third
    let common := sharedFirst + sharedSecond + sharedThird + sharedFourth
    have hCancelled := congrArg
      (fun ghost : CInfinityDiffeomorphismGhost period hPeriod => ghost - common)
      hJacobi
    have hLeading : leading = remainder := by
      calc
        leading = _ := by
          dsimp [leading, sharedFirst, sharedSecond, sharedThird, sharedFourth,
            common]
          abel
        _ = _ := hCancelled
        _ = remainder := by
          dsimp [remainder, sharedFirst, sharedSecond, sharedThird, sharedFourth,
            common]
          abel
    simpa [leading, remainder] using hLeading
  have hPoint := congrArg
    (fun ghost : CInfinityDiffeomorphismGhost period hPeriod => ghost point)
    hGhost
  have hPoint' :
      cInfinityScalarLieDerivative period hPeriod first
            (cInfinityScalarLieDerivative period hPeriod second scalar) point •
          third point =
        (cInfinityScalarLieDerivative period hPeriod
              (smoothGhostLieBracket period hPeriod first second) scalar point +
          cInfinityScalarLieDerivative period hPeriod second
            (cInfinityScalarLieDerivative period hPeriod first scalar) point) •
          third point := by
    simpa [cInfinityScalarSmulGhost, add_smul] using hPoint
  have hScalar := smul_left_injective Real hIndex hPoint'
  change
    cInfinityScalarLieDerivative period hPeriod
        (smoothGhostLieBracket period hPeriod first second) scalar point =
      cInfinityScalarLieDerivative period hPeriod first
          (cInfinityScalarLieDerivative period hPeriod second scalar) point -
        cInfinityScalarLieDerivative period hPeriod second
          (cInfinityScalarLieDerivative period hPeriod first scalar) point
  linarith

/-- Degree-one scalar Chevalley--Eilenberg differential. -/
def cInfinityScalarCEDifferentialOne
    (cochain : CInfinityDiffeomorphismGhost period hPeriod →ₗ[Real]
      CInfinityScalarField period hPeriod) :
    CInfinityDiffeomorphismGhost period hPeriod →ₗ[Real]
      (CInfinityDiffeomorphismGhost period hPeriod →ₗ[Real]
        CInfinityScalarField period hPeriod) :=
  LinearMap.mk₂ Real
    (fun first second =>
      cInfinityScalarLieDerivative period hPeriod first (cochain second) -
        cInfinityScalarLieDerivative period hPeriod second (cochain first) -
          cochain (smoothGhostLieBracket period hPeriod first second))
    (by
      intro first second third
      simp only [map_add,
        cInfinityScalarLieDerivative_addGhost,
        cInfinityScalarLieDerivative_addScalar,
        smoothGhostLieBracket_add_left]
      module)
    (by
      intro coefficient first second
      simp only [map_smul,
        cInfinityScalarLieDerivative_smulGhost,
        cInfinityScalarLieDerivative_smulScalar,
        smoothGhostLieBracket_smul_left]
      module)
    (by
      intro first second third
      simp only [map_add,
        cInfinityScalarLieDerivative_addGhost,
        cInfinityScalarLieDerivative_addScalar,
        smoothGhostLieBracket_add_right]
      module)
    (by
      intro coefficient first second
      simp only [map_smul,
        cInfinityScalarLieDerivative_smulGhost,
        cInfinityScalarLieDerivative_smulScalar,
        smoothGhostLieBracket_smul_right]
      module)

@[simp]
theorem cInfinityScalarCEDifferentialOne_apply
    (cochain : CInfinityDiffeomorphismGhost period hPeriod →ₗ[Real]
      CInfinityScalarField period hPeriod)
    (first second : CInfinityDiffeomorphismGhost period hPeriod) :
    cInfinityScalarCEDifferentialOne period hPeriod cochain first second =
      cInfinityScalarLieDerivative period hPeriod first (cochain second) -
        cInfinityScalarLieDerivative period hPeriod second (cochain first) -
          cochain (smoothGhostLieBracket period hPeriod first second) :=
  rfl

/-- Exact scalar CE closure `d¹(d⁰ scalar) = 0`. -/
theorem cInfinityScalarCEDifferentialOne_differentialZero
    (scalar : CInfinityScalarField period hPeriod) :
    cInfinityScalarCEDifferentialOne period hPeriod
        (cInfinityScalarCEDifferentialZero period hPeriod scalar) = 0 := by
  apply LinearMap.ext
  intro first
  apply LinearMap.ext
  intro second
  change
    cInfinityScalarLieDerivative period hPeriod first
          (cInfinityScalarLieDerivative period hPeriod second scalar) -
        cInfinityScalarLieDerivative period hPeriod second
          (cInfinityScalarLieDerivative period hPeriod first scalar) -
      cInfinityScalarLieDerivative period hPeriod
        (smoothGhostLieBracket period hPeriod first second) scalar = 0
  rw [cInfinityScalarLieDerivative_bracket]
  module

theorem scalar_ghost_ce_closure4D :
    ∀ scalar : CInfinityScalarField period hPeriod,
      cInfinityScalarCEDifferentialOne period hPeriod
          (cInfinityScalarCEDifferentialZero period hPeriod scalar) = 0 :=
  cInfinityScalarCEDifferentialOne_differentialZero period hPeriod

end

end P0EFTJanusMappingTorusScalarGhostCEClosure4D
end JanusFormal
