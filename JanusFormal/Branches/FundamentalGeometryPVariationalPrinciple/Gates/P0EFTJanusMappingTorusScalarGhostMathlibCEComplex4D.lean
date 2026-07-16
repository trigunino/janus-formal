import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGhostCEClosure4D
import Mathlib.Algebra.Lie.Cochain

/-!
# Mathlib low-degree CE complex for scalar ghosts on D8

The intrinsic smooth vector-field bracket and its action on smooth scalars are
packaged as genuine `LieRing`, `LieAlgebra`, `LieRingModule`, and `LieModule`
instances.  Mathlib's low-degree Chevalley--Eilenberg differential therefore
applies directly and supplies `d₂₃ ∘ d₁₂ = 0` for every scalar one-cochain.
This remains an ordinary Lie-algebra CE complex, not a BV or Koszul-graded
field algebra.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGhostMathlibCEComplex4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGradedScalarGhostAction4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D
open P0EFTJanusMappingTorusScalarGhostCEClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev Ghost := CInfinityDiffeomorphismGhost period hPeriod
private abbrev Scalar := CInfinityScalarField period hPeriod

local instance ghostBracket : Bracket (Ghost period hPeriod) (Ghost period hPeriod) where
  bracket := smoothGhostLieBracket period hPeriod

local instance ghostLieRing : LieRing (Ghost period hPeriod) where
  add_lie := smoothGhostLieBracket_add_left period hPeriod
  lie_add := smoothGhostLieBracket_add_right period hPeriod
  lie_self := smoothGhostLieBracket_self period hPeriod
  leibniz_lie := smoothGhostLieBracket_jacobi period hPeriod

local instance ghostLieAlgebra : LieAlgebra Real (Ghost period hPeriod) where
  lie_smul := smoothGhostLieBracket_smul_right period hPeriod

local instance scalarBracket : Bracket (Ghost period hPeriod) (Scalar period hPeriod) where
  bracket := cInfinityScalarLieDerivative period hPeriod

local instance scalarLieRingModule :
    LieRingModule (Ghost period hPeriod) (Scalar period hPeriod) where
  add_lie := cInfinityScalarLieDerivative_addGhost period hPeriod
  lie_add := cInfinityScalarLieDerivative_addScalar period hPeriod
  leibniz_lie := by
    intro first second scalar
    change
      cInfinityScalarLieDerivative period hPeriod first
          (cInfinityScalarLieDerivative period hPeriod second scalar) =
        cInfinityScalarLieDerivative period hPeriod
            (smoothGhostLieBracket period hPeriod first second) scalar +
          cInfinityScalarLieDerivative period hPeriod second
            (cInfinityScalarLieDerivative period hPeriod first scalar)
    rw [cInfinityScalarLieDerivative_bracket]
    module

local instance scalarLieModule :
    LieModule Real (Ghost period hPeriod) (Scalar period hPeriod) where
  smul_lie := cInfinityScalarLieDerivative_smulGhost period hPeriod
  lie_smul := fun coefficient ghost scalar =>
    cInfinityScalarLieDerivative_smulScalar period hPeriod ghost coefficient scalar

/-- The hand-written degree-one differential already used by Program P is
exactly Mathlib's alternating low-degree CE differential. -/
theorem mathlib_differentialOne_val_eq
    (cochain : Ghost period hPeriod →ₗ[Real] Scalar period hPeriod) :
    (LieModule.Cohomology.d₁₂ Real (Ghost period hPeriod)
        (Scalar period hPeriod) cochain).val =
      cInfinityScalarCEDifferentialOne period hPeriod cochain := by
  apply LinearMap.ext
  intro first
  apply LinearMap.ext
  intro second
  rfl

/-- Genuine degree-two closure for every scalar one-cochain, inherited from
Mathlib after instantiating the actual D8 ghost Lie algebra and scalar module. -/
theorem scalarGhost_mathlib_d₂₃_comp_d₁₂ :
    (LieModule.Cohomology.d₂₃ Real (Ghost period hPeriod)
      (Scalar period hPeriod)) ∘ₗ
        (LieModule.Cohomology.d₁₂ Real (Ghost period hPeriod)
          (Scalar period hPeriod)) = 0 :=
  LieModule.Cohomology.d₂₃_comp_d₁₂ Real
    (Ghost period hPeriod) (Scalar period hPeriod)

/-- Pointwise form of `d₂₃(d₁₂ cochain)=0`. -/
theorem scalarGhost_mathlib_d₂₃_d₁₂_apply
    (cochain : Ghost period hPeriod →ₗ[Real] Scalar period hPeriod)
    (first second third : Ghost period hPeriod) :
    LieModule.Cohomology.d₂₃ Real (Ghost period hPeriod)
        (Scalar period hPeriod)
        (LieModule.Cohomology.d₁₂ Real (Ghost period hPeriod)
          (Scalar period hPeriod) cochain) first second third = 0 := by
  have hComposition := LinearMap.congr_fun
    (scalarGhost_mathlib_d₂₃_comp_d₁₂ period hPeriod) cochain
  have hFirst := LinearMap.congr_fun hComposition first
  have hSecond := LinearMap.congr_fun hFirst second
  exact LinearMap.congr_fun hSecond third

end

end P0EFTJanusMappingTorusScalarGhostMathlibCEComplex4D
end JanusFormal
