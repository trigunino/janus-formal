import Mathlib.LinearAlgebra.TensorProduct.Map
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGradedGhostCoefficientWitness4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D

/-!
# Graded diffeomorphism-ghost tensor space

This gate couples the explicit odd coefficient algebra to genuine global
`C∞` tangent ghosts by a tensor product.  Left multiplication by the first odd
generator induces a nontrivial coefficient differential whose square vanishes
on the whole coupled space.  This is not yet the full nonlinear BRST/BV
differential on fields.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusGradedDiffeomorphismGhostTensor4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff TensorProduct
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusLinearizedDiffeomorphismBRST4D
open P0EFTJanusGradedGhostCoefficientWitness4D
open P0EFTJanusMappingTorusSmoothDiffeomorphismGhostLieBracket4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

/-- Odd coefficients tensored with genuine global `C∞` tangent ghosts. -/
abbrev GradedDiffeomorphismGhostModule :=
  OddCoefficientMatrix ⊗[Real]
    CInfinityDiffeomorphismGhost period hPeriod

/-- The odd coefficient differential, acting trivially on the tangent-ghost
factor. -/
def gradedGhostCoefficientDifferential :
    GradedDiffeomorphismGhostModule period hPeriod →ₗ[Real]
      GradedDiffeomorphismGhostModule period hPeriod :=
  TensorProduct.map oddCoefficientDifferential LinearMap.id

@[simp]
theorem gradedGhostCoefficientDifferential_tmul
    (coefficient : OddCoefficientMatrix)
    (ghost : CInfinityDiffeomorphismGhost period hPeriod) :
    gradedGhostCoefficientDifferential period hPeriod
        (coefficient ⊗ₜ[Real] ghost) =
      oddCoefficientDifferential coefficient ⊗ₜ[Real] ghost := by
  simp [gradedGhostCoefficientDifferential]

/-- Nilpotence holds on every coupled coefficient--ghost tensor. -/
theorem gradedGhostCoefficientDifferential_sq
    (term : GradedDiffeomorphismGhostModule period hPeriod) :
    gradedGhostCoefficientDifferential period hPeriod
        (gradedGhostCoefficientDifferential period hPeriod term) = 0 := by
  refine TensorProduct.induction_on term ?_ ?_ ?_
  · simp
  · intro coefficient ghost
    simp [oddCoefficientDifferential_sq]
  · intro first second hFirst hSecond
    simp only [map_add]
    rw [hFirst, hSecond, add_zero]

/-- The conventional quadratic odd coefficient coupled to the actual intrinsic
Lie bracket of two global `C∞` tangent ghosts. -/
def gradedQuadraticGhostBracketTerm
    (first second : CInfinityDiffeomorphismGhost period hPeriod) :
    GradedDiffeomorphismGhostModule period hPeriod :=
  gradedQuadraticGhostBRSTCoefficient ⊗ₜ[Real]
    smoothGhostLieBracket period hPeriod first second

/-- The same coupled term starting from the analytic ghosts already stored in
the independent field configuration. -/
def analyticGradedQuadraticGhostBracketTerm
    (first second : SmoothDiffeomorphismGhost period hPeriod) :
    GradedDiffeomorphismGhostModule period hPeriod :=
  gradedQuadraticGhostBracketTerm period hPeriod
    (smoothGhostToCInfinity period hPeriod first)
    (smoothGhostToCInfinity period hPeriod second)

@[simp]
theorem gradedQuadraticGhostBracketTerm_self
    (ghost : CInfinityDiffeomorphismGhost period hPeriod) :
    gradedQuadraticGhostBracketTerm period hPeriod ghost ghost = 0 := by
  simp [gradedQuadraticGhostBracketTerm]

theorem graded_ghost_tensor4D_closure :
    (∀ term : GradedDiffeomorphismGhostModule period hPeriod,
      gradedGhostCoefficientDifferential period hPeriod
          (gradedGhostCoefficientDifferential period hPeriod term) = 0) ∧
      ∀ ghost : CInfinityDiffeomorphismGhost period hPeriod,
        gradedQuadraticGhostBracketTerm period hPeriod ghost ghost = 0 :=
  ⟨gradedGhostCoefficientDifferential_sq period hPeriod,
    gradedQuadraticGhostBracketTerm_self period hPeriod⟩

end

end P0EFTJanusMappingTorusGradedDiffeomorphismGhostTensor4D
end JanusFormal
