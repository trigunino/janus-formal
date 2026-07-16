import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGhostCEClosure4D

/-!
# Exterior-valued diffeomorphism ghosts on the D8 quotient

This gate replaces the finite matrix witness by the genuine exterior algebra
on three odd generators.  Mathlib's `ZMod 2` Clifford grading (specialized to
the zero quadratic form) gives the actual odd/even coefficient grading.

The coefficient product and the intrinsic smooth ghost Lie bracket induce the
Koszul bracket on the tensor product.  We prove its odd--odd symmetry, the
signed odd Jacobi identity, the conventional quadratic BRST ghost term, and
the resulting cubic Jacobi obstruction.  The last statement is the ghost
sector nilpotence obstruction; it is not a construction of the full BRST/BV
differential on fields and antifields.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusExteriorDiffeomorphismGhostBRST4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff TensorProduct
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
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

/-- Three independent coefficient directions for odd ghosts. -/
abbrev OddGeneratorSpace := Fin 3 → Real

/-- The genuine exterior coefficient algebra. -/
abbrev GhostCoefficientExterior :=
  ExteriorAlgebra Real OddGeneratorSpace

/-- Its genuine `ZMod 2` superalgebra grading. -/
abbrev GhostCoefficientParity (degree : ZMod 2) :
    Submodule Real GhostCoefficientExterior :=
  CliffordAlgebra.evenOdd
    (0 : QuadraticForm Real OddGeneratorSpace) degree

/-- Coordinate vector underlying the `i`th exterior generator. -/
def oddBasisVector (i : Fin 3) : OddGeneratorSpace :=
  fun j => if j = i then 1 else 0

@[simp]
theorem oddBasisVector_self (i : Fin 3) :
    oddBasisVector i i = 1 := by
  simp [oddBasisVector]

theorem oddBasisVector_ne_zero (i : Fin 3) :
    oddBasisVector i ≠ 0 := by
  intro hZero
  have hAt := congrFun hZero i
  simp [oddBasisVector] at hAt

/-- The `i`th degree-one exterior generator. -/
def oddGenerator (i : Fin 3) : GhostCoefficientExterior :=
  ExteriorAlgebra.ι Real (oddBasisVector i)

theorem oddGenerator_ne_zero (i : Fin 3) :
    oddGenerator i ≠ 0 := by
  intro hZero
  have hVectorZero :=
    (ExteriorAlgebra.ι_eq_zero_iff (R := Real) (oddBasisVector i)).mp hZero
  exact oddBasisVector_ne_zero i hVectorZero

/-- Each generator belongs to the odd part of the actual `ZMod 2` grading. -/
theorem oddGenerator_mem_odd (i : Fin 3) :
    oddGenerator i ∈ GhostCoefficientParity 1 := by
  exact CliffordAlgebra.ι_mem_evenOdd_one
    (0 : QuadraticForm Real OddGeneratorSpace) (oddBasisVector i)

@[simp]
theorem oddGenerator_sq (i : Fin 3) :
    oddGenerator i * oddGenerator i = 0 := by
  exact ExteriorAlgebra.ι_sq_zero (R := Real) (oddBasisVector i)

/-- Degree-one exterior generators anticommute. -/
theorem oddGenerator_anticommute (i j : Fin 3) :
    oddGenerator i * oddGenerator j =
      -(oddGenerator j * oddGenerator i) := by
  exact eq_neg_of_add_eq_zero_left
    (ExteriorAlgebra.ι_add_mul_swap
      (R := Real) (oddBasisVector i) (oddBasisVector j))

/-- A product of two odd generators lies in the even part. -/
theorem oddGenerator_mul_mem_even (i j : Fin 3) :
    oddGenerator i * oddGenerator j ∈ GhostCoefficientParity 0 := by
  exact CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero
    (0 : QuadraticForm Real OddGeneratorSpace)
    (oddBasisVector i) (oddBasisVector j)

theorem oddGenerator_triple_swap (i j k : Fin 3) :
    oddGenerator j * (oddGenerator i * oddGenerator k) =
      -(oddGenerator i * (oddGenerator j * oddGenerator k)) := by
  rw [← mul_assoc, oddGenerator_anticommute, neg_mul, mul_assoc]

/-- Exterior coefficients tensored with the actual global smooth D8 ghosts. -/
abbrev ExteriorDiffeomorphismGhostModule :=
  GhostCoefficientExterior ⊗[Real]
    CInfinityDiffeomorphismGhost period hPeriod

/-- Koszul extension of the intrinsic D8 ghost Lie bracket.  The tangent Lie
algebra is degree zero; all parity is carried by the exterior coefficient. -/
def exteriorGhostBracket :
    ExteriorDiffeomorphismGhostModule period hPeriod →ₗ[Real]
      ExteriorDiffeomorphismGhostModule period hPeriod →ₗ[Real]
        ExteriorDiffeomorphismGhostModule period hPeriod :=
  TensorProduct.map₂
    (LinearMap.mul Real GhostCoefficientExterior)
    (smoothGhostLieBracketBilinear period hPeriod)

@[simp]
theorem exteriorGhostBracket_tmul
    (firstCoefficient secondCoefficient : GhostCoefficientExterior)
    (firstGhost secondGhost :
      CInfinityDiffeomorphismGhost period hPeriod) :
    exteriorGhostBracket period hPeriod
        (firstCoefficient ⊗ₜ[Real] firstGhost)
        (secondCoefficient ⊗ₜ[Real] secondGhost) =
      (firstCoefficient * secondCoefficient) ⊗ₜ[Real]
        smoothGhostLieBracket period hPeriod firstGhost secondGhost := by
  rfl

/-- A homogeneous odd pure ghost. -/
def oddPureGhost
    (index : Fin 3)
    (ghost : CInfinityDiffeomorphismGhost period hPeriod) :
    ExteriorDiffeomorphismGhostModule period hPeriod :=
  oddGenerator index ⊗ₜ[Real] ghost

@[simp]
theorem exteriorGhostBracket_oddPure_self
    (index : Fin 3)
    (ghost : CInfinityDiffeomorphismGhost period hPeriod) :
    exteriorGhostBracket period hPeriod
        (oddPureGhost period hPeriod index ghost)
        (oddPureGhost period hPeriod index ghost) = 0 := by
  simp [oddPureGhost]

/-- The bracket of two odd pure ghosts is symmetric, as required by the
Koszul sign rule. -/
theorem exteriorGhostBracket_oddPure_swap
    (i j : Fin 3)
    (first second : CInfinityDiffeomorphismGhost period hPeriod) :
    exteriorGhostBracket period hPeriod
        (oddPureGhost period hPeriod i first)
        (oddPureGhost period hPeriod j second) =
      exteriorGhostBracket period hPeriod
        (oddPureGhost period hPeriod j second)
        (oddPureGhost period hPeriod i first) := by
  simp only [oddPureGhost, exteriorGhostBracket_tmul]
  rw [oddGenerator_anticommute,
    smoothGhostLieBracket_swap period hPeriod first second]
  rw [TensorProduct.neg_tmul, TensorProduct.tmul_neg, neg_neg]

/-- Signed Jacobi identity for three homogeneous odd ghosts. -/
theorem exteriorGhostBracket_oddPure_jacobi
    (i j k : Fin 3)
    (first second third :
      CInfinityDiffeomorphismGhost period hPeriod) :
    exteriorGhostBracket period hPeriod
        (oddPureGhost period hPeriod i first)
        (exteriorGhostBracket period hPeriod
          (oddPureGhost period hPeriod j second)
          (oddPureGhost period hPeriod k third)) =
      exteriorGhostBracket period hPeriod
          (exteriorGhostBracket period hPeriod
            (oddPureGhost period hPeriod i first)
            (oddPureGhost period hPeriod j second))
          (oddPureGhost period hPeriod k third) -
        exteriorGhostBracket period hPeriod
          (oddPureGhost period hPeriod j second)
          (exteriorGhostBracket period hPeriod
            (oddPureGhost period hPeriod i first)
            (oddPureGhost period hPeriod k third)) := by
  simp only [oddPureGhost, exteriorGhostBracket_tmul]
  rw [smoothGhostLieBracket_jacobi period hPeriod first second third,
    TensorProduct.tmul_add,
    mul_assoc (oddGenerator i) (oddGenerator j) (oddGenerator k),
    oddGenerator_triple_swap i j k]
  rw [TensorProduct.neg_tmul]
  abel

/-- A finite odd ghost with two independent components. -/
def twoGeneratorOddGhost
    (first second : CInfinityDiffeomorphismGhost period hPeriod) :
    ExteriorDiffeomorphismGhostModule period hPeriod :=
  oddPureGhost period hPeriod 0 first +
    oddPureGhost period hPeriod 1 second

theorem twoGeneratorOddGhost_self_bracket
    (first second : CInfinityDiffeomorphismGhost period hPeriod) :
    exteriorGhostBracket period hPeriod
        (twoGeneratorOddGhost period hPeriod first second)
        (twoGeneratorOddGhost period hPeriod first second) =
      (2 : Real) •
        ((oddGenerator 0 * oddGenerator 1) ⊗ₜ[Real]
          smoothGhostLieBracket period hPeriod first second) := by
  simp only [twoGeneratorOddGhost, map_add, LinearMap.add_apply]
  rw [exteriorGhostBracket_oddPure_self,
    exteriorGhostBracket_oddPure_self,
    exteriorGhostBracket_oddPure_swap period hPeriod 1 0 second first]
  simp only [oddPureGhost, exteriorGhostBracket_tmul]
  module

/-- Conventional nonlinear `s c = -1/2 [c,c]` ghost term for two independent
odd components. -/
def nonlinearExteriorGhostBRSTTerm
    (first second : CInfinityDiffeomorphismGhost period hPeriod) :
    ExteriorDiffeomorphismGhostModule period hPeriod :=
  (-((2 : Real)⁻¹)) •
    exteriorGhostBracket period hPeriod
      (twoGeneratorOddGhost period hPeriod first second)
      (twoGeneratorOddGhost period hPeriod first second)

theorem nonlinearExteriorGhostBRSTTerm_eq
    (first second : CInfinityDiffeomorphismGhost period hPeriod) :
    nonlinearExteriorGhostBRSTTerm period hPeriod first second =
      -((oddGenerator 0 * oddGenerator 1) ⊗ₜ[Real]
        smoothGhostLieBracket period hPeriod first second) := by
  rw [nonlinearExteriorGhostBRSTTerm,
    twoGeneratorOddGhost_self_bracket, smul_smul]
  norm_num

/-- Cubic obstruction obtained by applying the quadratic ghost rule twice.
Its vanishing is the precise Jacobi/nilpotence statement closed here. -/
def cubicGhostBRSTJacobiObstruction
    (i j k : Fin 3)
    (first second third :
      CInfinityDiffeomorphismGhost period hPeriod) :
    ExteriorDiffeomorphismGhostModule period hPeriod :=
  exteriorGhostBracket period hPeriod
      (oddPureGhost period hPeriod i first)
      (exteriorGhostBracket period hPeriod
        (oddPureGhost period hPeriod j second)
        (oddPureGhost period hPeriod k third)) -
    exteriorGhostBracket period hPeriod
      (exteriorGhostBracket period hPeriod
        (oddPureGhost period hPeriod i first)
        (oddPureGhost period hPeriod j second))
      (oddPureGhost period hPeriod k third) +
    exteriorGhostBracket period hPeriod
      (oddPureGhost period hPeriod j second)
      (exteriorGhostBracket period hPeriod
        (oddPureGhost period hPeriod i first)
        (oddPureGhost period hPeriod k third))

@[simp]
theorem cubicGhostBRSTJacobiObstruction_zero
    (i j k : Fin 3)
    (first second third :
      CInfinityDiffeomorphismGhost period hPeriod) :
    cubicGhostBRSTJacobiObstruction period hPeriod i j k
      first second third = 0 := by
  rw [cubicGhostBRSTJacobiObstruction,
    exteriorGhostBracket_oddPure_jacobi]
  abel

theorem exterior_diffeomorphism_ghost_brst4D_closure :
    (∀ i : Fin 3, oddGenerator i ∈ GhostCoefficientParity 1) ∧
      (∀ i j : Fin 3,
        oddGenerator i * oddGenerator j ∈ GhostCoefficientParity 0) ∧
      (∀ first second : CInfinityDiffeomorphismGhost period hPeriod,
        nonlinearExteriorGhostBRSTTerm period hPeriod first second =
          -((oddGenerator 0 * oddGenerator 1) ⊗ₜ[Real]
            smoothGhostLieBracket period hPeriod first second)) ∧
      ∀ (i j k : Fin 3)
        (first second third :
          CInfinityDiffeomorphismGhost period hPeriod),
        cubicGhostBRSTJacobiObstruction period hPeriod i j k
          first second third = 0 :=
  ⟨oddGenerator_mem_odd,
    oddGenerator_mul_mem_even,
    nonlinearExteriorGhostBRSTTerm_eq period hPeriod,
    cubicGhostBRSTJacobiObstruction_zero period hPeriod⟩

end

end P0EFTJanusMappingTorusExteriorDiffeomorphismGhostBRST4D
end JanusFormal
