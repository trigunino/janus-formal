import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D

/-!
# Relative variational obstruction exactness

This gate constructs the horizontal cohomology group of the relative jet
bicomplex and proves the standard first-variation implication: whenever an
Euler cochain is obtained from a Lagrangian up to a horizontal boundary term,
its vertical Helmholtz obstruction is a horizontal boundary and hence has
zero cohomology class.  A later gate must realize these cochains for the exact
T03 action; no physical vanishing statement is made here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeVariationalObstructionExactness4D

set_option autoImplicit false

open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D
open P0EFTJanusProgramPRelativeJetVariationalBicomplexCore4D.RelativeJetVariationalBicomplexCore

universe u v

variable
    {R : Type u} [CommRing R]
    {C : RelativeJetStratum4D → Nat → Nat → Type v}
    [∀ stratum p q, AddCommGroup (C stratum p q)]
    [∀ stratum p q, Module R (C stratum p q)]

/-- Horizontal cocycles in one bidegree. -/
abbrev HorizontalCycles
    (bicomplex : RelativeJetVariationalBicomplexCore R C)
    (p q : Nat) :=
  LinearMap.ker (bicomplex.dH p q)

/-- The horizontal differential, with codomain restricted to cocycles. -/
def horizontalBoundaryMap
    (bicomplex : RelativeJetVariationalBicomplexCore R C)
    (p q : Nat) :
    RelativeJetCochain C p q →ₗ[R] HorizontalCycles bicomplex (p + 1) q where
  toFun cochain := ⟨bicomplex.dH p q cochain, bicomplex.dH_dH p q cochain⟩
  map_add' first second := by
    apply Subtype.ext
    exact (bicomplex.dH p q).map_add first second
  map_smul' scalar cochain := by
    apply Subtype.ext
    exact (bicomplex.dH p q).map_smul scalar cochain

/-- Horizontal cohomology at successor degree: cocycles modulo actual
horizontal boundaries. -/
abbrev HorizontalCohomologyAtSucc
    (bicomplex : RelativeJetVariationalBicomplexCore R C)
    (p q : Nat) :=
  HorizontalCycles bicomplex (p + 1) q ⧸
    LinearMap.range (horizontalBoundaryMap bicomplex p q)

/-- A relative first-variation formula in adjacent horizontal degrees. -/
structure RelativeFirstVariationData
    (bicomplex : RelativeJetVariationalBicomplexCore R C)
    (p : Nat) where
  lagrangian : RelativeJetCochain C (p + 1) 0
  euler : RelativeJetCochain C (p + 1) 1
  boundaryPotential : RelativeJetCochain C p 1
  firstVariation :
    bicomplex.dV (p + 1) 0 lagrangian =
      euler + bicomplex.dH p 1 boundaryPotential

namespace RelativeFirstVariationData

/-- The vertical Euler obstruction is the horizontal differential of the
vertical boundary potential. -/
theorem euler_obstruction_eq_horizontal_boundary
    {bicomplex : RelativeJetVariationalBicomplexCore R C}
    {p : Nat} (data : RelativeFirstVariationData bicomplex p) :
    bicomplex.dV (p + 1) 1 data.euler =
      bicomplex.dH p 2 (bicomplex.dV p 1 data.boundaryPotential) := by
  calc
    bicomplex.dV (p + 1) 1 data.euler =
        bicomplex.dV (p + 1) 1 data.euler +
          (bicomplex.dV (p + 1) 1
              (bicomplex.dH p 1 data.boundaryPotential) +
            bicomplex.dH p 2
              (bicomplex.dV p 1 data.boundaryPotential)) := by
        rw [bicomplex.mixed_anticommutes p 1 data.boundaryPotential]
        simp
    _ =
        (bicomplex.dV (p + 1) 1 data.euler +
          bicomplex.dV (p + 1) 1
            (bicomplex.dH p 1 data.boundaryPotential)) +
          bicomplex.dH p 2
            (bicomplex.dV p 1 data.boundaryPotential) := by
        abel
    _ =
        bicomplex.dV (p + 1) 1
            (data.euler + bicomplex.dH p 1 data.boundaryPotential) +
          bicomplex.dH p 2
            (bicomplex.dV p 1 data.boundaryPotential) := by
        rw [(bicomplex.dV (p + 1) 1).map_add]
    _ =
        bicomplex.dV (p + 1) 1
            (bicomplex.dV (p + 1) 0 data.lagrangian) +
          bicomplex.dH p 2
            (bicomplex.dV p 1 data.boundaryPotential) := by
        rw [data.firstVariation]
    _ = bicomplex.dH p 2
          (bicomplex.dV p 1 data.boundaryPotential) := by
        rw [bicomplex.dV_dV]
        simp

/-- The Euler obstruction, equipped with its horizontal closedness proof. -/
def eulerObstructionCycle
    {bicomplex : RelativeJetVariationalBicomplexCore R C}
    {p : Nat} (data : RelativeFirstVariationData bicomplex p) :
    HorizontalCycles bicomplex (p + 1) 2 :=
  ⟨bicomplex.dV (p + 1) 1 data.euler, by
    rw [data.euler_obstruction_eq_horizontal_boundary]
    exact bicomplex.dH_dH p 2
      (bicomplex.dV p 1 data.boundaryPotential)⟩

/-- Horizontal cohomology class of the nonlinear Euler obstruction. -/
def eulerObstructionClass
    {bicomplex : RelativeJetVariationalBicomplexCore R C}
    {p : Nat} (data : RelativeFirstVariationData bicomplex p) :
    HorizontalCohomologyAtSucc bicomplex p 2 :=
  (LinearMap.range (horizontalBoundaryMap bicomplex p 2)).mkQ
    data.eulerObstructionCycle

/-- The variational obstruction class vanishes for every genuine relative
first-variation formula. -/
theorem eulerObstructionClass_eq_zero
    {bicomplex : RelativeJetVariationalBicomplexCore R C}
    {p : Nat} (data : RelativeFirstVariationData bicomplex p) :
    data.eulerObstructionClass = 0 := by
  change
    (Submodule.Quotient.mk data.eulerObstructionCycle :
      HorizontalCohomologyAtSucc bicomplex p 2) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  refine ⟨bicomplex.dV p 1 data.boundaryPotential, ?_⟩
  apply Subtype.ext
  exact data.euler_obstruction_eq_horizontal_boundary.symm

end RelativeFirstVariationData
end P0EFTJanusProgramPRelativeVariationalObstructionExactness4D
end JanusFormal
