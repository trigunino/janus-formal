import Mathlib

namespace JanusFormal
namespace P0EFTJanusRP4TwistedFluxPrimitiveSelector

set_option autoImplicit false

/--
A signed orientation-twisted four-form flux sector.

The topological input is represented by an integer class.  The physical
selection input is deliberately split into:

* oddness, which is the algebraic form of selecting the non-trivial mod-two
  class; and
* minimality among odd sectors.

The theorem below proves that these two inputs force the primitive magnitude
`1`.  It does not assume a numerical value for the dimensionful charge unit.
-/
structure TwistedFluxSector where
  flux : ℤ
  oddMagnitude : flux.natAbs % 2 = 1
  minimalOddMagnitude :
    ∀ m : ℕ, m % 2 = 1 → flux.natAbs ≤ m

/-- PT reverses the signed twisted flux. -/
def ptConjugate (n : ℤ) : ℤ := -n

@[simp] theorem pt_conjugate_is_involutive (n : ℤ) :
    ptConjugate (ptConjugate n) = n := by
  simp [ptConjugate]

@[simp] theorem pt_conjugate_preserves_magnitude (n : ℤ) :
    (ptConjugate n).natAbs = n.natAbs := by
  simp [ptConjugate]

@[simp] theorem pt_conjugate_preserves_quadratic_energy (n : ℤ) :
    ptConjugate n * ptConjugate n = n * n := by
  simp [ptConjugate]

/--
A non-trivial mod-two flux sector that minimizes the magnitude among all odd
sectors is necessarily primitive.
-/
theorem minimal_odd_flux_is_primitive (s : TwistedFluxSector) :
    s.flux.natAbs = 1 := by
  have hOdd : s.flux.natAbs % 2 = 1 := s.oddMagnitude
  have hLe : s.flux.natAbs ≤ 1 :=
    s.minimalOddMagnitude 1 (by decide)
  omega

/-- The primitive selected sector is nonzero. -/
theorem primitive_flux_is_nonzero (s : TwistedFluxSector) :
    s.flux ≠ 0 := by
  intro hZero
  have hPrimitive := minimal_odd_flux_is_primitive s
  simp [hZero] at hPrimitive

end P0EFTJanusRP4TwistedFluxPrimitiveSelector
end JanusFormal
