import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9DiffeomorphismGhostPrincipalSymbolBridge4D

/-!
# D9 ghost principal-symbol cohomology at the zero mode

The complete local D9 ghost has one `U(1)` and three diffeomorphism
coordinates.  At zero covector its principal-symbol differential is exactly
zero.  This gate computes the resulting two-term symbol cohomology: the kernel
is the full four-dimensional coordinate space, the image is zero, and the
quotient by the image is linearly equivalent to that coordinate space.

This is only the constant/zero-covector symbol subcomplex.  It does not compute
the cohomology of the global differential operator or impose its domain.
-/

namespace JanusFormal
namespace P0EFTJanusD9GhostZeroModeCohomology4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusCompleteGaugeFixedEllipticSymbol

/-- Linear coordinates of the complete local D9 ghost sector: one `U(1)`
coordinate followed by three diffeomorphism coordinates. -/
abbrev D9GhostCoordinateSpace := Real × (Real × Real × Real)

/-- Coordinate packaging of the complete D9 ghost field. -/
def d9GhostFieldEquiv : GaugeFixedGhostField ≃ D9GhostCoordinateSpace where
  toFun field := (field.u1Ghost,
    (field.diffeomorphismGhost.x, field.diffeomorphismGhost.y,
      field.diffeomorphismGhost.z))
  invFun coordinate :=
    { u1Ghost := coordinate.1
      diffeomorphismGhost :=
        { x := coordinate.2.1
          y := coordinate.2.2.1
          z := coordinate.2.2.2 } }
  left_inv field := by cases field; rfl
  right_inv coordinate := by rcases coordinate with ⟨u1, x, y, z⟩; rfl

@[simp] theorem d9GhostFieldEquiv_zero :
    d9GhostFieldEquiv zeroGhostField = (0 : D9GhostCoordinateSpace) := by
  rfl

/-- The two-term D9 ghost symbol differential restricted to the zero
covector. -/
def d9GhostZeroModeDifferential :
    D9GhostCoordinateSpace →ₗ[Real] D9GhostCoordinateSpace := 0

/-- The coordinate differential implements the actual complete D9 principal
symbol at zero covector. -/
theorem ghostPrincipalSymbol_zeroMode
    (coordinate : D9GhostCoordinateSpace) :
    ghostPrincipalSymbol zeroTangent (d9GhostFieldEquiv.symm coordinate) =
      zeroGhostField := by
  apply GaugeFixedGhostField.ext
  · simp [ghostPrincipalSymbol, d9GhostFieldEquiv, zeroTangent,
      normSquared, tangentDot, zeroGhostField]
  · simp [ghostPrincipalSymbol, d9GhostFieldEquiv, ghostLaplacianSymbol,
      zeroTangent, normSquared, tangentDot, zeroGhostField, scaleTangent]

/-- Every constant ghost coordinate is closed at zero covector. -/
theorem d9GhostZeroModeDifferential_ker :
    LinearMap.ker d9GhostZeroModeDifferential = ⊤ := by
  exact LinearMap.ker_zero

/-- There are no nonzero exact coordinates in this isolated two-term zero
symbol complex. -/
theorem d9GhostZeroModeDifferential_range :
    LinearMap.range d9GhostZeroModeDifferential = ⊥ := by
  exact LinearMap.range_zero

/-- Cohomology of the isolated zero-mode symbol complex: closed coordinates
modulo the (zero) incoming image. -/
abbrev D9GhostZeroModeCohomology :=
  D9GhostCoordinateSpace ⧸ (LinearMap.range d9GhostZeroModeDifferential)

/-- Canonical projection to zero-mode symbol cohomology. -/
def d9GhostZeroModeCohomologyProjection :
    D9GhostCoordinateSpace →ₗ[Real] D9GhostZeroModeCohomology :=
  (LinearMap.range d9GhostZeroModeDifferential).mkQ

theorem d9GhostZeroModeCohomologyProjection_injective :
    Function.Injective d9GhostZeroModeCohomologyProjection := by
  apply LinearMap.ker_eq_bot.mp
  rw [d9GhostZeroModeCohomologyProjection, Submodule.ker_mkQ,
    d9GhostZeroModeDifferential_range]

theorem d9GhostZeroModeCohomologyProjection_surjective :
    Function.Surjective d9GhostZeroModeCohomologyProjection := by
  exact Submodule.mkQ_surjective _

/-- Explicit identification of the computed quotient cohomology with all four
constant ghost coordinates. -/
def d9GhostZeroModeCohomologyEquiv :
    D9GhostCoordinateSpace ≃ₗ[Real] D9GhostZeroModeCohomology :=
  LinearEquiv.ofBijective d9GhostZeroModeCohomologyProjection
    ⟨d9GhostZeroModeCohomologyProjection_injective,
      d9GhostZeroModeCohomologyProjection_surjective⟩

/-- Complete local certificate for this zero-covector subcomplex. -/
theorem d9_ghost_zero_mode_cohomology4D :
    LinearMap.ker d9GhostZeroModeDifferential = ⊤ ∧
      LinearMap.range d9GhostZeroModeDifferential = ⊥ ∧
      Function.Bijective d9GhostZeroModeCohomologyProjection :=
  ⟨d9GhostZeroModeDifferential_ker,
    d9GhostZeroModeDifferential_range,
    d9GhostZeroModeCohomologyProjection_injective,
    d9GhostZeroModeCohomologyProjection_surjective⟩

end
end P0EFTJanusD9GhostZeroModeCohomology4D
end JanusFormal
