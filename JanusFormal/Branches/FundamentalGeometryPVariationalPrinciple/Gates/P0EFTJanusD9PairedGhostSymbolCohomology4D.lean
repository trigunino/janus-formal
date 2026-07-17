import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusD9PairedGhostNonzeroSymbolKernel4D

/-!
# Paired D9 ghost symbol cohomology away from the zero covector

The quotient by the range of the paired five-coordinate ghost symbol is
constructed explicitly.  At every nonzero covector the symbol is an
isomorphism, hence this quotient is trivial, whereas the zero-covector
quotient remains the five-coordinate cohomology already computed.  This is a
pointwise symbol calculation only; no global BRST operator is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusD9PairedGhostSymbolCohomology4D

set_option autoImplicit false

noncomputable section

open P0EFTJanusCompleteGaugeFixedEllipticSymbol
open P0EFTJanusImmersionFiberAlgebra
open P0EFTJanusGaugeFixedPrincipalSymbols
open P0EFTJanusD9PairedU1GhostZeroModeCohomology4D
open P0EFTJanusD9PairedGhostNonzeroSymbolKernel4D

/-- Pointwise cokernel of the paired ghost principal symbol. -/
abbrev D9PairedGhostSymbolCohomology (covector : TangentVector3) :=
  D9PairedGhostCoordinateSpace ⧸
    LinearMap.range (d9PairedGhostPrincipalSymbol covector)

def d9PairedGhostSymbolCohomologyProjection (covector : TangentVector3) :
    D9PairedGhostCoordinateSpace →ₗ[Real]
      D9PairedGhostSymbolCohomology covector :=
  (LinearMap.range (d9PairedGhostPrincipalSymbol covector)).mkQ

theorem d9PairedGhostSymbolCohomologyProjection_eq_zero
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent)
    (coordinate : D9PairedGhostCoordinateSpace) :
    d9PairedGhostSymbolCohomologyProjection covector coordinate = 0 := by
  change (Submodule.Quotient.mk coordinate :
    D9PairedGhostSymbolCohomology covector) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  rw [d9PairedGhostPrincipalSymbol_range covector hCovector]
  trivial

theorem d9PairedGhostSymbolCohomology_eq_zero
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent)
    (cohomologyClass : D9PairedGhostSymbolCohomology covector) :
    cohomologyClass = 0 := by
  obtain ⟨coordinate, rfl⟩ :=
    Submodule.mkQ_surjective
      (LinearMap.range (d9PairedGhostPrincipalSymbol covector)) cohomologyClass
  exact d9PairedGhostSymbolCohomologyProjection_eq_zero covector hCovector coordinate

theorem d9PairedGhostSymbolCohomology_subsingleton
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent) :
    Subsingleton (D9PairedGhostSymbolCohomology covector) :=
  ⟨fun first second =>
    (d9PairedGhostSymbolCohomology_eq_zero covector hCovector first).trans
      (d9PairedGhostSymbolCohomology_eq_zero covector hCovector second).symm⟩

/-- Complete nonzero-covector symbol certificate: no kernel and no cokernel. -/
theorem d9_paired_ghost_nonzero_symbol_cohomology4D
    (covector : TangentVector3) (hCovector : covector ≠ zeroTangent) :
    LinearMap.ker (d9PairedGhostPrincipalSymbol covector) = ⊥ ∧
      LinearMap.range (d9PairedGhostPrincipalSymbol covector) = ⊤ ∧
      ∀ cohomologyClass : D9PairedGhostSymbolCohomology covector,
        cohomologyClass = 0 :=
  ⟨d9PairedGhostPrincipalSymbol_ker covector hCovector,
    d9PairedGhostPrincipalSymbol_range covector hCovector,
    d9PairedGhostSymbolCohomology_eq_zero covector hCovector⟩

end
end P0EFTJanusD9PairedGhostSymbolCohomology4D
end JanusFormal
