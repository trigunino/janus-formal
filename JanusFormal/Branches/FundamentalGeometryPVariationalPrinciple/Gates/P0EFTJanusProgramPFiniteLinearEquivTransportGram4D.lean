import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.Basis.Basic

/-!
# Gram nondegeneracy under linear-equivalence transport

Transporting a finite basis through a linear equivalence preserves linear
independence.  In a real inner-product target, the transported Gram determinant
is therefore nonzero.  This is the finite-dimensional step needed by kernel
transports; no determinant margin or unitary hypothesis is required.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteLinearEquivTransportGram4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators InnerProductSpace

variable {Index Kernel Ambient : Type*}
  [AddCommGroup Kernel] [Module Real Kernel]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]

/-- A linear equivalence transports a finite basis to a linearly independent
family. -/
theorem linearIndependent_basis_linearEquiv
    (basis : Module.Basis Index Real Kernel)
    (transport : Kernel ≃ₗ[Real] Ambient) :
    LinearIndependent Real (fun index => transport (basis index)) := by
  have hTransported := basis.linearIndependent.map' transport.toLinearMap
    (LinearMap.ker_eq_bot.mpr transport.injective)
  simpa [Function.comp_def] using hTransported

/-- Consequently the transported Gram determinant never vanishes. -/
theorem gram_det_ne_zero_of_basis_linearEquiv
    [Fintype Index] [DecidableEq Index]
    (basis : Module.Basis Index Real Kernel)
    (transport : Kernel ≃ₗ[Real] Ambient) :
    (Matrix.gram Real (fun index => transport (basis index))).det ≠ 0 :=
  Matrix.det_gram_ne_zero_iff_linearIndependent.mpr
    (linearIndependent_basis_linearEquiv basis transport)

/-- Public finite transport-to-Gram checkpoint. -/
theorem finite_linear_equiv_transport_gram_gate
    [Fintype Index] [DecidableEq Index]
    (basis : Module.Basis Index Real Kernel)
    (transport : Kernel ≃ₗ[Real] Ambient) :
    LinearIndependent Real (fun index => transport (basis index)) ∧
    (Matrix.gram Real (fun index => transport (basis index))).det ≠ 0 :=
  ⟨linearIndependent_basis_linearEquiv basis transport,
    gram_det_ne_zero_of_basis_linearEquiv basis transport⟩

end
end P0EFTJanusProgramPFiniteLinearEquivTransportGram4D
end JanusFormal
