import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.InnerProductSpace.Dual
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D

/-!
# Noether directions lie in the Hessian kernel

A continuous symmetry direction should not be supplied again as an operator
zero mode.  If the directional first variation of a `C²` scalar action vanishes
on a germ around the base point, differentiating this identity shows that the
second Fréchet derivative vanishes whenever one slot is that direction.

For a symmetric real Hessian, its Riesz representative therefore annihilates
the symmetry direction.  This is the generic calculus bridge needed to derive
Candidate-A zero modes from action-level Noether identities rather than from a
separate equation `H v = 0`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPNoetherHessianKernel4D

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 900000

noncomputable section

open Filter Topology
open scoped InnerProductSpace
open P0EFTJanusConvexHelmholtzReconstruction

variable {E : Type*} [NormedAddCommGroup E]

section

variable [NormedSpace Real E]

/-- Second Fréchet derivative of a scalar action at one base point. -/
def noetherHessianForm
    (action : E → Real) (base : E) :
    E →L[Real] E →L[Real] Real :=
  fderiv Real (actionGradient action) base

/-- A Noether direction on a genuine germ: its directional first variation is
identically zero near the chosen base point. -/
structure NoetherModeGermAt
    (action : E → Real) (base mode : E) : Prop where
  firstVariation_zero :
    (fun point => actionGradient action point mode) =ᶠ[𝓝 base]
      (fun _ : E => (0 : Real))

/-- Differentiating the Noether identity kills the symmetry direction in the
second Hessian slot. -/
theorem noetherMode_hessian_right_zero
    (action : E → Real) (base mode : E)
    (hC2 : ContDiffAt Real 2 action base)
    (hNoether : NoetherModeGermAt action base mode)
    (direction : E) :
    noetherHessianForm action base direction mode = 0 := by
  have hGradient : DifferentiableAt Real (actionGradient action) base :=
    (hC2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hMode : DifferentiableAt Real (fun _ : E => mode) base :=
    differentiableAt_const mode
  have hModeFDeriv :
      fderiv Real (fun _ : E => mode) base = 0 :=
    (hasFDerivAt_const mode base).fderiv
  have hApply :
      fderiv Real (fun point => actionGradient action point mode) base =
        (fderiv Real (actionGradient action) base).flip mode := by
    simpa only [hModeFDeriv, ContinuousLinearMap.comp_zero, zero_add] using
      (fderiv_clm_apply hGradient hMode)
  have hZero :
      fderiv Real (fun point => actionGradient action point mode) base = 0 := by
    rw [hNoether.firstVariation_zero.fderiv_eq]
    simp
  rw [hApply] at hZero
  have hEval := congrArg
    (fun linear : E →L[Real] Real => linear direction) hZero
  simpa [noetherHessianForm] using hEval

/-- Symmetry moves the preceding vanishing identity to the first Hessian slot. -/
theorem noetherMode_hessian_left_zero
    (action : E → Real) (base mode : E)
    (hC2 : ContDiffAt Real 2 action base)
    (hSymmetric : ∀ first second,
      noetherHessianForm action base first second =
        noetherHessianForm action base second first)
    (hNoether : NoetherModeGermAt action base mode)
    (direction : E) :
    noetherHessianForm action base mode direction = 0 := by
  rw [hSymmetric mode direction]
  exact noetherMode_hessian_right_zero action base mode hC2 hNoether direction

end

section Riesz

variable [InnerProductSpace Real E] [CompleteSpace E]

/-- Riesz representative of the genuine second Fréchet derivative. -/
def noetherHessianRieszOperator
    (action : E → Real) (base : E) : E →L[Real] E :=
  @InnerProductSpace.continuousLinearMapOfBilin
    Real E inferInstance inferInstance inferInstance inferInstance
    (noetherHessianForm action base)

/-- A germ-level Noether direction is an actual zero mode of the Riesz
representative of the symmetric Hessian. -/
theorem noetherMode_riesz_zero
    (action : E → Real) (base mode : E)
    (hC2 : ContDiffAt Real 2 action base)
    (hSymmetric : ∀ first second,
      noetherHessianForm action base first second =
        noetherHessianForm action base second first)
    (hNoether : NoetherModeGermAt action base mode) :
    noetherHessianRieszOperator action base mode = 0 := by
  let operator := noetherHessianRieszOperator action base
  have hPairing :
      inner Real (operator mode) (operator mode) =
        noetherHessianForm action base mode (operator mode) :=
    @InnerProductSpace.continuousLinearMapOfBilin_apply
      Real E inferInstance inferInstance inferInstance inferInstance
      (noetherHessianForm action base) mode (operator mode)
  have hFormZero :
      noetherHessianForm action base mode (operator mode) = 0 :=
    noetherMode_hessian_left_zero action base mode hC2 hSymmetric hNoether
      (operator mode)
  have hInner : inner Real (operator mode) (operator mode) = 0 :=
    hPairing.trans hFormZero
  have hNorm : ‖operator mode‖ = 0 := by
    rw [← sq_eq_zero_iff, ← real_inner_self_eq_norm_sq]
    exact hInner
  exact norm_eq_zero.mp hNorm

/-- Public Noether-to-kernel checkpoint. -/
theorem noether_hessian_kernel_gate
    (action : E → Real) (base mode : E)
    (hC2 : ContDiffAt Real 2 action base)
    (hSymmetric : ∀ first second,
      noetherHessianForm action base first second =
        noetherHessianForm action base second first)
    (hNoether : NoetherModeGermAt action base mode) :
    (∀ direction, noetherHessianForm action base direction mode = 0) ∧
      (∀ direction, noetherHessianForm action base mode direction = 0) ∧
      noetherHessianRieszOperator action base mode = 0 :=
  ⟨noetherMode_hessian_right_zero action base mode hC2 hNoether,
    noetherMode_hessian_left_zero action base mode hC2 hSymmetric hNoether,
    noetherMode_riesz_zero action base mode hC2 hSymmetric hNoether⟩

end Riesz

end
end P0EFTJanusProgramPNoetherHessianKernel4D
end JanusFormal
