import Mathlib.LinearAlgebra.Dimension.Finite
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

/-!
# Explicit finite models of an operator kernel

A proof that `ker H` is finite-dimensional is analytically sufficient but does
not identify the physical zero modes.  This file replaces that opaque fact by
an explicit finite coordinate model:

`(ZeroMode → Real) ≃ₗ[Real] ker H`.

The kernel dimension is then exactly `Fintype.card ZeroMode`, and the same model
supplies the finite-kernel field of the actual-kernel gap packet.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteKernelModel4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- A finite set of named zero modes whose coordinate space is linearly
identical to the actual operator kernel. -/
structure FiniteKernelModel (operator : E →L[Real] E) where
  ZeroMode : Type
  zeroModeFintype : Fintype ZeroMode
  zeroModeDecidableEq : DecidableEq ZeroMode
  coordinates : (ZeroMode → Real) ≃ₗ[Real] operator.ker

namespace FiniteKernelModel

variable {operator : E →L[Real] E}

local instance zeroModeFintype (model : FiniteKernelModel operator) :
    Fintype model.ZeroMode := model.zeroModeFintype

local instance zeroModeDecidableEq (model : FiniteKernelModel operator) :
    DecidableEq model.ZeroMode := model.zeroModeDecidableEq

/-- The explicit model installs finite-dimensionality of the actual kernel. -/
@[reducible] def kernelFiniteDimensional
    (model : FiniteKernelModel operator) :
    FiniteDimensional Real operator.ker := by
  letI : FiniteDimensional Real (model.ZeroMode → Real) :=
    Module.Finite.pi
  exact model.coordinates.finiteDimensional

/-- The actual kernel dimension is the number of classified zero modes. -/
theorem kernel_finrank_eq_card
    (model : FiniteKernelModel operator) :
    Module.finrank Real operator.ker = Fintype.card model.ZeroMode := by
  letI : FiniteDimensional Real operator.ker :=
    model.kernelFiniteDimensional
  calc
    Module.finrank Real operator.ker =
        Module.finrank Real (model.ZeroMode → Real) :=
      model.coordinates.symm.finrank_eq
    _ = Fintype.card model.ZeroMode := by
      simp

/-- Coordinate synthesis of one named zero-mode coefficient vector. -/
def synthesize
    (model : FiniteKernelModel operator)
    (coefficient : model.ZeroMode → Real) : E :=
  (model.coordinates coefficient).1

/-- Every synthesized vector is genuinely annihilated by the operator. -/
theorem synthesize_mem_kernel
    (model : FiniteKernelModel operator)
    (coefficient : model.ZeroMode → Real) :
    operator (model.synthesize coefficient) = 0 :=
  LinearMap.mem_ker.mp (model.coordinates coefficient).2

/-- Every actual zero mode has unique finite coordinates. -/
def analyze
    (model : FiniteKernelModel operator)
    (zeroMode : operator.ker) : model.ZeroMode → Real :=
  model.coordinates.symm zeroMode

@[simp]
theorem synthesize_analyze
    (model : FiniteKernelModel operator)
    (zeroMode : operator.ker) :
    model.synthesize (model.analyze zeroMode) = zeroMode.1 := by
  unfold synthesize analyze
  rw [model.coordinates.apply_symm_apply]

@[simp]
theorem analyze_synthesize
    (model : FiniteKernelModel operator)
    (coefficient : model.ZeroMode → Real) :
    model.analyze (model.coordinates coefficient) = coefficient :=
  model.coordinates.symm_apply_apply coefficient

end FiniteKernelModel

section Gap

variable [InnerProductSpace Real E] [CompleteSpace E]

/-- Actual-kernel analytic data with an explicit finite zero-mode model. -/
structure SelfAdjointKernelComplementGapWithModel
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator) : Prop where
  model : FiniteKernelModel operator
  gap : Real
  gap_pos : 0 < gap
  lowerBound : ∀ vector : SelfAdjointKernelComplement operator,
    gap * ‖vector‖ ≤
      ‖selfAdjointKernelComplementOperator operator hSelfAdjoint vector‖

/-- Forget the zero-mode names and obtain the analytic gap packet. -/
def SelfAdjointKernelComplementGapWithModel.toGapData
    {operator : E →L[Real] E}
    {hSelfAdjoint : IsSelfAdjoint operator}
    (data : SelfAdjointKernelComplementGapWithModel operator hSelfAdjoint) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint where
  kernel_finite := data.model.kernelFiniteDimensional
  gap := data.gap
  gap_pos := data.gap_pos
  lowerBound := data.lowerBound

/-- Public finite-zero-mode checkpoint. -/
theorem finite_kernel_model_actual_gap_gate
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (data : SelfAdjointKernelComplementGapWithModel operator hSelfAdjoint) :
    SelfAdjointKernelComplementGapData operator hSelfAdjoint ∧
      Module.finrank Real operator.ker = Fintype.card data.model.ZeroMode := by
  letI : Fintype data.model.ZeroMode := data.model.zeroModeFintype
  letI : DecidableEq data.model.ZeroMode := data.model.zeroModeDecidableEq
  letI : FiniteDimensional Real operator.ker :=
    data.model.kernelFiniteDimensional
  exact ⟨data.toGapData, data.model.kernel_finrank_eq_card⟩

end Gap

end
end P0EFTJanusProgramPFiniteKernelModel4D
end JanusFormal
