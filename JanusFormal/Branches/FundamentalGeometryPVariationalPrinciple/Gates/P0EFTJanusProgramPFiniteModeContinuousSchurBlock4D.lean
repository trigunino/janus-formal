import Mathlib.Analysis.Normed.Operator.Prod
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeSchurBlockElimination4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeSchurClosedRange4D

/-!
# Continuous four-block Schur elimination

When the decomposition, the four blocks and the inverse of the complementary
block are bounded, the reduced left coordinate map is bounded automatically.
This file constructs that map from product projections and composition of
continuous linear maps.

Consequently the full finite-mode Schur package -- kernel equivalence, finite
kernel, closed range and canonical zero-mode model -- follows from one bounded
four-block decomposition.  No separate range-coordinate map is supplied.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteModeContinuousSchurBlock4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteModeSchurKernel4D
open P0EFTJanusProgramPFiniteModeSchurBlockElimination4D
open P0EFTJanusProgramPFiniteModeSchurClosedRange4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Bounded four-block representation of an operator. -/
structure FiniteModeContinuousSchurBlockData
    (operator : E →L[Real] E)
    (Mode Complement : Type*)
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement] where
  decomposition : E ≃L[Real] ((Mode → Real) × Complement)
  finiteBlock : (Mode → Real) →L[Real] (Mode → Real)
  upperRight : Complement →L[Real] (Mode → Real)
  lowerLeft : (Mode → Real) →L[Real] Complement
  complementEquiv : Complement ≃L[Real] Complement
  operator_block : ∀ state : (Mode → Real) × Complement,
    decomposition (operator (decomposition.symm state)) =
      (finiteBlock state.1 + upperRight state.2,
        lowerLeft state.1 + complementEquiv state.2)

/-- Forget continuity and retain the four algebraic blocks. -/
def FiniteModeContinuousSchurBlockData.toLinearBlockData
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeContinuousSchurBlockData operator Mode Complement) :
    FiniteModeSchurBlockData operator Mode Complement where
  decomposition := data.decomposition.toLinearEquiv
  finiteBlock := data.finiteBlock.toLinearMap
  upperRight := data.upperRight.toLinearMap
  lowerLeft := data.lowerLeft.toLinearMap
  complementEquiv := data.complementEquiv.toLinearEquiv
  operator_block := data.operator_block

/-- Bounded left triangular reduction on the product coordinates. -/
def finiteModeContinuousSchurLeftReduction
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeContinuousSchurBlockData operator Mode Complement) :
    ((Mode → Real) × Complement) →L[Real]
      ((Mode → Real) × Complement) :=
  let first := ContinuousLinearMap.fst Real (Mode → Real) Complement
  let second := ContinuousLinearMap.snd Real (Mode → Real) Complement
  let correction := data.upperRight.comp
    (data.complementEquiv.symm.toContinuousLinearMap.comp second)
  (first - correction).prod second

/-- Continuous reduced coordinate map `L ∘ decomposition`. -/
def finiteModeContinuousSchurRangeCoordinates
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeContinuousSchurBlockData operator Mode Complement) :
    E →L[Real] ((Mode → Real) × Complement) :=
  (finiteModeContinuousSchurLeftReduction data).comp
    data.decomposition.toContinuousLinearMap

/-- The bounded left reduction agrees with the algebraic Gaussian-elimination
map used by the kernel factorization. -/
theorem finiteModeContinuousSchurRangeCoordinates_eq
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeContinuousSchurBlockData operator Mode Complement)
    (state : E) :
    finiteModeContinuousSchurRangeCoordinates data state =
      finiteModeSchurLeftReduction data.toLinearBlockData
        (data.toLinearBlockData.decomposition state) := by
  apply Prod.ext <;> rfl

/-- The complete closed-range Schur packet generated from bounded blocks. -/
def FiniteModeContinuousSchurBlockData.toClosedRangeData
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeContinuousSchurBlockData operator Mode Complement) :
    FiniteModeSchurClosedRangeData operator Mode Complement where
  schurData := data.toLinearBlockData.toKernelData
  rangeCoordinates := finiteModeContinuousSchurRangeCoordinates data
  rangeCoordinates_eq := finiteModeContinuousSchurRangeCoordinates_eq data

/-- Closed range is automatic for a bounded four-block Schur decomposition. -/
theorem finiteModeContinuousSchur_operatorRange_closed
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeContinuousSchurBlockData operator Mode Complement) :
    IsClosed (operator.range : Set E) :=
  finiteModeSchur_operatorRange_closed data.toClosedRangeData

/-- The actual kernel is exactly the finite Schur kernel. -/
noncomputable def finiteModeContinuousSchurKernelEquiv
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeContinuousSchurBlockData operator Mode Complement) :
    operator.ker ≃ₗ[Real]
      (finiteModeSchurBlockOperator data.toLinearBlockData).ker :=
  finiteModeSchurBlockKernelEquiv data.toLinearBlockData

/-- Public bounded four-block Schur checkpoint. -/
theorem finite_mode_continuous_schur_block_gate
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeContinuousSchurBlockData operator Mode Complement) :
    IsClosed (operator.range : Set E) ∧
      Nonempty (operator.ker ≃ₗ[Real]
        (finiteModeSchurBlockOperator data.toLinearBlockData).ker) ∧
      Module.finrank Real operator.ker ≤ Fintype.card Mode :=
  ⟨finiteModeContinuousSchur_operatorRange_closed data,
    ⟨finiteModeContinuousSchurKernelEquiv data⟩,
    finiteModeSchurBlock_operatorKernel_finrank_le_card
      data.toLinearBlockData⟩

end
end P0EFTJanusProgramPFiniteModeContinuousSchurBlock4D
end JanusFormal
