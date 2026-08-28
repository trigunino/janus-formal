import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeSchurKernel4D

/-!
# Nondegenerate finite Schur reduction

If both diagonal blocks in the reduced factorization

`L H R = diag(S, D)`

are bijective, then the original operator is bijective.  This file performs
that elementary reconstruction and packages the full bounded inverse when the
ambient space is complete.

The result is the zero-mode-free stratum of the Schur frontier: invertibility
of the finite Schur operator is exactly the remaining finite-dimensional
nondegeneracy test.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteModeSchurNondegenerate4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteModeSchurKernel4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- Finite Schur factorization with an invertible finite Schur block. -/
structure FiniteModeSchurNondegenerateData
    (operator : E →L[Real] E)
    (Mode Complement : Type*)
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement] where
  schurData : FiniteModeSchurKernelData operator Mode Complement
  schur_bijective : Function.Bijective schurData.schur

/-- Injectivity of the full operator follows from injectivity of the two
reduced diagonal blocks. -/
theorem finiteModeSchur_operator_injective
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurNondegenerateData operator Mode Complement) :
    Function.Injective operator := by
  intro first second hEqual
  let firstReduced := data.schurData.rightReduction.symm
    (data.schurData.decomposition first)
  let secondReduced := data.schurData.rightReduction.symm
    (data.schurData.decomposition second)
  have hReduced :
      (data.schurData.schur firstReduced.1,
        data.schurData.complementOperator firstReduced.2) =
      (data.schurData.schur secondReduced.1,
        data.schurData.complementOperator secondReduced.2) := by
    rw [← data.schurData.factorization firstReduced,
      ← data.schurData.factorization secondReduced, hEqual]
  have hFirst : firstReduced.1 = secondReduced.1 :=
    data.schur_bijective.1 (congrArg Prod.fst hReduced)
  have hSecond : firstReduced.2 = secondReduced.2 :=
    data.schurData.complement_bijective.1 (congrArg Prod.snd hReduced)
  have hState : firstReduced = secondReduced := Prod.ext hFirst hSecond
  change data.schurData.decomposition.symm
      (data.schurData.rightReduction firstReduced) =
    data.schurData.decomposition.symm
      (data.schurData.rightReduction secondReduced)
  rw [hState]

/-- Surjectivity is solved independently in the finite Schur and complementary
coordinates and transported back through the two reductions. -/
theorem finiteModeSchur_operator_surjective
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurNondegenerateData operator Mode Complement) :
    Function.Surjective operator := by
  intro target
  let targetReduced := data.schurData.leftReduction
    (data.schurData.decomposition target)
  obtain ⟨finiteSource, hFinite⟩ :=
    data.schur_bijective.2 targetReduced.1
  obtain ⟨complementSource, hComplement⟩ :=
    data.schurData.complement_bijective.2 targetReduced.2
  let reduced : (Mode → Real) × Complement :=
    (finiteSource, complementSource)
  let source : E := data.schurData.decomposition.symm
    (data.schurData.rightReduction reduced)
  refine ⟨source, ?_⟩
  apply data.schurData.decomposition.injective
  apply data.schurData.leftReduction.injective
  rw [data.schurData.factorization reduced]
  exact Prod.ext hFinite hComplement

/-- Bijectivity of the full operator. -/
theorem finiteModeSchur_operator_bijective
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurNondegenerateData operator Mode Complement) :
    Function.Bijective operator :=
  ⟨finiteModeSchur_operator_injective data,
    finiteModeSchur_operator_surjective data⟩

/-- The actual kernel is trivial on the nondegenerate Schur stratum. -/
theorem finiteModeSchur_operator_ker_eq_bot
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurNondegenerateData operator Mode Complement) :
    operator.ker = ⊥ :=
  LinearMap.ker_eq_bot.mpr (finiteModeSchur_operator_injective data)

/-- Hence the zero-mode count is exactly zero. -/
theorem finiteModeSchur_operator_kernel_finrank_zero
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurNondegenerateData operator Mode Complement) :
    Module.finrank Real operator.ker = 0 := by
  rw [finiteModeSchur_operator_ker_eq_bot data]
  simp

section Complete

variable [CompleteSpace E]

/-- The full operator as a continuous linear equivalence. -/
noncomputable def finiteModeSchurOperatorContinuousEquiv
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurNondegenerateData operator Mode Complement) :
    E ≃L[Real] E :=
  ContinuousLinearEquiv.ofBijective operator
    (finiteModeSchur_operator_bijective data)

/-- Full Green operator on the nondegenerate stratum. -/
noncomputable def finiteModeSchurFullGreen
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurNondegenerateData operator Mode Complement) :
    E →L[Real] E :=
  (finiteModeSchurOperatorContinuousEquiv data).symm.toContinuousLinearMap

@[simp]
theorem finiteModeSchurFullGreen_operator
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurNondegenerateData operator Mode Complement)
    (state : E) :
    finiteModeSchurFullGreen data (operator state) = state :=
  (finiteModeSchurOperatorContinuousEquiv data).symm_apply_apply state

@[simp]
theorem finiteModeSchur_operator_fullGreen
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurNondegenerateData operator Mode Complement)
    (state : E) :
    operator (finiteModeSchurFullGreen data state) = state :=
  (finiteModeSchurOperatorContinuousEquiv data).apply_symm_apply state

/-- Public zero-mode-free Schur checkpoint. -/
theorem finite_mode_schur_nondegenerate_gate
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [AddCommGroup Complement] [Module Real Complement]
    (data : FiniteModeSchurNondegenerateData operator Mode Complement) :
    Function.Bijective operator ∧
      operator.ker = ⊥ ∧
      Module.finrank Real operator.ker = 0 ∧
      (∀ state, finiteModeSchurFullGreen data (operator state) = state) ∧
      (∀ state, operator (finiteModeSchurFullGreen data state) = state) :=
  ⟨finiteModeSchur_operator_bijective data,
    finiteModeSchur_operator_ker_eq_bot data,
    finiteModeSchur_operator_kernel_finrank_zero data,
    finiteModeSchurFullGreen_operator data,
    finiteModeSchur_operator_fullGreen data⟩

end Complete

end
end P0EFTJanusProgramPFiniteModeSchurNondegenerate4D
end JanusFormal
