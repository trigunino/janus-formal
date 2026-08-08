import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeSchurExplicitGreen4D

/-!
# Quantitative norm bound for the explicit Schur Green operator

The block formula

`G = T⁻¹ R diag(S⁻¹,D⁻¹) L T`

gives an immediate product bound for the propagator norm.  This file records
that bound explicitly so it can be used as a perturbative radius without
re-running the abstract bounded inverse theorem.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteModeSchurExplicitGreenBound4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteModeSchurExplicitGreen4D
open P0EFTJanusProgramPFiniteModeContinuousSchurBlock4D

variable {E : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E] [CompleteSpace E]

/-- Product bound read directly from the five bounded factors of the Green
formula. -/
def finiteModeSchurExplicitGreenNormBound
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeSchurExplicitGreenData operator Mode Complement) : Real :=
  ‖data.blocks.decomposition.symm.toContinuousLinearMap‖ *
    ‖finiteModeContinuousSchurRightReduction data‖ *
    ‖finiteModeSchurDiagonalInverse data‖ *
    ‖finiteModeContinuousSchurLeftReduction data.blocks‖ *
    ‖data.blocks.decomposition.toContinuousLinearMap‖

/-- The explicit Green norm is controlled by the product of the coordinate,
triangular and diagonal inverse norms. -/
theorem finiteModeSchurExplicitGreen_norm_le
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeSchurExplicitGreenData operator Mode Complement) :
    ‖finiteModeSchurExplicitGreen data‖ ≤
      finiteModeSchurExplicitGreenNormBound data := by
  let T := data.blocks.decomposition.toContinuousLinearMap
  let Tinv := data.blocks.decomposition.symm.toContinuousLinearMap
  let L := finiteModeContinuousSchurLeftReduction data.blocks
  let Dinv := finiteModeSchurDiagonalInverse data
  let R := finiteModeContinuousSchurRightReduction data
  have hTL : ‖L.comp T‖ ≤ ‖L‖ * ‖T‖ :=
    ContinuousLinearMap.opNorm_comp_le L T
  have hD : ‖Dinv.comp (L.comp T)‖ ≤ ‖Dinv‖ * ‖L.comp T‖ :=
    ContinuousLinearMap.opNorm_comp_le Dinv (L.comp T)
  have hR : ‖R.comp (Dinv.comp (L.comp T))‖ ≤
      ‖R‖ * ‖Dinv.comp (L.comp T)‖ :=
    ContinuousLinearMap.opNorm_comp_le R (Dinv.comp (L.comp T))
  have hTinv : ‖Tinv.comp (R.comp (Dinv.comp (L.comp T)))‖ ≤
      ‖Tinv‖ * ‖R.comp (Dinv.comp (L.comp T))‖ :=
    ContinuousLinearMap.opNorm_comp_le Tinv
      (R.comp (Dinv.comp (L.comp T)))
  change ‖Tinv.comp (R.comp (Dinv.comp (L.comp T)))‖ ≤ _
  calc
    ‖Tinv.comp (R.comp (Dinv.comp (L.comp T)))‖
        ≤ ‖Tinv‖ * ‖R.comp (Dinv.comp (L.comp T))‖ := hTinv
    _ ≤ ‖Tinv‖ * (‖R‖ * ‖Dinv.comp (L.comp T)‖) := by
      exact mul_le_mul_of_nonneg_left hR (norm_nonneg _)
    _ ≤ ‖Tinv‖ * (‖R‖ * (‖Dinv‖ * ‖L.comp T‖)) := by
      gcongr
    _ ≤ ‖Tinv‖ * (‖R‖ * (‖Dinv‖ * (‖L‖ * ‖T‖))) := by
      gcongr
    _ = finiteModeSchurExplicitGreenNormBound data := by
      simp [finiteModeSchurExplicitGreenNormBound, T, Tinv, L, Dinv, R]
      ring

/-- The product bound is nonnegative. -/
theorem finiteModeSchurExplicitGreenNormBound_nonnegative
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeSchurExplicitGreenData operator Mode Complement) :
    0 ≤ finiteModeSchurExplicitGreenNormBound data := by
  unfold finiteModeSchurExplicitGreenNormBound
  positivity

/-- Public quantitative propagator checkpoint. -/
theorem finite_mode_schur_explicit_green_bound_gate
    {operator : E →L[Real] E}
    {Mode Complement : Type*}
    [Fintype Mode] [DecidableEq Mode]
    [NormedAddCommGroup Complement] [NormedSpace Real Complement]
    (data : FiniteModeSchurExplicitGreenData operator Mode Complement) :
    ‖finiteModeSchurExplicitGreen data‖ ≤
        finiteModeSchurExplicitGreenNormBound data ∧
      0 ≤ finiteModeSchurExplicitGreenNormBound data :=
  ⟨finiteModeSchurExplicitGreen_norm_le data,
    finiteModeSchurExplicitGreenNormBound_nonnegative data⟩

end
end P0EFTJanusProgramPFiniteModeSchurExplicitGreenBound4D
end JanusFormal
