import Mathlib.Analysis.Normed.Operator.Prod
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeSchurExplicitGreen4D

/-!
# Quantitative operator-norm bound for a Schur Green factorization

For a Green operator represented by five bounded factors

`T⁻¹ ∘ R ∘ diag(S⁻¹,D⁻¹) ∘ L ∘ T`,

the operator norm is bounded by the product of the five factor norms.  This is
the quantitative estimate used by the nondegenerate finite-Schur frontier.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteModeSchurGreenNormBound4D

set_option autoImplicit false
noncomputable section

variable {E F G : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]
  [NormedAddCommGroup G] [NormedSpace Real G]

/-- A five-factor bounded realization of one Green operator. -/
structure FiniteModeSchurGreenFactorization
    (green : E →L[Real] E) where
  coordinates : E ≃L[Real] F × G
  rightReduction : F × G →L[Real] F × G
  diagonalInverse : F × G →L[Real] F × G
  leftReduction : F × G →L[Real] F × G
  green_eq :
    green =
      coordinates.symm.toContinuousLinearMap.comp
        (rightReduction.comp
          (diagonalInverse.comp
            (leftReduction.comp coordinates.toContinuousLinearMap)))

/-- Product of the norms of the five factors. -/
def FiniteModeSchurGreenFactorization.factorNormBound
    {green : E →L[Real] E}
    (factorization : FiniteModeSchurGreenFactorization (F := F) (G := G) green) :
    Real :=
  ‖factorization.coordinates.symm.toContinuousLinearMap‖ *
    ‖factorization.rightReduction‖ *
    ‖factorization.diagonalInverse‖ *
    ‖factorization.leftReduction‖ *
    ‖factorization.coordinates.toContinuousLinearMap‖

theorem FiniteModeSchurGreenFactorization.factorNormBound_nonneg
    {green : E →L[Real] E}
    (factorization : FiniteModeSchurGreenFactorization (F := F) (G := G) green) :
    0 ≤ factorization.factorNormBound := by
  unfold FiniteModeSchurGreenFactorization.factorNormBound
  positivity

/-- The explicit Schur Green operator is controlled by the product of the
coordinate, triangular-reduction and diagonal-inverse norms. -/
theorem FiniteModeSchurGreenFactorization.norm_le_factorNormBound
    {green : E →L[Real] E}
    (factorization : FiniteModeSchurGreenFactorization (F := F) (G := G) green) :
    ‖green‖ ≤ factorization.factorNormBound := by
  rw [factorization.green_eq]
  unfold FiniteModeSchurGreenFactorization.factorNormBound
  calc
    ‖factorization.coordinates.symm.toContinuousLinearMap.comp
        (factorization.rightReduction.comp
          (factorization.diagonalInverse.comp
            (factorization.leftReduction.comp
              factorization.coordinates.toContinuousLinearMap)))‖
        ≤ ‖factorization.coordinates.symm.toContinuousLinearMap‖ *
          ‖factorization.rightReduction.comp
            (factorization.diagonalInverse.comp
              (factorization.leftReduction.comp
                factorization.coordinates.toContinuousLinearMap))‖ := by
            exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖factorization.coordinates.symm.toContinuousLinearMap‖ *
          (‖factorization.rightReduction‖ *
            ‖factorization.diagonalInverse.comp
              (factorization.leftReduction.comp
                factorization.coordinates.toContinuousLinearMap)‖) := by
            exact mul_le_mul_of_nonneg_left
              (ContinuousLinearMap.opNorm_comp_le _ _) (norm_nonneg _)
    _ ≤ ‖factorization.coordinates.symm.toContinuousLinearMap‖ *
          (‖factorization.rightReduction‖ *
            (‖factorization.diagonalInverse‖ *
              ‖factorization.leftReduction.comp
                factorization.coordinates.toContinuousLinearMap‖)) := by
            gcongr
            exact ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖factorization.coordinates.symm.toContinuousLinearMap‖ *
          (‖factorization.rightReduction‖ *
            (‖factorization.diagonalInverse‖ *
              (‖factorization.leftReduction‖ *
                ‖factorization.coordinates.toContinuousLinearMap‖))) := by
            gcongr
            exact ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖factorization.coordinates.symm.toContinuousLinearMap‖ *
          ‖factorization.rightReduction‖ *
          ‖factorization.diagonalInverse‖ *
          ‖factorization.leftReduction‖ *
          ‖factorization.coordinates.toContinuousLinearMap‖ := by
            ring

/-- Public quantitative Schur-propagator checkpoint. -/
theorem finite_mode_schur_green_norm_bound_gate
    (green : E →L[Real] E)
    (factorization : FiniteModeSchurGreenFactorization (F := F) (G := G) green) :
    0 ≤ factorization.factorNormBound ∧
      ‖green‖ ≤ factorization.factorNormBound :=
  ⟨factorization.factorNormBound_nonneg,
    factorization.norm_le_factorNormBound⟩

end
end P0EFTJanusProgramPFiniteModeSchurGreenNormBound4D
end JanusFormal
