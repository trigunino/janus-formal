import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeBismutFreedRealLineUnitOneFormTerminal4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPDifferentiableOperatorGeometricBismutFreedComparison4D

/-!
# Families-index agreement on the real parameter line

Every alternating bilinear two-form on the one-dimensional real parameter
space vanishes.  Hence the derived BF curvature and any supplied genuine local
families-index two-form both vanish, making their agreement automatic on this
restricted base.  This does not construct or identify a higher-dimensional
local index form.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPRelativeBismutFreedRealLineFamiliesIndexTerminal4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPDifferentiableBismutFreedCurvature4D
open P0EFTJanusProgramPDifferentiableOperatorGeometricBismutFreedComparison4D
open P0EFTJanusProgramPDifferentiableOperatorGeometricBismutFreedComparisonFromOneForm4D
open P0EFTJanusProgramPRelativeBismutFreedRealLineUnitOneFormTerminal4D

universe u v

variable {E : Type u}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]

/-- A derived BF curvature vanishes on a one-dimensional real base. -/
theorem differentiableBismutFreedCurvature_eq_zero
    (data : DifferentiableLinearGeometricBismutFreedOneFormData Real)
    (base first second : Real) :
    data.curvature base first second = 0 := by
  calc
    data.curvature base first second =
        first • data.curvature base 1 second := by
      simpa using data.curvature_smul_left base first 1 second
    _ = first • (second • data.curvature base 1 1) := by
      congr 1
      simpa using data.curvature_smul_right base second 1 1
    _ = 0 := by simp

/-- Any supplied alternating local families-index two-form vanishes on the
real line. -/
theorem localFamiliesIndexTwoForm_eq_zero
    (data : LocalFamiliesIndexTwoFormData Real)
    (base first second : Real) :
    data.twoForm base first second = 0 := by
  have hDiagonal : data.twoForm base 1 1 = 0 :=
    CharZero.eq_neg_self_iff.mp (data.antisymm base 1 1)
  calc
    data.twoForm base first second =
        first • data.twoForm base 1 second := by
      have hSmul := (data.twoForm base).map_smul first (1 : Real)
      have hApplied := DFunLike.congr_fun hSmul second
      simpa using hApplied
    _ = first • (second • data.twoForm base 1 1) := by
      congr 1
      simpa using (data.twoForm base 1).map_smul second (1 : Real)
    _ = 0 := by simp [hDiagonal]

/-- Real-line BF terminal plus an independently supplied genuine local index
two-form.  No curvature agreement is assumed. -/
structure RelativeBismutFreedRealLineFamiliesIndexTerminalData
    (actual reference : Real → E →L[Real] E) where
  bismutFreed :
    RelativeBismutFreedRealLineUnitOneFormTerminalData.{u, v}
      actual reference
  localIndex : LocalFamiliesIndexTwoFormData Real

namespace RelativeBismutFreedRealLineFamiliesIndexTerminalData

/-- Families-index agreement follows from the two one-dimensional vanishing
theorems. -/
theorem familiesIndex_agreement
    {actual reference : Real → E →L[Real] E}
    (data : RelativeBismutFreedRealLineFamiliesIndexTerminalData.{u, v}
      actual reference)
    (base first second : Real) :
    data.bismutFreed.geometric.curvature base first second =
      data.localIndex.twoForm base first second := by
  rw [differentiableBismutFreedCurvature_eq_zero,
    localFamiliesIndexTwoForm_eq_zero]

/-- Canonical differential families-index packet on the real parameter line. -/
def toDifferentialFamiliesIndexComparison
    {actual reference : Real → E →L[Real] E}
    (data : RelativeBismutFreedRealLineFamiliesIndexTerminalData.{u, v}
      actual reference) :
    DifferentialFamiliesIndexComparisonData.{0, u, v}
      actual reference where
  comparison :=
    data.bismutFreed.toDifferentiableFromOneForm.toDifferentiableOperatorGeometricBismutFreedComparisonData
  localIndex := data.localIndex
  familiesIndex_agreement := data.familiesIndex_agreement

/-- Public one-dimensional families-index checkpoint. -/
theorem relative_bismut_freed_real_line_families_index_terminal_gate
    (actual reference : Real → E →L[Real] E)
    (data : RelativeBismutFreedRealLineFamiliesIndexTerminalData.{u, v}
      actual reference) :
    (∀ base first second,
      data.bismutFreed.geometric.curvature base first second = 0) ∧
    (∀ base first second,
      data.localIndex.twoForm base first second = 0) ∧
    (∀ base first second,
      data.bismutFreed.geometric.curvature base first second =
        data.localIndex.twoForm base first second) ∧
    Nonempty (DifferentialFamiliesIndexComparisonData.{0, u, v}
      actual reference) :=
  ⟨differentiableBismutFreedCurvature_eq_zero data.bismutFreed.geometric,
    localFamiliesIndexTwoForm_eq_zero data.localIndex,
    data.familiesIndex_agreement,
    ⟨data.toDifferentialFamiliesIndexComparison⟩⟩

end RelativeBismutFreedRealLineFamiliesIndexTerminalData

end
end P0EFTJanusProgramPRelativeBismutFreedRealLineFamiliesIndexTerminal4D
end JanusFormal
