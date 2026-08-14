import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteFamilyGramInjectivity4D

/-!
# Stability of finite coefficient synthesis under perturbation

Let `S_ref` and `S_target` be synthesis maps for two finite vector families.
If the reference family has a positive coefficient lower bound

`m * ‖c‖ ≤ ‖S_ref(c)‖`

and the synthesis defect satisfies

`‖S_ref(c) - S_target(c)‖ ≤ delta * ‖c‖`

with `delta < m`, then the target synthesis map is injective.  This is the
finite-dimensional perturbation mechanism used for the Candidate-A projected
kernel family: `S_target` is physical projection of the existing named basis,
and the defect is precisely its off-sector leakage.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteFamilySynthesisPerturbation4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators
open P0EFTJanusProgramPFiniteFamilyGramBasis4D
open P0EFTJanusProgramPFiniteFamilyGramInjectivity4D

variable {Index E : Type*}
  [Fintype Index] [DecidableEq Index]
  [NormedAddCommGroup E] [NormedSpace Real E]

/-- A target finite family remains linearly independent when its synthesis map
is a perturbation smaller than a positive lower bound for a reference family. -/
theorem finiteFamilySynthesis_injective_of_reference_lower_bound_of_defect
    (reference target : Index → E)
    (lowerConstant defectConstant : Real)
    (hLowerConstant : 0 < lowerConstant)
    (hDefectSmall : defectConstant < lowerConstant)
    (hReferenceLower : ∀ coefficient,
      lowerConstant * ‖coefficient‖ ≤
        ‖finiteFamilySynthesis reference coefficient‖)
    (hDefect : ∀ coefficient,
      ‖finiteFamilySynthesis reference coefficient -
          finiteFamilySynthesis target coefficient‖ ≤
        defectConstant * ‖coefficient‖) :
    Function.Injective (finiteFamilySynthesis target) := by
  intro first second hEqual
  let difference := first - second
  have hTargetZero : finiteFamilySynthesis target difference = 0 := by
    dsimp [difference]
    rw [map_sub, hEqual, sub_self]
  have hReferenceLeDefect :
      ‖finiteFamilySynthesis reference difference‖ ≤
        defectConstant * ‖difference‖ := by
    calc
      ‖finiteFamilySynthesis reference difference‖ =
          ‖(finiteFamilySynthesis reference difference -
              finiteFamilySynthesis target difference) +
            finiteFamilySynthesis target difference‖ := by
        rw [hTargetZero]
        simp
      _ ≤ ‖finiteFamilySynthesis reference difference -
              finiteFamilySynthesis target difference‖ +
            ‖finiteFamilySynthesis target difference‖ :=
        norm_add_le _ _
      _ ≤ defectConstant * ‖difference‖ + 0 := by
        exact add_le_add (hDefect difference) (by simp [hTargetZero])
      _ = defectConstant * ‖difference‖ := by simp
  have hCombined :
      lowerConstant * ‖difference‖ ≤
        defectConstant * ‖difference‖ :=
    (hReferenceLower difference).trans hReferenceLeDefect
  have hDifferenceNormZero : ‖difference‖ = 0 := by
    by_contra hNorm
    have hNormPos : 0 < ‖difference‖ :=
      lt_of_le_of_ne (norm_nonneg difference) (Ne.symm hNorm)
    have hLowerLeDefect : lowerConstant ≤ defectConstant :=
      (mul_le_mul_right hNormPos).mp hCombined
    exact (not_le_of_gt hDefectSmall) hLowerLeDefect
  exact sub_eq_zero.mp (norm_eq_zero.mp hDifferenceNormZero)

/-- The same small-defect hypotheses imply injectivity of the target Gram
endomorphism. -/
theorem finiteFamilyGramMap_injective_of_reference_lower_bound_of_defect
    (reference target : Index → E)
    (lowerConstant defectConstant : Real)
    (hLowerConstant : 0 < lowerConstant)
    (hDefectSmall : defectConstant < lowerConstant)
    (hReferenceLower : ∀ coefficient,
      lowerConstant * ‖coefficient‖ ≤
        ‖finiteFamilySynthesis reference coefficient‖)
    (hDefect : ∀ coefficient,
      ‖finiteFamilySynthesis reference coefficient -
          finiteFamilySynthesis target coefficient‖ ≤
        defectConstant * ‖coefficient‖) :
    Function.Injective (finiteFamilyGramMap target) :=
  finiteFamilyGramMap_injective_of_synthesis_injective target
    (finiteFamilySynthesis_injective_of_reference_lower_bound_of_defect
      reference target lowerConstant defectConstant hLowerConstant hDefectSmall
      hReferenceLower hDefect)

/-- Public finite synthesis-perturbation checkpoint. -/
theorem finite_family_synthesis_perturbation_gate
    (reference target : Index → E)
    (lowerConstant defectConstant : Real)
    (hLowerConstant : 0 < lowerConstant)
    (hDefectSmall : defectConstant < lowerConstant)
    (hReferenceLower : ∀ coefficient,
      lowerConstant * ‖coefficient‖ ≤
        ‖finiteFamilySynthesis reference coefficient‖)
    (hDefect : ∀ coefficient,
      ‖finiteFamilySynthesis reference coefficient -
          finiteFamilySynthesis target coefficient‖ ≤
        defectConstant * ‖coefficient‖) :
    Function.Injective (finiteFamilySynthesis target) ∧
    Function.Injective (finiteFamilyGramMap target) :=
  ⟨finiteFamilySynthesis_injective_of_reference_lower_bound_of_defect
      reference target lowerConstant defectConstant hLowerConstant hDefectSmall
      hReferenceLower hDefect,
    finiteFamilyGramMap_injective_of_reference_lower_bound_of_defect
      reference target lowerConstant defectConstant hLowerConstant hDefectSmall
      hReferenceLower hDefect⟩

end
end P0EFTJanusProgramPFiniteFamilySynthesisPerturbation4D
end JanusFormal