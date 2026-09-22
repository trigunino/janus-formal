import Mathlib.Analysis.InnerProductSpace.Adjoint

/-! Assembly of three concrete Hilbert columns and one common physical operator. -/
namespace JanusFormal
namespace P0EFTJanusProgramPT12ThreeBlockHilbertAssembly4D
set_option autoImplicit false
noncomputable section
open scoped InnerProductSpace

variable {E D A T : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
variable [NormedAddCommGroup D] [InnerProductSpace Real D]
variable [NormedAddCommGroup A] [InnerProductSpace Real A]
variable [NormedAddCommGroup T] [InnerProductSpace Real T]
variable (operator physical : E →L[Real] E)
variable (includeD : D →L[Real] E) (includeA : A →L[Real] E) (includeT : T →L[Real] E)
variable (readD : E →L[Real] D) (readA : E →L[Real] A) (readT : E →L[Real] T)
variable (blockD : D →L[Real] D) (blockA : A →L[Real] A) (blockT : T →L[Real] T)

def threeBlockOperator : E →L[Real] E :=
  includeD.comp (blockD.comp readD) + includeA.comp (blockA.comp readA) + includeT.comp (blockT.comp readT)

omit [CompleteSpace E] in
theorem threeBlock_sum_eq
    (hReconstruct : ∀ vector, includeD (readD vector) + includeA (readA vector) + includeT (readT vector) = vector)
    (hD : ∀ vector, operator (includeD vector) = includeD (blockD vector) + physical (includeD vector))
    (hA : ∀ vector, operator (includeA vector) = includeA (blockA vector) + physical (includeA vector))
    (hT : ∀ vector, operator (includeT vector) = includeT (blockT vector))
    (hPhysicalT : ∀ vector, physical (includeT vector) = 0) :
    operator = threeBlockOperator includeD includeA includeT readD readA readT blockD blockA blockT + physical := by
  ext vector
  have h := congrArg operator (hReconstruct vector)
  rw [map_add, map_add, hD, hA, hT] at h
  have hPhysical := congrArg physical (hReconstruct vector)
  rw [map_add, map_add, hPhysicalT, add_zero] at hPhysical
  change operator vector = includeD (blockD (readD vector)) + includeA (blockA (readA vector)) +
    includeT (blockT (readT vector)) + physical vector
  rw [← h, ← hPhysical]
  abel

theorem selfAdjoint_sub (hOperator : IsSelfAdjoint operator) (hPhysical : IsSelfAdjoint physical) :
    IsSelfAdjoint (operator - physical) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro first second
  change inner Real (operator first - physical first) second =
    inner Real first (operator second - physical second)
  rw [inner_sub_left, inner_sub_right]
  exact congrArg₂ (· - ·) (hOperator.isSymmetric first second) (hPhysical.isSymmetric first second)

omit [CompleteSpace E] in
theorem threeBlock_pairing
    (hOperator : operator = threeBlockOperator includeD includeA includeT readD readA readT blockD blockA blockT + physical)
    (hD : ∀ vector test, inner Real (includeD vector) test = inner Real vector (readD test))
    (hA : ∀ vector test, inner Real (includeA vector) test = inner Real vector (readA test))
    (hT : ∀ vector test, inner Real (includeT vector) test = inner Real vector (readT test))
    (first second : E) :
    inner Real (operator first) second =
      inner Real (blockD (readD first)) (readD second) +
      inner Real (blockA (readA first)) (readA second) +
      inner Real (blockT (readT first)) (readT second) + inner Real (physical first) second := by
  rw [hOperator]
  simp only [threeBlockOperator, add_apply, ContinuousLinearMap.comp_apply,
    inner_add_left, hD, hA, hT]

end
end P0EFTJanusProgramPT12ThreeBlockHilbertAssembly4D
end JanusFormal
