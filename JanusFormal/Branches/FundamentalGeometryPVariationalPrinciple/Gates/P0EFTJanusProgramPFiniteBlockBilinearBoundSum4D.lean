import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRobinHessianPullbackBound4D

/-!
# A distinguished Robin block plus a finite family of physical blocks

This file performs the finite estimate needed by H11 once the true H10 Robin
form has been pulled back to the common domain.  The Robin constant is fixed by
operator norms; the only free estimates are those of the remaining finite
physical family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteBlockBilinearBoundSum4D

set_option autoImplicit false
noncomputable section

open scoped BigOperators

variable {E F Block : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [NormedAddCommGroup F] [NormedSpace Real F]
  [Fintype Block]

/-- The common-domain form made from the true Robin pullback and the remaining
finite physical blocks. -/
def robinPlusFinitePhysicalForm
    (robin : F →L[Real] F →L[Real] Real)
    (projection : E →L[Real] F)
    (physical : Block → E →L[Real] E →L[Real] Real) :
    E →L[Real] E →L[Real] Real :=
  robinHessianPullback robin projection +
    ∑ block : Block, physical block

/-- The exact bound used for the H11 common-domain extension. -/
theorem norm_robinPlusFinitePhysicalForm_le
    (robin : F →L[Real] F →L[Real] Real)
    (projection : E →L[Real] F)
    (physical : Block → E →L[Real] E →L[Real] Real)
    (constant : Block → Real)
    (constant_nonneg : ∀ block, 0 ≤ constant block)
    (estimate : ∀ block first second,
      ‖physical block first second‖ ≤
        constant block * ‖first‖ * ‖second‖)
    (first second : E) :
    ‖robinPlusFinitePhysicalForm robin projection physical first second‖ ≤
      ((‖robin‖ * ‖projection‖ * ‖projection‖) +
          ∑ block : Block, constant block) *
        ‖first‖ * ‖second‖ := by
  change
    ‖robinHessianPullback robin projection first second +
      ∑ block : Block, physical block first second‖ ≤ _
  calc
    ‖robinHessianPullback robin projection first second +
        ∑ block : Block, physical block first second‖
        ≤ ‖robinHessianPullback robin projection first second‖ +
          ‖∑ block : Block, physical block first second‖ :=
      norm_add_le _ _
    _ ≤ (‖robin‖ * ‖projection‖ * ‖projection‖) * ‖first‖ * ‖second‖ +
          ∑ block : Block, ‖physical block first second‖ := by
      exact add_le_add
        (norm_robinHessianPullback_le robin projection first second)
        (norm_sum_le Finset.univ
          (fun block : Block => physical block first second))
    _ ≤ (‖robin‖ * ‖projection‖ * ‖projection‖) * ‖first‖ * ‖second‖ +
          ∑ block : Block, constant block * ‖first‖ * ‖second‖ := by
      exact add_le_add_left
        (Finset.sum_le_sum fun block _ => estimate block first second) _
    _ = ((‖robin‖ * ‖projection‖ * ‖projection‖) +
          ∑ block : Block, constant block) *
        ‖first‖ * ‖second‖ := by
      simp only [Finset.sum_mul]
      ring

/-- The finite sum is symmetric when H10 and every remaining physical block
are symmetric. -/
theorem robinPlusFinitePhysicalForm_symmetric
    (robin : F →L[Real] F →L[Real] Real)
    (projection : E →L[Real] F)
    (physical : Block → E →L[Real] E →L[Real] Real)
    (hRobin : ∀ first second, robin first second = robin second first)
    (hPhysical : ∀ block first second,
      physical block first second = physical block second first) :
    ∀ first second,
      robinPlusFinitePhysicalForm robin projection physical first second =
        robinPlusFinitePhysicalForm robin projection physical second first := by
  intro first second
  change
    robinHessianPullback robin projection first second +
        ∑ block : Block, physical block first second =
      robinHessianPullback robin projection second first +
        ∑ block : Block, physical block second first
  rw [robinHessianPullback_symmetric robin projection hRobin first second]
  congr 1
  apply Finset.sum_congr rfl
  intro block _
  exact hPhysical block first second

/-- Public estimate/symmetry checkpoint. -/
theorem robin_plus_finite_physical_bound_gate
    (robin : F →L[Real] F →L[Real] Real)
    (projection : E →L[Real] F)
    (physical : Block → E →L[Real] E →L[Real] Real)
    (constant : Block → Real)
    (constant_nonneg : ∀ block, 0 ≤ constant block)
    (estimate : ∀ block first second,
      ‖physical block first second‖ ≤
        constant block * ‖first‖ * ‖second‖)
    (hRobin : ∀ first second, robin first second = robin second first)
    (hPhysical : ∀ block first second,
      physical block first second = physical block second first) :
    (∀ first second,
      ‖robinPlusFinitePhysicalForm robin projection physical first second‖ ≤
        ((‖robin‖ * ‖projection‖ * ‖projection‖) +
            ∑ block : Block, constant block) *
          ‖first‖ * ‖second‖) ∧
    (∀ first second,
      robinPlusFinitePhysicalForm robin projection physical first second =
        robinPlusFinitePhysicalForm robin projection physical second first) :=
  ⟨norm_robinPlusFinitePhysicalForm_le robin projection physical constant
      constant_nonneg estimate,
    robinPlusFinitePhysicalForm_symmetric robin projection physical hRobin
      hPhysical⟩

end
end P0EFTJanusProgramPFiniteBlockBilinearBoundSum4D
end JanusFormal
