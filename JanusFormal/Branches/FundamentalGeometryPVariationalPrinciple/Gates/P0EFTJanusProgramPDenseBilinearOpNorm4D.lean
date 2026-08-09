import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Analysis.Normed.Operator.Basic

/-!
# Operator norm of a bilinear form from a dense-core estimate

A continuous bilinear form on a completion is controlled by any uniform product
bound verified on a dense linear core.  This elementary lemma lets the H11
construction expose the same scalar constant both before and after completion:
no extra norm estimate for the extended form is required.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPDenseBilinearOpNorm4D

set_option autoImplicit false
noncomputable section

open Set Topology

variable {Core Hilbert : Type*}
  [AddCommGroup Core] [Module Real Core]
  [NormedAddCommGroup Hilbert] [NormedSpace Real Hilbert]

/-- A product bound on a dense linear image controls the operator norm of the
completed continuous bilinear form. -/
theorem continuousBilinear_opNorm_le_of_dense
    (embedding : Core →ₗ[Real] Hilbert)
    (hDense : DenseRange embedding)
    (form : Hilbert →L[Real] Hilbert →L[Real] Real)
    (constant : Real)
    (constant_nonneg : 0 ≤ constant)
    (estimate : ∀ first second : Core,
      ‖form (embedding first) (embedding second)‖ ≤
        constant * ‖embedding first‖ * ‖embedding second‖) :
    ‖form‖ ≤ constant := by
  have hSecond : ∀ first : Core,
      ‖form (embedding first)‖ ≤ constant * ‖embedding first‖ := by
    intro first
    apply (form (embedding first)).opNorm_le_bound
      (mul_nonneg constant_nonneg (norm_nonneg _))
    intro second
    let controlled : Set Hilbert :=
      {vector | ‖form (embedding first) vector‖ ≤
        (constant * ‖embedding first‖) * ‖vector‖}
    have hControlledClosed : IsClosed controlled := by
      exact isClosed_le
        ((form (embedding first)).continuous.norm)
        (continuous_const.mul continuous_norm)
    have hRange : Set.range embedding ⊆ controlled := by
      rintro _ ⟨core, rfl⟩
      simpa [mul_assoc] using estimate first core
    have hClosure : closure (Set.range embedding) ⊆ controlled :=
      hControlledClosed.closure_subset_iff.mpr hRange
    apply hClosure
    rw [hDense.closure_eq]
    exact mem_univ second
  apply form.opNorm_le_bound constant_nonneg
  intro first
  let controlled : Set Hilbert :=
    {vector | ‖form vector‖ ≤ constant * ‖vector‖}
  have hControlledClosed : IsClosed controlled := by
    exact isClosed_le form.continuous.norm
      (continuous_const.mul continuous_norm)
  have hRange : Set.range embedding ⊆ controlled := by
    rintro _ ⟨core, rfl⟩
    exact hSecond core
  have hClosure : closure (Set.range embedding) ⊆ controlled :=
    hControlledClosed.closure_subset_iff.mpr hRange
  apply hClosure
  rw [hDense.closure_eq]
  exact mem_univ first

/-- Public dense-bilinear norm checkpoint. -/
theorem dense_bilinear_opNorm_gate
    (embedding : Core →ₗ[Real] Hilbert)
    (hDense : DenseRange embedding)
    (form : Hilbert →L[Real] Hilbert →L[Real] Real)
    (constant : Real)
    (constant_nonneg : 0 ≤ constant)
    (estimate : ∀ first second : Core,
      ‖form (embedding first) (embedding second)‖ ≤
        constant * ‖embedding first‖ * ‖embedding second‖) :
    ‖form‖ ≤ constant :=
  continuousBilinear_opNorm_le_of_dense embedding hDense form constant
    constant_nonneg estimate

end
end P0EFTJanusProgramPDenseBilinearOpNorm4D
end JanusFormal
