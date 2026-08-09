import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeOrthogonalSchurCoercivity4D

/-!
# Invariant finite-mode orthogonal reduction

When a finite subspace `K` is invariant under a self-adjoint operator `H`, its
orthogonal complement is invariant as well.  In the orthogonal block matrix of
`H` the two off-diagonal blocks therefore vanish.  The Schur operator is simply
the finite block `A`, while a norm gap on `Kᗮ` constructs the inverse of the
complement block `D`.

This is the natural route for reference modes chosen from eigenspaces or exact
symmetry modes.  It needs no positivity of the quadratic form and no supplied
complement inverse.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteModeInvariantOrthogonalReduction4D

set_option autoImplicit false
set_option maxHeartbeats 7200000
set_option synthInstance.maxHeartbeats 3600000

noncomputable section

open Set
open scoped InnerProductSpace
open P0EFTJanusProgramPFiniteModeCanonicalSchurDecomposition4D
open P0EFTJanusProgramPFiniteModeOrthogonalSchurDecomposition4D
open P0EFTJanusProgramPFiniteModeOrthogonalSchurNamedVectors4D
open P0EFTJanusProgramPFiniteModeOrthogonalSchurCoercivity4D
open P0EFTJanusProgramPSelfAdjointLowerBoundSurjective4D

variable {E Mode : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype Mode] [DecidableEq Mode]

/-- A finite invariant subspace and a spectral norm gap on its orthogonal
complement. -/
structure FiniteModeInvariantOrthogonalGapData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator) where
  modeSubspace : Submodule Real E
  modeEquiv : (Mode → Real) ≃L[Real] modeSubspace
  invariant : ∀ vector : modeSubspace,
    operator (vector : E) ∈ modeSubspace
  gap : Real
  gap_pos : 0 < gap
  lowerBound : ∀ vector : modeSubspaceᗮ,
    gap * ‖vector‖ ≤ ‖operator (vector : E)‖

namespace FiniteModeInvariantOrthogonalGapData

variable {operator : E →L[Real] E}
variable {hSelfAdjoint : IsSelfAdjoint operator}

/-- Self-adjointness makes the orthogonal complement invariant. -/
theorem orthogonal_invariant
    (data : FiniteModeInvariantOrthogonalGapData
      (Mode := Mode) operator hSelfAdjoint)
    (vector : data.modeSubspaceᗮ) :
    operator (vector : E) ∈ data.modeSubspaceᗮ := by
  rw [Submodule.mem_orthogonal']
  intro mode hMode
  let modeVector : data.modeSubspace := ⟨mode, hMode⟩
  have hImage : operator (modeVector : E) ∈ data.modeSubspace :=
    data.invariant modeVector
  calc
    ⟪operator (vector : E), mode, Real⟫ =
        ⟪(vector : E), operator mode, Real⟫ :=
      hSelfAdjoint.isSymmetric (vector : E) mode
    _ = 0 := vector.2 _ hImage

/-- On the invariant complement, the canonical block `D` is literally the
original operator with its codomain restricted. -/
theorem complementBlock_apply
    (data : FiniteModeInvariantOrthogonalGapData
      (Mode := Mode) operator hSelfAdjoint)
    (vector : data.modeSubspaceᗮ) :
    finiteModeOrthogonalComplementBlock operator data.modeSubspace
        data.modeEquiv vector =
      ⟨operator (vector : E), data.orthogonal_invariant vector⟩ := by
  apply Subtype.ext
  simpa [finiteModeOrthogonalComplementBlock,
    finiteModeCanonicalBlockD, finiteModeConjugatedOperator,
    finiteModeOrthogonalDecomposition]

/-- Gap for the canonical complementary block. -/
theorem complement_lowerBound
    (data : FiniteModeInvariantOrthogonalGapData
      (Mode := Mode) operator hSelfAdjoint)
    (vector : data.modeSubspaceᗮ) :
    data.gap * ‖vector‖ ≤
      ‖finiteModeOrthogonalComplementBlock operator data.modeSubspace
        data.modeEquiv vector‖ := by
  rw [data.complementBlock_apply vector]
  exact data.lowerBound vector

/-- Reciprocal gap. -/
def inverseGap
    (data : FiniteModeInvariantOrthogonalGapData
      (Mode := Mode) operator hSelfAdjoint) : NNReal :=
  ⟨data.gap⁻¹, inv_nonneg.mpr (le_of_lt data.gap_pos)⟩

/-- Global lower bound used by the self-adjoint surjectivity theorem. -/
theorem complement_globalLowerBound
    (data : FiniteModeInvariantOrthogonalGapData
      (Mode := Mode) operator hSelfAdjoint)
    (vector : data.modeSubspaceᗮ) :
    ‖vector‖ ≤ (data.inverseGap : Real) *
      ‖finiteModeOrthogonalComplementBlock operator data.modeSubspace
        data.modeEquiv vector‖ := by
  have hLower := data.complement_lowerBound vector
  have hGapNe : data.gap ≠ 0 := ne_of_gt data.gap_pos
  change ‖vector‖ ≤ data.gap⁻¹ *
    ‖finiteModeOrthogonalComplementBlock operator data.modeSubspace
      data.modeEquiv vector‖
  calc
    ‖vector‖ = data.gap⁻¹ * (data.gap * ‖vector‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ hGapNe, one_mul]
    _ ≤ data.gap⁻¹ *
        ‖finiteModeOrthogonalComplementBlock operator data.modeSubspace
          data.modeEquiv vector‖ :=
      mul_le_mul_of_nonneg_left hLower
        (inv_nonneg.mpr (le_of_lt data.gap_pos))

/-- The invariant complement block is bijective. -/
theorem complement_bijective
    (data : FiniteModeInvariantOrthogonalGapData
      (Mode := Mode) operator hSelfAdjoint) :
    Function.Bijective
      (finiteModeOrthogonalComplementBlock operator data.modeSubspace
        data.modeEquiv) :=
  selfAdjoint_bijective_of_globalLowerBound
    (finiteModeOrthogonalComplementBlock operator data.modeSubspace
      data.modeEquiv)
    (finiteModeOrthogonalComplementBlock_isSelfAdjoint operator hSelfAdjoint
      data.modeSubspace data.modeEquiv)
    data.inverseGap data.complement_globalLowerBound

/-- Continuous inverse of the invariant complementary block. -/
noncomputable def complementEquiv
    (data : FiniteModeInvariantOrthogonalGapData
      (Mode := Mode) operator hSelfAdjoint) :
    data.modeSubspaceᗮ ≃L[Real] data.modeSubspaceᗮ :=
  ContinuousLinearEquiv.ofBijective
    (finiteModeOrthogonalComplementBlock operator data.modeSubspace
      data.modeEquiv)
    data.complement_bijective

/-- Full orthogonal Schur packet. -/
noncomputable def toOrthogonalSchurData
    (data : FiniteModeInvariantOrthogonalGapData
      (Mode := Mode) operator hSelfAdjoint) :
    FiniteModeOrthogonalSchurDecompositionData operator Mode where
  modeSubspace := data.modeSubspace
  modeEquiv := data.modeEquiv
  complementEquiv := data.complementEquiv
  complementEquiv_eq := rfl

/-- The block from the complement to the invariant finite space vanishes. -/
theorem blockB_eq_zero
    (data : FiniteModeInvariantOrthogonalGapData
      (Mode := Mode) operator hSelfAdjoint) :
    data.toOrthogonalSchurData.blocks.B = 0 := by
  ext vector
  have hOrthogonal := data.orthogonal_invariant vector
  simpa [FiniteModeOrthogonalSchurDecompositionData.blocks,
    FiniteModeCanonicalSchurDecompositionData.blocks,
    finiteModeCanonicalBlockB, finiteModeConjugatedOperator,
    finiteModeOrthogonalDecomposition] using hOrthogonal

/-- The block from the finite invariant space to its complement vanishes. -/
theorem blockC_eq_zero
    (data : FiniteModeInvariantOrthogonalGapData
      (Mode := Mode) operator hSelfAdjoint) :
    data.toOrthogonalSchurData.blocks.C = 0 := by
  ext coordinate
  let modeVector : data.modeSubspace := data.modeEquiv coordinate
  have hInvariant : operator (modeVector : E) ∈ data.modeSubspace :=
    data.invariant modeVector
  simpa [FiniteModeOrthogonalSchurDecompositionData.blocks,
    FiniteModeCanonicalSchurDecompositionData.blocks,
    finiteModeCanonicalBlockC, finiteModeConjugatedOperator,
    finiteModeOrthogonalDecomposition] using hInvariant

/-- For an invariant finite subspace, the Schur operator is exactly its finite
compression `A`. -/
theorem schur_eq_blockA
    (data : FiniteModeInvariantOrthogonalGapData
      (Mode := Mode) operator hSelfAdjoint) :
    data.toOrthogonalSchurData.schur =
      data.toOrthogonalSchurData.blocks.A := by
  rw [FiniteModeOrthogonalSchurDecompositionData.schur]
  simp [finiteModeSchurOperator, data.blockB_eq_zero, data.blockC_eq_zero]

/-- Public invariant reduction checkpoint. -/
theorem finite_mode_invariant_orthogonal_reduction_gate
    (data : FiniteModeInvariantOrthogonalGapData
      (Mode := Mode) operator hSelfAdjoint) :
    data.toOrthogonalSchurData.blocks.B = 0 ∧
      data.toOrthogonalSchurData.blocks.C = 0 ∧
      data.toOrthogonalSchurData.schur =
        data.toOrthogonalSchurData.blocks.A ∧
      Function.Bijective
        (finiteModeOrthogonalComplementBlock operator data.modeSubspace
          data.modeEquiv) :=
  ⟨data.blockB_eq_zero, data.blockC_eq_zero, data.schur_eq_blockA,
    data.complement_bijective⟩

end FiniteModeInvariantOrthogonalGapData

/-- Concrete linearly independent reference vectors spanning an invariant
subspace, plus a norm gap on its orthogonal complement. -/
structure FiniteModeNamedInvariantOrthogonalGapData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator) where
  vector : Mode → E
  linearIndependent : LinearIndependent Real vector
  invariant : ∀ state : finiteModeNamedSubspace vector,
    operator (state : E) ∈ finiteModeNamedSubspace vector
  gap : Real
  gap_pos : 0 < gap
  lowerBound : ∀ state : (finiteModeNamedSubspace vector)ᗮ,
    gap * ‖state‖ ≤ ‖operator (state : E)‖

namespace FiniteModeNamedInvariantOrthogonalGapData

variable {operator : E →L[Real] E}
variable {hSelfAdjoint : IsSelfAdjoint operator}

/-- Construct the invariant finite-subspace packet. -/
def toInvariantData
    (data : FiniteModeNamedInvariantOrthogonalGapData
      (Mode := Mode) operator hSelfAdjoint) :
    FiniteModeInvariantOrthogonalGapData
      (Mode := Mode) operator hSelfAdjoint where
  modeSubspace := finiteModeNamedSubspace data.vector
  modeEquiv := finiteModeNamedContinuousEquiv data.vector
    data.linearIndependent
  invariant := data.invariant
  gap := data.gap
  gap_pos := data.gap_pos
  lowerBound := data.lowerBound

/-- Public named invariant checkpoint. -/
theorem finite_mode_named_invariant_orthogonal_reduction_gate
    (data : FiniteModeNamedInvariantOrthogonalGapData
      (Mode := Mode) operator hSelfAdjoint) :
    LinearIndependent Real data.vector ∧
      data.toInvariantData.toOrthogonalSchurData.blocks.B = 0 ∧
      data.toInvariantData.toOrthogonalSchurData.blocks.C = 0 ∧
      data.toInvariantData.toOrthogonalSchurData.schur =
        data.toInvariantData.toOrthogonalSchurData.blocks.A ∧
      Function.Bijective
        (finiteModeOrthogonalComplementBlock operator
          (finiteModeNamedSubspace data.vector)
          (finiteModeNamedContinuousEquiv data.vector
            data.linearIndependent)) :=
  ⟨data.linearIndependent,
    data.toInvariantData.blockB_eq_zero,
    data.toInvariantData.blockC_eq_zero,
    data.toInvariantData.schur_eq_blockA,
    data.toInvariantData.complement_bijective⟩

end FiniteModeNamedInvariantOrthogonalGapData

end
end P0EFTJanusProgramPFiniteModeInvariantOrthogonalReduction4D
end JanusFormal
