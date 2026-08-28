import Mathlib.Analysis.InnerProductSpace.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeOrthogonalSchurNamedVectors4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPSelfAdjointLowerBoundSurjective4D

/-!
# Orthogonal Schur inversion from complementary coercivity

For a self-adjoint operator and an orthogonal decomposition

`E = K ⊕ Kᗮ`,

the canonical complementary Schur block is self-adjoint on `Kᗮ`.  Therefore a
quadratic coercivity estimate on that block yields a norm lower bound by
Cauchy--Schwarz, then surjectivity and a bounded inverse by the existing
self-adjoint lower-bound theorem.

This removes the supplied inverse of `D` from the finite-mode Schur interface.
For physically named reference vectors, the subspace `K`, its finite basis and
the orthogonal decomposition are all constructed automatically.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteModeOrthogonalSchurCoercivity4D

set_option autoImplicit false
set_option maxHeartbeats 4800000
set_option synthInstance.maxHeartbeats 2400000

noncomputable section

open Set
open scoped InnerProductSpace
open P0EFTJanusProgramPFiniteModeCanonicalSchurDecomposition4D
open P0EFTJanusProgramPFiniteModeOrthogonalSchurDecomposition4D
open P0EFTJanusProgramPFiniteModeOrthogonalSchurBasis4D
open P0EFTJanusProgramPFiniteModeOrthogonalSchurNamedVectors4D
open P0EFTJanusProgramPSelfAdjointLowerBoundSurjective4D

variable {E Mode : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype Mode] [DecidableEq Mode]

/-- Canonical complementary block on the orthogonal complement of the selected
finite mode subspace. -/
def finiteModeOrthogonalComplementBlock
    (operator : E →L[Real] E)
    (modeSubspace : Submodule Real E)
    (modeEquiv : (Mode → Real) ≃L[Real] modeSubspace) :
    modeSubspaceᗮ →L[Real] modeSubspaceᗮ :=
  finiteModeCanonicalBlockD operator
    (finiteModeOrthogonalDecomposition modeSubspace modeEquiv)

/-- The canonical orthogonal complementary block of a self-adjoint operator is
self-adjoint. -/
theorem finiteModeOrthogonalComplementBlock_isSelfAdjoint
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator)
    (modeSubspace : Submodule Real E)
    (modeEquiv : (Mode → Real) ≃L[Real] modeSubspace) :
    IsSelfAdjoint
      (finiteModeOrthogonalComplementBlock operator modeSubspace modeEquiv) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro first second
  have hOperator := hSelfAdjoint.isSymmetric (first : E) (second : E)
  simpa [finiteModeOrthogonalComplementBlock,
    finiteModeCanonicalBlockD, finiteModeConjugatedOperator,
    finiteModeOrthogonalDecomposition, real_inner_comm] using hOperator

/-- PDE input on the canonical orthogonal complementary block. -/
structure FiniteModeOrthogonalSchurCoercivityData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator) where
  modeSubspace : Submodule Real E
  modeEquiv : (Mode → Real) ≃L[Real] modeSubspace
  constant : Real
  constant_pos : 0 < constant
  coercive : ∀ vector : modeSubspaceᗮ,
    constant * ‖vector‖ ^ 2 ≤
      ⟪vector,
        finiteModeOrthogonalComplementBlock operator modeSubspace modeEquiv
          vector⟫_Real

namespace FiniteModeOrthogonalSchurCoercivityData

variable {operator : E →L[Real] E}
variable {hSelfAdjoint : IsSelfAdjoint operator}

/-- Quadratic coercivity gives the operator norm lower bound on `D`. -/
theorem complement_lowerBound
    (data : FiniteModeOrthogonalSchurCoercivityData
      (Mode := Mode) operator hSelfAdjoint)
    (vector : data.modeSubspaceᗮ) :
    data.constant * ‖vector‖ ≤
      ‖finiteModeOrthogonalComplementBlock operator data.modeSubspace
        data.modeEquiv vector‖ := by
  by_cases hNorm : ‖vector‖ = 0
  · simp [hNorm]
  · have hNormPos : 0 < ‖vector‖ :=
      lt_of_le_of_ne (norm_nonneg _) (Ne.symm hNorm)
    have hInnerUpper :
        ⟪vector,
          finiteModeOrthogonalComplementBlock operator data.modeSubspace
            data.modeEquiv vector⟫_Real ≤
          ‖vector‖ *
            ‖finiteModeOrthogonalComplementBlock operator data.modeSubspace
              data.modeEquiv vector‖ :=
      real_inner_le_norm _ _
    have hMul :
        ‖vector‖ * (data.constant * ‖vector‖) ≤
          ‖vector‖ *
            ‖finiteModeOrthogonalComplementBlock operator data.modeSubspace
              data.modeEquiv vector‖ := by
      calc
        ‖vector‖ * (data.constant * ‖vector‖) =
            data.constant * ‖vector‖ ^ 2 := by ring
        _ ≤ ⟪vector,
              finiteModeOrthogonalComplementBlock operator data.modeSubspace
                data.modeEquiv vector⟫_Real :=
          data.coercive vector
        _ ≤ ‖vector‖ *
              ‖finiteModeOrthogonalComplementBlock operator data.modeSubspace
                data.modeEquiv vector‖ := hInnerUpper
    exact le_of_mul_le_mul_left hMul hNormPos

/-- Reciprocal coercivity constant in the form used by the global lower-bound
theorem. -/
def inverseConstant
    (data : FiniteModeOrthogonalSchurCoercivityData
      (Mode := Mode) operator hSelfAdjoint) : NNReal :=
  ⟨data.constant⁻¹, inv_nonneg.mpr (le_of_lt data.constant_pos)⟩

/-- Global lower bound `‖x‖ ≤ c⁻¹ ‖Dx‖`. -/
theorem complement_globalLowerBound
    (data : FiniteModeOrthogonalSchurCoercivityData
      (Mode := Mode) operator hSelfAdjoint)
    (vector : data.modeSubspaceᗮ) :
    ‖vector‖ ≤ (data.inverseConstant : Real) *
      ‖finiteModeOrthogonalComplementBlock operator data.modeSubspace
        data.modeEquiv vector‖ := by
  have hLower := data.complement_lowerBound vector
  have hConstantNe : data.constant ≠ 0 := ne_of_gt data.constant_pos
  change ‖vector‖ ≤ data.constant⁻¹ *
    ‖finiteModeOrthogonalComplementBlock operator data.modeSubspace
      data.modeEquiv vector‖
  calc
    ‖vector‖ = data.constant⁻¹ * (data.constant * ‖vector‖) := by
      rw [← mul_assoc, inv_mul_cancel₀ hConstantNe, one_mul]
    _ ≤ data.constant⁻¹ *
        ‖finiteModeOrthogonalComplementBlock operator data.modeSubspace
          data.modeEquiv vector‖ :=
      mul_le_mul_of_nonneg_left hLower
        (inv_nonneg.mpr (le_of_lt data.constant_pos))

/-- The canonical complementary block is bijective. -/
theorem complement_bijective
    (data : FiniteModeOrthogonalSchurCoercivityData
      (Mode := Mode) operator hSelfAdjoint) :
    Function.Bijective
      (finiteModeOrthogonalComplementBlock operator data.modeSubspace
        data.modeEquiv) :=
  selfAdjoint_bijective_of_globalLowerBound
    (finiteModeOrthogonalComplementBlock operator data.modeSubspace
      data.modeEquiv)
    (finiteModeOrthogonalComplementBlock_isSelfAdjoint operator hSelfAdjoint
      data.modeSubspace data.modeEquiv)
    data.inverseConstant data.complement_globalLowerBound

/-- Continuous inverse of `D`, constructed rather than supplied. -/
noncomputable def complementEquiv
    (data : FiniteModeOrthogonalSchurCoercivityData
      (Mode := Mode) operator hSelfAdjoint) :
    data.modeSubspaceᗮ ≃L[Real] data.modeSubspaceᗮ :=
  ContinuousLinearEquiv.ofBijective
    (finiteModeOrthogonalComplementBlock operator data.modeSubspace
      data.modeEquiv)
    (LinearMap.ker_eq_bot.mpr data.complement_bijective.1)
    (LinearMap.range_eq_top.mpr data.complement_bijective.2)

/-- Coercivity constructs the complete canonical orthogonal Schur packet. -/
noncomputable def toOrthogonalSchurData
    (data : FiniteModeOrthogonalSchurCoercivityData
      (Mode := Mode) operator hSelfAdjoint) :
    FiniteModeOrthogonalSchurDecompositionData (Mode := Mode) operator where
  modeSubspace := data.modeSubspace
  modeEquiv := data.modeEquiv
  complementEquiv := data.complementEquiv
  complementEquiv_eq := rfl

/-- Public coercivity-to-Schur checkpoint. -/
theorem finite_mode_orthogonal_schur_coercivity_gate
    (data : FiniteModeOrthogonalSchurCoercivityData
      (Mode := Mode) operator hSelfAdjoint) :
    Function.Bijective
        (finiteModeOrthogonalComplementBlock operator data.modeSubspace
          data.modeEquiv) ∧
      Nonempty
        (FiniteModeOrthogonalSchurDecompositionData (Mode := Mode) operator) :=
  ⟨data.complement_bijective, ⟨data.toOrthogonalSchurData⟩⟩

end FiniteModeOrthogonalSchurCoercivityData

/-- The strongest finite reference-mode input: concrete linearly independent
ambient vectors and coercivity of the automatically extracted complementary
block. -/
structure FiniteModeOrthogonalSchurNamedCoercivityData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator) where
  vector : Mode → E
  linearIndependent : LinearIndependent Real vector
  constant : Real
  constant_pos : 0 < constant
  coercive : ∀ state : (finiteModeNamedSubspace vector)ᗮ,
    constant * ‖state‖ ^ 2 ≤
      ⟪state,
        finiteModeOrthogonalComplementBlock operator
          (finiteModeNamedSubspace vector)
          (finiteModeNamedContinuousEquiv vector linearIndependent) state⟫_Real

namespace FiniteModeOrthogonalSchurNamedCoercivityData

variable {operator : E →L[Real] E}
variable {hSelfAdjoint : IsSelfAdjoint operator}

/-- Forget only the concrete vector presentation and obtain the coercive
orthogonal subspace packet. -/
def toCoercivityData
    (data : FiniteModeOrthogonalSchurNamedCoercivityData
      (Mode := Mode) operator hSelfAdjoint) :
    FiniteModeOrthogonalSchurCoercivityData
      (Mode := Mode) operator hSelfAdjoint where
  modeSubspace := finiteModeNamedSubspace data.vector
  modeEquiv := finiteModeNamedContinuousEquiv data.vector
    data.linearIndependent
  constant := data.constant
  constant_pos := data.constant_pos
  coercive := data.coercive

/-- Complete orthogonal Schur data generated from named vectors and one
coercivity estimate. -/
noncomputable def toOrthogonalSchurData
    (data : FiniteModeOrthogonalSchurNamedCoercivityData
      (Mode := Mode) operator hSelfAdjoint) :
    FiniteModeOrthogonalSchurDecompositionData (Mode := Mode) operator :=
  data.toCoercivityData.toOrthogonalSchurData

/-- Public named-vector coercivity checkpoint. -/
theorem finite_mode_orthogonal_schur_named_coercivity_gate
    (data : FiniteModeOrthogonalSchurNamedCoercivityData
      (Mode := Mode) operator hSelfAdjoint) :
    LinearIndependent Real data.vector ∧
      Function.Bijective
        (finiteModeOrthogonalComplementBlock operator
          (finiteModeNamedSubspace data.vector)
          (finiteModeNamedContinuousEquiv data.vector
            data.linearIndependent)) ∧
      Nonempty
        (FiniteModeOrthogonalSchurDecompositionData (Mode := Mode) operator) :=
  ⟨data.linearIndependent,
    data.toCoercivityData.complement_bijective,
    ⟨data.toOrthogonalSchurData⟩⟩

end FiniteModeOrthogonalSchurNamedCoercivityData

end
end P0EFTJanusProgramPFiniteModeOrthogonalSchurCoercivity4D
end JanusFormal
