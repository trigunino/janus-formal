import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeOrthogonalSchurCoercivity4D

/-!
# Orthogonal Schur inversion from ambient coercivity

Elliptic estimates are naturally stated for the original self-adjoint operator,
not for a separately named compressed block.  For `y ∈ Kᗮ`, orthogonal
projection does not change the pairing with `y`, hence

`⟪y, D y⟫ = ⟪y, H y⟫`.

Therefore coercivity of the full operator on the complement of the selected
finite mode space supplies exactly the complementary-block coercivity consumed
by the Schur construction.  This file records that reduction and its concrete
named-reference-vector form.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteModeOrthogonalSchurAmbientCoercivity4D

set_option autoImplicit false
set_option maxHeartbeats 5600000
set_option synthInstance.maxHeartbeats 2800000

noncomputable section

open Set
open scoped InnerProductSpace
open P0EFTJanusProgramPFiniteModeCanonicalSchurDecomposition4D
open P0EFTJanusProgramPFiniteModeOrthogonalSchurDecomposition4D
open P0EFTJanusProgramPFiniteModeOrthogonalSchurNamedVectors4D
open P0EFTJanusProgramPFiniteModeOrthogonalSchurCoercivity4D

variable {E Mode : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype Mode] [DecidableEq Mode]

/-- Compression to `Kᗮ` preserves the quadratic pairing of vectors already in
`Kᗮ`. -/
theorem finiteModeOrthogonalComplementBlock_inner_eq_ambient
    (operator : E →L[Real] E)
    (modeSubspace : Submodule Real E)
    (modeEquiv : (Mode → Real) ≃L[Real] modeSubspace)
    (vector : modeSubspaceᗮ) :
    ⟪vector,
      finiteModeOrthogonalComplementBlock operator modeSubspace modeEquiv
        vector, Real⟫ =
      ⟪(vector : E), operator (vector : E), Real⟫ := by
  simpa [finiteModeOrthogonalComplementBlock,
    finiteModeCanonicalBlockD, finiteModeConjugatedOperator,
    finiteModeOrthogonalDecomposition, real_inner_comm]

/-- Ambient PDE input: coercivity of `H` on the canonical orthogonal complement
of a finite subspace. -/
structure FiniteModeOrthogonalSchurAmbientCoercivityData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator) where
  modeSubspace : Submodule Real E
  modeEquiv : (Mode → Real) ≃L[Real] modeSubspace
  constant : Real
  constant_pos : 0 < constant
  coercive : ∀ vector : modeSubspaceᗮ,
    constant * ‖vector‖ ^ 2 ≤
      ⟪(vector : E), operator (vector : E), Real⟫

namespace FiniteModeOrthogonalSchurAmbientCoercivityData

variable {operator : E →L[Real] E}
variable {hSelfAdjoint : IsSelfAdjoint operator}

/-- Convert the ambient estimate to complementary-block coercivity. -/
def toComplementCoercivity
    (data : FiniteModeOrthogonalSchurAmbientCoercivityData
      (Mode := Mode) operator hSelfAdjoint) :
    FiniteModeOrthogonalSchurCoercivityData
      (Mode := Mode) operator hSelfAdjoint where
  modeSubspace := data.modeSubspace
  modeEquiv := data.modeEquiv
  constant := data.constant
  constant_pos := data.constant_pos
  coercive := by
    intro vector
    rw [finiteModeOrthogonalComplementBlock_inner_eq_ambient operator
      data.modeSubspace data.modeEquiv vector]
    exact data.coercive vector

/-- Ambient coercivity constructs the entire orthogonal Schur packet. -/
noncomputable def toOrthogonalSchurData
    (data : FiniteModeOrthogonalSchurAmbientCoercivityData
      (Mode := Mode) operator hSelfAdjoint) :
    FiniteModeOrthogonalSchurDecompositionData operator Mode :=
  data.toComplementCoercivity.toOrthogonalSchurData

/-- Public ambient-coercivity checkpoint. -/
theorem finite_mode_orthogonal_schur_ambient_coercivity_gate
    (data : FiniteModeOrthogonalSchurAmbientCoercivityData
      (Mode := Mode) operator hSelfAdjoint) :
    Function.Bijective
        (finiteModeOrthogonalComplementBlock operator data.modeSubspace
          data.modeEquiv) ∧
      Nonempty (FiniteModeOrthogonalSchurDecompositionData operator Mode) :=
  data.toComplementCoercivity.finite_mode_orthogonal_schur_coercivity_gate

end FiniteModeOrthogonalSchurAmbientCoercivityData

/-- Concrete reference vectors together with coercivity of the original
operator on their canonical orthogonal complement. -/
structure FiniteModeOrthogonalSchurNamedAmbientCoercivityData
    (operator : E →L[Real] E)
    (hSelfAdjoint : IsSelfAdjoint operator) where
  vector : Mode → E
  linearIndependent : LinearIndependent Real vector
  constant : Real
  constant_pos : 0 < constant
  coercive : ∀ state : (finiteModeNamedSubspace vector)ᗮ,
    constant * ‖state‖ ^ 2 ≤
      ⟪(state : E), operator (state : E), Real⟫

namespace FiniteModeOrthogonalSchurNamedAmbientCoercivityData

variable {operator : E →L[Real] E}
variable {hSelfAdjoint : IsSelfAdjoint operator}

/-- Construct the ambient finite-subspace coercivity packet. -/
def toAmbientCoercivity
    (data : FiniteModeOrthogonalSchurNamedAmbientCoercivityData
      (Mode := Mode) operator hSelfAdjoint) :
    FiniteModeOrthogonalSchurAmbientCoercivityData
      (Mode := Mode) operator hSelfAdjoint where
  modeSubspace := finiteModeNamedSubspace data.vector
  modeEquiv := finiteModeNamedContinuousEquiv data.vector
    data.linearIndependent
  constant := data.constant
  constant_pos := data.constant_pos
  coercive := data.coercive

/-- Convert to the preceding compressed-block named coercivity packet. -/
def toNamedComplementCoercivity
    (data : FiniteModeOrthogonalSchurNamedAmbientCoercivityData
      (Mode := Mode) operator hSelfAdjoint) :
    FiniteModeOrthogonalSchurNamedCoercivityData
      (Mode := Mode) operator hSelfAdjoint where
  vector := data.vector
  linearIndependent := data.linearIndependent
  constant := data.constant
  constant_pos := data.constant_pos
  coercive := by
    intro state
    rw [finiteModeOrthogonalComplementBlock_inner_eq_ambient operator
      (finiteModeNamedSubspace data.vector)
      (finiteModeNamedContinuousEquiv data.vector data.linearIndependent)
      state]
    exact data.coercive state

/-- Public named ambient-coercivity checkpoint. -/
theorem finite_mode_orthogonal_schur_named_ambient_coercivity_gate
    (data : FiniteModeOrthogonalSchurNamedAmbientCoercivityData
      (Mode := Mode) operator hSelfAdjoint) :
    LinearIndependent Real data.vector ∧
      Function.Bijective
        (finiteModeOrthogonalComplementBlock operator
          (finiteModeNamedSubspace data.vector)
          (finiteModeNamedContinuousEquiv data.vector
            data.linearIndependent)) ∧
      Nonempty (FiniteModeOrthogonalSchurDecompositionData operator Mode) :=
  data.toNamedComplementCoercivity.finite_mode_orthogonal_schur_named_coercivity_gate

end FiniteModeOrthogonalSchurNamedAmbientCoercivityData

end
end P0EFTJanusProgramPFiniteModeOrthogonalSchurAmbientCoercivity4D
end JanusFormal
