import Mathlib.Analysis.Normed.Operator.Prod
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeContinuousSchurBlock4D

/-!
# Canonical four-block extraction from a continuous decomposition

A bounded operator and a continuous decomposition

`E ≃L (Mode → ℝ) × Complement`

already determine the four Schur blocks.  They are obtained by conjugating the
operator and composing with the canonical product inclusions and projections.
The block identity is therefore algebraic and must not be supplied as a new
analytic hypothesis.

The only additional datum needed for Schur elimination is a continuous linear
equivalence whose forward map is the automatically extracted complementary
block `D`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteModeCanonicalSchurDecomposition4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteModeContinuousSchurBlock4D

variable {E Mode Complement : Type*}
  [NormedAddCommGroup E] [NormedSpace Real E]
  [Fintype Mode] [DecidableEq Mode]
  [NormedAddCommGroup Complement] [NormedSpace Real Complement]

private abbrev FinitePart (Mode : Type*) := Mode → Real
private abbrev SchurProduct (Mode Complement : Type*) := (Mode → Real) × Complement

/-- The full operator in finite/complement coordinates. -/
def finiteModeConjugatedOperator
    (operator : E →L[Real] E)
    (decomposition : E ≃L[Real] SchurProduct Mode Complement) :
    SchurProduct Mode Complement →L[Real] SchurProduct Mode Complement :=
  decomposition.toContinuousLinearMap.comp
    (operator.comp decomposition.symm.toContinuousLinearMap)

/-- Canonical finite-to-finite block `A`. -/
def finiteModeCanonicalBlockA
    (operator : E →L[Real] E)
    (decomposition : E ≃L[Real] SchurProduct Mode Complement) :
    FinitePart Mode →L[Real] FinitePart Mode :=
  (ContinuousLinearMap.fst Real (FinitePart Mode) Complement).comp
    ((finiteModeConjugatedOperator operator decomposition).comp
      (ContinuousLinearMap.inl Real (FinitePart Mode) Complement))

/-- Canonical complement-to-finite block `B`. -/
def finiteModeCanonicalBlockB
    (operator : E →L[Real] E)
    (decomposition : E ≃L[Real] SchurProduct Mode Complement) :
    Complement →L[Real] FinitePart Mode :=
  (ContinuousLinearMap.fst Real (FinitePart Mode) Complement).comp
    ((finiteModeConjugatedOperator operator decomposition).comp
      (ContinuousLinearMap.inr Real (FinitePart Mode) Complement))

/-- Canonical finite-to-complement block `C`. -/
def finiteModeCanonicalBlockC
    (operator : E →L[Real] E)
    (decomposition : E ≃L[Real] SchurProduct Mode Complement) :
    FinitePart Mode →L[Real] Complement :=
  (ContinuousLinearMap.snd Real (FinitePart Mode) Complement).comp
    ((finiteModeConjugatedOperator operator decomposition).comp
      (ContinuousLinearMap.inl Real (FinitePart Mode) Complement))

/-- Canonical complementary block `D`. -/
def finiteModeCanonicalBlockD
    (operator : E →L[Real] E)
    (decomposition : E ≃L[Real] SchurProduct Mode Complement) :
    Complement →L[Real] Complement :=
  (ContinuousLinearMap.snd Real (FinitePart Mode) Complement).comp
    ((finiteModeConjugatedOperator operator decomposition).comp
      (ContinuousLinearMap.inr Real (FinitePart Mode) Complement))

/-- A continuous finite/complement decomposition for which the automatically
extracted complementary block is invertible. -/
structure FiniteModeCanonicalSchurDecompositionData
    (operator : E →L[Real] E) where
  decomposition : E ≃L[Real] SchurProduct Mode Complement
  complementEquiv : Complement ≃L[Real] Complement
  complementEquiv_eq :
    complementEquiv.toContinuousLinearMap =
      finiteModeCanonicalBlockD operator decomposition

/-- The canonical decomposition constructs the complete bounded four-block
Schur packet. -/
def FiniteModeCanonicalSchurDecompositionData.toContinuousSchurBlockData
    {operator : E →L[Real] E}
    (data : FiniteModeCanonicalSchurDecompositionData
      (Mode := Mode) (Complement := Complement) operator) :
    FiniteModeContinuousSchurBlockData operator Mode Complement where
  decomposition := data.decomposition
  finiteBlock := finiteModeCanonicalBlockA operator data.decomposition
  upperRight := finiteModeCanonicalBlockB operator data.decomposition
  lowerLeft := finiteModeCanonicalBlockC operator data.decomposition
  complementEquiv := data.complementEquiv
  operator_block := by
    intro state
    have hComplement : data.complementEquiv state.2 =
        finiteModeCanonicalBlockD operator data.decomposition state.2 := by
      change data.complementEquiv.toContinuousLinearMap state.2 = _
      rw [data.complementEquiv_eq]
    rw [hComplement]
    change finiteModeConjugatedOperator operator data.decomposition state = _
    have hSplit : state =
        ContinuousLinearMap.inl Real (FinitePart Mode) Complement state.1 +
          ContinuousLinearMap.inr Real (FinitePart Mode) Complement state.2 := by
      apply Prod.ext <;> simp
    conv_lhs => rw [hSplit, map_add]
    rfl

/-- Exact block formula, now a theorem rather than an input field. -/
theorem finiteModeCanonicalSchur_operator_block
    {operator : E →L[Real] E}
    (data : FiniteModeCanonicalSchurDecompositionData
      (Mode := Mode) (Complement := Complement) operator)
    (state : SchurProduct Mode Complement) :
    data.decomposition (operator (data.decomposition.symm state)) =
      (finiteModeCanonicalBlockA operator data.decomposition state.1 +
          finiteModeCanonicalBlockB operator data.decomposition state.2,
        finiteModeCanonicalBlockC operator data.decomposition state.1 +
          data.complementEquiv state.2) :=
  data.toContinuousSchurBlockData.operator_block state

/-- Public checkpoint: one decomposition and invertibility of its canonical
complementary block generate all four bounded Schur blocks. -/
theorem finite_mode_canonical_schur_decomposition_gate
    (operator : E →L[Real] E)
    (data : FiniteModeCanonicalSchurDecompositionData
      (Mode := Mode) (Complement := Complement) operator) :
    Nonempty (FiniteModeContinuousSchurBlockData operator Mode Complement) ∧
      (∀ state,
        data.decomposition (operator (data.decomposition.symm state)) =
          (finiteModeCanonicalBlockA operator data.decomposition state.1 +
              finiteModeCanonicalBlockB operator data.decomposition state.2,
            finiteModeCanonicalBlockC operator data.decomposition state.1 +
              data.complementEquiv state.2)) :=
  ⟨⟨data.toContinuousSchurBlockData⟩,
    finiteModeCanonicalSchur_operator_block data⟩

end
end P0EFTJanusProgramPFiniteModeCanonicalSchurDecomposition4D
end JanusFormal
