import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceUnitaryConjugation4D

/-!
# Intrinsic nuclear trace across an isometric equivalence

The unitary-conjugation result is extended from one Hilbert space to two
isometrically equivalent real Hilbert spaces.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPIntrinsicNuclearTraceIsometricEquivalenceTransport4D

set_option autoImplicit false
noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
open P0EFTJanusProgramPIntrinsicNuclearTrace4D

universe u w v

variable {E : Type u} {F : Type w}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace Real F] [CompleteSpace F]

/-- Conjugate an operator through an isometric equivalence between two
Hilbert spaces. -/
def isometricEquivalenceConjugatedOperator
    (coordinates : E ≃ₗᵢ[Real] F) (operator : E →L[Real] E) :
    F →L[Real] F :=
  coordinates.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (operator.comp
      coordinates.symm.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem isometricEquivalenceConjugatedOperator_apply
    (coordinates : E ≃ₗᵢ[Real] F) (operator : E →L[Real] E) (vector : F) :
    isometricEquivalenceConjugatedOperator coordinates operator vector =
      coordinates (operator (coordinates.symm vector)) :=
  rfl

@[simp] theorem isometricEquivalenceConjugatedOperator_symm
    (coordinates : E ≃ₗᵢ[Real] F) (operator : E →L[Real] E) :
    isometricEquivalenceConjugatedOperator coordinates.symm
        (isometricEquivalenceConjugatedOperator coordinates operator) =
      operator := by
  ext vector
  simp

/-- Transport a summable rank-one expansion across an isometric equivalence. -/
def isometricEquivalenceTransport
    {operator : E →L[Real] E}
    (data : SummableRankOneOperatorExpansion operator)
    (coordinates : E ≃ₗᵢ[Real] F) :
    SummableRankOneOperatorExpansion
      (isometricEquivalenceConjugatedOperator coordinates operator) where
  Index := data.Index
  coefficient := data.coefficient
  leftVector := fun index => coordinates (data.leftVector index)
  rightVector := fun index => coordinates (data.rightVector index)
  summable_nuclearNorm := by
    simpa using data.summable_nuclearNorm
  trace_summable := by
    simpa using data.trace_summable
  operator_eq_tsum := by
    have hSummable : Summable data.component :=
      Summable.of_norm data.component_norm_summable
    have hOperator : operator = ∑' index, data.component index := by
      simpa [SummableRankOneOperatorExpansion.component] using
        data.operator_eq_tsum
    let rightComposition :
        (E →L[Real] E) →L[Real] (E →L[Real] F) :=
      ContinuousLinearMap.compL Real E E F
        coordinates.toContinuousLinearEquiv.toContinuousLinearMap
    let leftComposition :
        (E →L[Real] F) →L[Real] (F →L[Real] F) :=
      (ContinuousLinearMap.compL Real F E F).flip
        coordinates.symm.toContinuousLinearEquiv.toContinuousLinearMap
    calc
      isometricEquivalenceConjugatedOperator coordinates operator =
          leftComposition (rightComposition operator) := rfl
      _ = leftComposition (rightComposition
          (∑' index, data.component index)) :=
        congrArg (fun current => leftComposition (rightComposition current))
          hOperator
      _ = leftComposition (∑' index, rightComposition (data.component index)) :=
        congrArg leftComposition (rightComposition.map_tsum hSummable)
      _ = ∑' index, leftComposition (rightComposition (data.component index)) :=
        leftComposition.map_tsum
          (hSummable.map rightComposition rightComposition.continuous)
      _ = ∑' index, data.coefficient index •
          InnerProductSpace.rankOne Real (coordinates (data.leftVector index))
            (coordinates (data.rightVector index)) := by
        apply tsum_congr
        intro index
        ext vector
        simp [leftComposition, rightComposition,
          SummableRankOneOperatorExpansion.component,
          InnerProductSpace.rankOne_apply,
          coordinates.inner_map_eq_flip]

@[simp] theorem isometricEquivalenceTransport_expansionTrace
    {operator : E →L[Real] E}
    (data : SummableRankOneOperatorExpansion operator)
    (coordinates : E ≃ₗᵢ[Real] F) :
    (isometricEquivalenceTransport data coordinates).expansionTrace =
      data.expansionTrace := by
  simp [SummableRankOneOperatorExpansion.expansionTrace,
    isometricEquivalenceTransport]

/-- Reindex an expansion along an equality of its represented operators. -/
def transportExpansionOperator
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace Real G]
    {first second : G →L[Real] G}
    (data : SummableRankOneOperatorExpansion first)
    (hOperator : first = second) :
    SummableRankOneOperatorExpansion second := by
  cases hOperator
  exact data

@[simp] theorem transportExpansionOperator_expansionTrace
    {G : Type*} [NormedAddCommGroup G] [InnerProductSpace Real G]
    {first second : G →L[Real] G}
    (data : SummableRankOneOperatorExpansion first)
    (hOperator : first = second) :
    (transportExpansionOperator data hOperator).expansionTrace =
      data.expansionTrace := by
  cases hOperator
  rfl

/-- Construct the complete intrinsic nuclear certificate on the target space
from the source certificate alone. -/
def intrinsicNuclearTraceDataIsometricEquivalenceTransport
    {operator : E →L[Real] E}
    (coordinates : E ≃ₗᵢ[Real] F)
    (source : IntrinsicNuclearTraceData.{u, v} operator) :
    IntrinsicNuclearTraceData.{w, v}
      (isometricEquivalenceConjugatedOperator coordinates operator) where
  expansion := isometricEquivalenceTransport source.expansion coordinates
  presentation_independent := by
    intro other
    let pulledRaw := isometricEquivalenceTransport other coordinates.symm
    let pulled := transportExpansionOperator pulledRaw
      (isometricEquivalenceConjugatedOperator_symm coordinates operator)
    calc
      other.expansionTrace = pulledRaw.expansionTrace :=
        (isometricEquivalenceTransport_expansionTrace other coordinates.symm).symm
      _ = pulled.expansionTrace :=
        (transportExpansionOperator_expansionTrace pulledRaw
          (isometricEquivalenceConjugatedOperator_symm coordinates operator)).symm
      _ = source.expansion.expansionTrace :=
        source.presentation_independent pulled
      _ = (isometricEquivalenceTransport source.expansion coordinates).expansionTrace :=
        (isometricEquivalenceTransport_expansionTrace source.expansion coordinates).symm

@[simp] theorem intrinsicNuclearTraceDataIsometricEquivalenceTransport_trace
    {operator : E →L[Real] E}
    (coordinates : E ≃ₗᵢ[Real] F)
    (source : IntrinsicNuclearTraceData.{u, v} operator) :
    intrinsicNuclearTrace
        (intrinsicNuclearTraceDataIsometricEquivalenceTransport coordinates source) =
      intrinsicNuclearTrace source :=
  isometricEquivalenceTransport_expansionTrace source.expansion coordinates

/-- Intrinsic nuclear trace is invariant under an isometric equivalence of
ambient Hilbert spaces. -/
theorem intrinsicNuclearTrace_isometricEquivalenceTransport
    {operator : E →L[Real] E}
    (coordinates : E ≃ₗᵢ[Real] F)
    (source : IntrinsicNuclearTraceData.{u, v} operator)
    (target : IntrinsicNuclearTraceData.{w, v}
      (isometricEquivalenceConjugatedOperator coordinates operator)) :
    intrinsicNuclearTrace target = intrinsicNuclearTrace source := by
  calc
    intrinsicNuclearTrace target =
        (isometricEquivalenceTransport source.expansion coordinates).expansionTrace :=
      (target.expansionTrace_eq
        (isometricEquivalenceTransport source.expansion coordinates)).symm
    _ = source.expansion.expansionTrace :=
      isometricEquivalenceTransport_expansionTrace source.expansion coordinates
    _ = intrinsicNuclearTrace source := rfl

/-- Public transport checkpoint. -/
theorem intrinsic_nuclear_trace_isometric_equivalence_transport_gate
    {operator : E →L[Real] E}
    (coordinates : E ≃ₗᵢ[Real] F)
    (source : IntrinsicNuclearTraceData.{u, v} operator)
    (target : IntrinsicNuclearTraceData.{w, v}
      (isometricEquivalenceConjugatedOperator coordinates operator)) :
    intrinsicNuclearTrace target = intrinsicNuclearTrace source :=
  intrinsicNuclearTrace_isometricEquivalenceTransport coordinates source target

end
end P0EFTJanusProgramPIntrinsicNuclearTraceIsometricEquivalenceTransport4D
end JanusFormal
