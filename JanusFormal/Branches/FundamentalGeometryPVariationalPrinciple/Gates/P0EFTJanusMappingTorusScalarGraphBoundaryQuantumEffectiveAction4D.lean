import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphBoundaryFredholmDeterminant4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphBoundaryCoerciveAction4D

/-!
# One-loop effective scalar boundary action

For a fixed spectral parameter and background linearized operator, the
regularized Fredholm determinant is independent of the boundary source variable.
The one-loop effective boundary action is therefore

`S_eff(g) = S_classical(g) + hbar S_1loop`.

It is defined exactly away from nonzero Robin bulk modes.  Wherever it is
defined, its first variation with respect to `g` is exactly the classical Schur
variation, so stationary points remain the Schur solutions.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphBoundaryQuantumEffectiveAction4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D
open P0EFTJanusMappingTorusScalarGraphBoundaryTripleFamily4D
open P0EFTJanusMappingTorusScalarGraphBoundarySpectrumReduction4D
open P0EFTJanusMappingTorusScalarGraphBoundaryReducedAction4D
open P0EFTJanusMappingTorusScalarGraphBoundaryCoerciveAction4D
open P0EFTJanusMappingTorusScalarGraphBoundaryFredholmDeterminant4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- One-loop effective reduced boundary action. -/
noncomputable def canonicalScalarGraphBoundaryQuantumEffectiveAction
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (parameters : Set Real)
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (robin : Trace →L[Real] Trace)
    (determinantData : CanonicalScalarGraphBoundaryFredholmDeterminantData
      data traceBound parameters family robin)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters)
    (quantumWeight : Real) (boundary : Trace) : Option Real :=
  match determinantData.oneLoop spectralParameter hParameter with
  | none => none
  | some oneLoop =>
      some (canonicalScalarGraphRobinReducedAction
        data traceBound spectralParameter
          (family.poissonData spectralParameter hParameter) robin boundary +
        quantumWeight * oneLoop)

/-- The effective action is defined exactly at Fredholm-regular parameters. -/
theorem canonicalScalarGraphBoundaryQuantumEffectiveAction_isSome_iff
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (parameters : Set Real)
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (robin : Trace →L[Real] Trace)
    (determinantData : CanonicalScalarGraphBoundaryFredholmDeterminantData
      data traceBound parameters family robin)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters)
    (quantumWeight : Real) (boundary : Trace) :
    (canonicalScalarGraphBoundaryQuantumEffectiveAction
      data traceBound parameters family robin determinantData
        spectralParameter hParameter quantumWeight boundary).isSome ↔
      determinantData.Regular spectralParameter hParameter := by
  unfold canonicalScalarGraphBoundaryQuantumEffectiveAction
  cases hLoop : determinantData.oneLoop spectralParameter hParameter with
  | none =>
      have hNotRegular : ¬ determinantData.Regular spectralParameter hParameter := by
        intro hRegular
        have hSome := determinantData.oneLoop_isSome_iff
          spectralParameter hParameter |>.2 hRegular
        rw [hLoop] at hSome
        simp at hSome
      simp [hLoop, hNotRegular]
  | some value =>
      have hRegular : determinantData.Regular spectralParameter hParameter :=
        (determinantData.oneLoop_isSome_iff
          spectralParameter hParameter).1 (by simp [hLoop])
      simp [hLoop, hRegular]

/-- The effective action is undefined exactly when a nonzero Robin bulk mode
appears. -/
theorem canonicalScalarGraphBoundaryQuantumEffectiveAction_eq_none_iff_bulkMode
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (parameters : Set Real)
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (robin : Trace →L[Real] Trace)
    (determinantData : CanonicalScalarGraphBoundaryFredholmDeterminantData
      data traceBound parameters family robin)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters)
    (quantumWeight : Real) (boundary : Trace) :
    canonicalScalarGraphBoundaryQuantumEffectiveAction
        data traceBound parameters family robin determinantData
          spectralParameter hParameter quantumWeight boundary = none ↔
      ∃ field : canonicalScalarGraphRobinHomogeneousSolutionSubmodule
        data traceBound spectralParameter robin, field ≠ 0 := by
  unfold canonicalScalarGraphBoundaryQuantumEffectiveAction
  cases hLoop : determinantData.oneLoop spectralParameter hParameter with
  | none =>
      have hMode := (determinantData.oneLoop_eq_none_iff_bulkMode
        spectralParameter hParameter).1 hLoop
      simp [hLoop, hMode]
  | some value =>
      have hNoMode : ¬ ∃ field : canonicalScalarGraphRobinHomogeneousSolutionSubmodule
          data traceBound spectralParameter robin, field ≠ 0 := by
        intro hMode
        have hNone := (determinantData.oneLoop_eq_none_iff_bulkMode
          spectralParameter hParameter).2 hMode
        rw [hLoop] at hNone
        simp at hNone
      simp [hLoop, hNoMode]

/-- Value of the effective action at a regular parameter. -/
theorem canonicalScalarGraphBoundaryQuantumEffectiveAction_eq_some
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (parameters : Set Real)
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (robin : Trace →L[Real] Trace)
    (determinantData : CanonicalScalarGraphBoundaryFredholmDeterminantData
      data traceBound parameters family robin)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters)
    (quantumWeight : Real) (boundary : Trace)
    (hRegular : determinantData.Regular spectralParameter hParameter) :
    canonicalScalarGraphBoundaryQuantumEffectiveAction
        data traceBound parameters family robin determinantData
          spectralParameter hParameter quantumWeight boundary =
      some (canonicalScalarGraphRobinReducedAction
        data traceBound spectralParameter
          (family.poissonData spectralParameter hParameter) robin boundary +
        quantumWeight *
          ((1 / 2 : Real) * Real.log
            |determinantData.determinant spectralParameter hParameter|)) := by
  unfold canonicalScalarGraphBoundaryQuantumEffectiveAction
  rw [determinantData.oneLoop_eq_some
    spectralParameter hParameter hRegular]

/-- Classical limit at zero quantum weight. -/
theorem canonicalScalarGraphBoundaryQuantumEffectiveAction_zero_weight
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (parameters : Set Real)
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (robin : Trace →L[Real] Trace)
    (determinantData : CanonicalScalarGraphBoundaryFredholmDeterminantData
      data traceBound parameters family robin)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters)
    (boundary : Trace)
    (hRegular : determinantData.Regular spectralParameter hParameter) :
    canonicalScalarGraphBoundaryQuantumEffectiveAction
        data traceBound parameters family robin determinantData
          spectralParameter hParameter 0 boundary =
      some (canonicalScalarGraphRobinReducedAction
        data traceBound spectralParameter
          (family.poissonData spectralParameter hParameter) robin boundary) := by
  rw [canonicalScalarGraphBoundaryQuantumEffectiveAction_eq_some
    data traceBound parameters family robin determinantData
      spectralParameter hParameter 0 boundary hRegular]
  simp

/-- At a regular parameter, the boundary derivative of the effective action is
exactly the classical Schur derivative. -/
theorem canonicalScalarGraphBoundaryQuantumEffectiveAction_hasDerivAt
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (parameters : Set Real)
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (robin : Trace →L[Real] Trace)
    (hRobin : robin.toLinearMap.IsSymmetric)
    (determinantData : CanonicalScalarGraphBoundaryFredholmDeterminantData
      data traceBound parameters family robin)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters)
    (quantumWeight : Real) (boundary variation : Trace)
    (hRegular : determinantData.Regular spectralParameter hParameter) :
    HasDerivAt
      (fun parameter : Real =>
        (canonicalScalarGraphBoundaryQuantumEffectiveAction
          data traceBound parameters family robin determinantData
            spectralParameter hParameter quantumWeight
            (boundary + parameter • variation)).get
          (by
            rw [canonicalScalarGraphBoundaryQuantumEffectiveAction_isSome_iff]
            exact hRegular))
      (inner Real variation
        (canonicalScalarGraphBoundarySchurOperator
          data traceBound spectralParameter
            (family.poissonData spectralParameter hParameter) robin boundary)) 0 := by
  have hLoop := determinantData.oneLoop_eq_some
    spectralParameter hParameter hRegular
  unfold canonicalScalarGraphBoundaryQuantumEffectiveAction
  simp only [hLoop, Option.get_some]
  simpa using canonicalScalarGraphRobinReducedAction_hasDerivAt
    data traceBound spectralParameter
      (family.poissonData spectralParameter hParameter)
      robin hRobin boundary variation

/-- Quantum effective-action certificate. -/
theorem canonicalScalarGraphBoundaryQuantumEffectiveAction_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (parameters : Set Real)
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (robin : Trace →L[Real] Trace)
    (determinantData : CanonicalScalarGraphBoundaryFredholmDeterminantData
      data traceBound parameters family robin)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters)
    (quantumWeight : Real) (boundary : Trace) :
    ((canonicalScalarGraphBoundaryQuantumEffectiveAction
      data traceBound parameters family robin determinantData
        spectralParameter hParameter quantumWeight boundary).isSome ↔
      determinantData.Regular spectralParameter hParameter) ∧
    (canonicalScalarGraphBoundaryQuantumEffectiveAction
        data traceBound parameters family robin determinantData
          spectralParameter hParameter quantumWeight boundary = none ↔
      ∃ field : canonicalScalarGraphRobinHomogeneousSolutionSubmodule
        data traceBound spectralParameter robin, field ≠ 0) :=
  ⟨canonicalScalarGraphBoundaryQuantumEffectiveAction_isSome_iff
      data traceBound parameters family robin determinantData
        spectralParameter hParameter quantumWeight boundary,
    canonicalScalarGraphBoundaryQuantumEffectiveAction_eq_none_iff_bulkMode
      data traceBound parameters family robin determinantData
        spectralParameter hParameter quantumWeight boundary⟩

end
end P0EFTJanusMappingTorusScalarGraphBoundaryQuantumEffectiveAction4D
end JanusFormal
