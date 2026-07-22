import Mathlib.Analysis.SpecialFunctions.Log.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphInterfaceGluing4D

/-!
# Finite-dimensional determinant of the scalar gluing operator

For a finite-dimensional common trace space, the determinant of the interface
Schur operator

`M_left + M_right - J`

is the finite gluing determinant.  It vanishes exactly when a nonzero glued
homogeneous bulk pair exists.  Its logarithm defines the finite interface
one-loop contribution away from those modes.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphFiniteInterfaceDeterminant4D

set_option autoImplicit false
noncomputable section

open Set Topology Module
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D
open P0EFTJanusMappingTorusScalarGraphInterfaceGluing4D

universe u₁ u₂ v₁ v₂ w

variable {DomainLeft : Type u₁} {DomainRight : Type u₂}
  {AmbientLeft : Type v₁} {AmbientRight : Type v₂}
  {Trace : Type w}
  [AddCommGroup DomainLeft] [Module Real DomainLeft]
  [AddCommGroup DomainRight] [Module Real DomainRight]
  [NormedAddCommGroup AmbientLeft] [InnerProductSpace Real AmbientLeft]
  [CompleteSpace AmbientLeft]
  [NormedAddCommGroup AmbientRight] [InnerProductSpace Real AmbientRight]
  [CompleteSpace AmbientRight]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]
  [FiniteDimensional Real Trace]

variable
  {left : CanonicalScalarHilbertGreenSystem
    (Domain := DomainLeft) (Ambient := AmbientLeft) (Trace := Trace)}
  {leftTraceBound : HasCanonicalScalarHilbertBoundaryGraphBound left}
  {right : CanonicalScalarHilbertGreenSystem
    (Domain := DomainRight) (Ambient := AmbientRight) (Trace := Trace)}
  {rightTraceBound : HasCanonicalScalarHilbertBoundaryGraphBound right}
  {spectralParameter : Real}

/-- Finite interface gluing determinant. -/
noncomputable def canonicalScalarGraphInterfaceDeterminant
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace) : Real :=
  LinearMap.det (interfaceData.schurOperator junction).toLinearMap

/-- Interface determinant zero iff interface Schur kernel is nontrivial. -/
theorem canonicalScalarGraphInterfaceDeterminant_eq_zero_iff_kernel
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace) :
    canonicalScalarGraphInterfaceDeterminant interfaceData junction = 0 ↔
      LinearMap.ker (interfaceData.schurOperator junction).toLinearMap ≠ ⊥ :=
  LinearMap.det_eq_zero_iff_ker_ne_bot

/-- Interface determinant zero iff a nonzero glued homogeneous bulk pair exists. -/
theorem canonicalScalarGraphInterfaceDeterminant_eq_zero_iff_gluedMode
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace) :
    canonicalScalarGraphInterfaceDeterminant interfaceData junction = 0 ↔
      ∃ field : interfaceData.gluedHomogeneousSolutionSubmodule junction,
        field ≠ 0 := by
  rw [canonicalScalarGraphInterfaceDeterminant_eq_zero_iff_kernel,
    Submodule.ne_bot_iff]
  let equivalence := interfaceData.schurKernelGluedSolutionEquiv junction
  constructor
  · rintro ⟨boundary, hBoundary, hBoundaryNonzero⟩
    let boundarySubtype : LinearMap.ker
        (interfaceData.schurOperator junction).toLinearMap :=
      ⟨boundary, hBoundary⟩
    refine ⟨equivalence boundarySubtype, ?_⟩
    intro hZero
    apply hBoundaryNonzero
    have hSubtypeZero : boundarySubtype = 0 := by
      apply equivalence.injective
      simpa using hZero
    simpa [boundarySubtype] using congrArg Subtype.val hSubtypeZero
  · rintro ⟨field, hField⟩
    refine ⟨(equivalence.symm field : Trace),
      (equivalence.symm field).property, ?_⟩
    intro hBoundaryZero
    apply hField
    apply equivalence.symm.injective
    apply Subtype.ext
    simpa using hBoundaryZero

/-- Finite interface one-loop term, undefined at a gluing mode. -/
noncomputable def canonicalScalarGraphInterfaceOneLoop
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace) : Option Real :=
  if hRegular : canonicalScalarGraphInterfaceDeterminant
      interfaceData junction ≠ 0 then
    some ((1 / 2 : Real) * Real.log
      |canonicalScalarGraphInterfaceDeterminant interfaceData junction|)
  else none

/-- Interface one-loop is defined exactly at an invertible gluing operator. -/
theorem canonicalScalarGraphInterfaceOneLoop_isSome_iff
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace) :
    (canonicalScalarGraphInterfaceOneLoop interfaceData junction).isSome ↔
      canonicalScalarGraphInterfaceDeterminant interfaceData junction ≠ 0 := by
  unfold canonicalScalarGraphInterfaceOneLoop
  split_ifs with hRegular
  · simp [hRegular]
  · simp [hRegular]

/-- Interface one-loop is undefined exactly at a nonzero glued mode. -/
theorem canonicalScalarGraphInterfaceOneLoop_eq_none_iff_gluedMode
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace) :
    canonicalScalarGraphInterfaceOneLoop interfaceData junction = none ↔
      ∃ field : interfaceData.gluedHomogeneousSolutionSubmodule junction,
        field ≠ 0 := by
  unfold canonicalScalarGraphInterfaceOneLoop
  split_ifs with hRegular
  · have hNoMode : ¬ ∃ field : interfaceData.gluedHomogeneousSolutionSubmodule
        junction, field ≠ 0 := by
      intro hMode
      exact hRegular
        ((canonicalScalarGraphInterfaceDeterminant_eq_zero_iff_gluedMode
          interfaceData junction).2 hMode)
    simp [hRegular, hNoMode]
  · have hMode :=
      (canonicalScalarGraphInterfaceDeterminant_eq_zero_iff_gluedMode
        interfaceData junction).1 (not_ne_iff.mp hRegular)
    simp [hRegular, hMode]

/-- Value of the interface one-loop term at a regular point. -/
theorem canonicalScalarGraphInterfaceOneLoop_eq_some
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace)
    (hRegular : canonicalScalarGraphInterfaceDeterminant
      interfaceData junction ≠ 0) :
    canonicalScalarGraphInterfaceOneLoop interfaceData junction =
      some ((1 / 2 : Real) * Real.log
        |canonicalScalarGraphInterfaceDeterminant interfaceData junction|) := by
  simp [canonicalScalarGraphInterfaceOneLoop, hRegular]

/-- Finite gluing determinant certificate. -/
theorem canonicalScalarGraphFiniteInterfaceDeterminant_certificate
    (interfaceData : CanonicalScalarGraphInterfacePoissonData
      left leftTraceBound right rightTraceBound spectralParameter)
    (junction : Trace →L[Real] Trace) :
    (canonicalScalarGraphInterfaceDeterminant interfaceData junction = 0 ↔
      ∃ field : interfaceData.gluedHomogeneousSolutionSubmodule junction,
        field ≠ 0) ∧
      (canonicalScalarGraphInterfaceOneLoop interfaceData junction = none ↔
        ∃ field : interfaceData.gluedHomogeneousSolutionSubmodule junction,
          field ≠ 0) :=
  ⟨canonicalScalarGraphInterfaceDeterminant_eq_zero_iff_gluedMode
      interfaceData junction,
    canonicalScalarGraphInterfaceOneLoop_eq_none_iff_gluedMode
      interfaceData junction⟩

end
end P0EFTJanusMappingTorusScalarGraphFiniteInterfaceDeterminant4D
end JanusFormal
