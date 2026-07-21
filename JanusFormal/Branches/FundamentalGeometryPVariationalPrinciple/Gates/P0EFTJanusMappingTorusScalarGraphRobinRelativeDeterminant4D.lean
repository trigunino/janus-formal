import Mathlib.Analysis.SpecialFunctions.Log.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphRobinResolventComparison4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphBoundaryFredholmDeterminant4D

/-!
# Relative determinants for scalar Robin boundary conditions

Absolute infinite-dimensional determinants require a normalization.  Relative
determinants between two Robin boundary conditions are more canonical.  This
file records the exact interface:

* the relative determinant is nonzero wherever both endpoints are regular;
* inversion exchanges the endpoints;
* composition satisfies the determinant cocycle;
* the relative one-loop action is one half the logarithm of its absolute value.

The analytic construction may later be supplied by a Fredholm determinant of
the relative Krein factor or by a spectral-shift function.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphRobinRelativeDeterminant4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphBoundaryTripleFamily4D
open P0EFTJanusMappingTorusScalarGraphBoundaryFredholmDeterminant4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

/-- A Robin boundary condition equipped with an absolute Fredholm determinant
normalization. -/
structure CanonicalScalarGraphRobinDeterminantRealization
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (parameters : Set Real)
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters) where
  robin : Trace →L[Real] Trace
  determinant : CanonicalScalarGraphBoundaryFredholmDeterminantData
    data traceBound parameters family robin

/-- Relative determinant system for a collection of Robin realizations. -/
structure CanonicalScalarGraphRobinRelativeDeterminantSystem
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (parameters : Set Real)
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (Index : Type*) where
  realization : Index → CanonicalScalarGraphRobinDeterminantRealization
    data traceBound parameters family
  relativeDeterminant : Index → Index →
    ∀ spectralParameter : Real,
      spectralParameter ∈ parameters → Real
  identity : ∀ index spectralParameter hParameter,
    relativeDeterminant index index spectralParameter hParameter = 1
  inverse : ∀ first second spectralParameter hParameter,
    relativeDeterminant first second spectralParameter hParameter *
      relativeDeterminant second first spectralParameter hParameter = 1
  cocycle : ∀ first second third spectralParameter hParameter,
    relativeDeterminant first second spectralParameter hParameter *
      relativeDeterminant second third spectralParameter hParameter =
        relativeDeterminant first third spectralParameter hParameter
  nonzero_of_regular : ∀ first second spectralParameter hParameter,
    (realization first).determinant.Regular spectralParameter hParameter →
    (realization second).determinant.Regular spectralParameter hParameter →
      relativeDeterminant first second spectralParameter hParameter ≠ 0
  agrees_with_absolute : ∀ first second spectralParameter hParameter,
    relativeDeterminant first second spectralParameter hParameter *
      (realization second).determinant.determinant
        spectralParameter hParameter =
      (realization first).determinant.determinant
        spectralParameter hParameter

namespace CanonicalScalarGraphRobinRelativeDeterminantSystem

/-- Relative one-loop action, defined when the relative determinant is nonzero. -/
noncomputable def relativeOneLoop
    (system : CanonicalScalarGraphRobinRelativeDeterminantSystem
      data traceBound parameters family Index)
    (first second : Index)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    Option Real :=
  if hNonzero : system.relativeDeterminant first second
      spectralParameter hParameter ≠ 0 then
    some ((1 / 2 : Real) * Real.log
      |system.relativeDeterminant first second spectralParameter hParameter|)
  else none

/-- Relative one-loop vanishes on the identity pair. -/
theorem relativeOneLoop_self
    (system : CanonicalScalarGraphRobinRelativeDeterminantSystem
      data traceBound parameters family Index)
    (index : Index)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    system.relativeOneLoop index index spectralParameter hParameter = some 0 := by
  unfold relativeOneLoop
  rw [system.identity]
  simp

/-- Relative determinant is nonzero whenever both absolute realizations are
regular. -/
theorem relativeDeterminant_ne_zero_of_regular
    (system : CanonicalScalarGraphRobinRelativeDeterminantSystem
      data traceBound parameters family Index)
    (first second : Index)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters)
    (hFirst : (system.realization first).determinant.Regular
      spectralParameter hParameter)
    (hSecond : (system.realization second).determinant.Regular
      spectralParameter hParameter) :
    system.relativeDeterminant first second spectralParameter hParameter ≠ 0 :=
  system.nonzero_of_regular first second spectralParameter hParameter hFirst hSecond

/-- Relative one-loop is defined on the common regular set. -/
theorem relativeOneLoop_isSome_of_regular
    (system : CanonicalScalarGraphRobinRelativeDeterminantSystem
      data traceBound parameters family Index)
    (first second : Index)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters)
    (hFirst : (system.realization first).determinant.Regular
      spectralParameter hParameter)
    (hSecond : (system.realization second).determinant.Regular
      spectralParameter hParameter) :
    (system.relativeOneLoop first second spectralParameter hParameter).isSome := by
  unfold relativeOneLoop
  simp [system.relativeDeterminant_ne_zero_of_regular
    first second spectralParameter hParameter hFirst hSecond]

/-- On the common regular set, the relative one-loop action is the difference of
absolute one-loop actions. -/
theorem relativeOneLoop_eq_absolute_difference
    (system : CanonicalScalarGraphRobinRelativeDeterminantSystem
      data traceBound parameters family Index)
    (first second : Index)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters)
    (hFirst : (system.realization first).determinant.Regular
      spectralParameter hParameter)
    (hSecond : (system.realization second).determinant.Regular
      spectralParameter hParameter) :
    (system.relativeOneLoop first second spectralParameter hParameter).get
        (system.relativeOneLoop_isSome_of_regular
          first second spectralParameter hParameter hFirst hSecond) =
      ((system.realization first).determinant.oneLoop
          spectralParameter hParameter).get
          ((system.realization first).determinant.oneLoop_isSome_iff
            spectralParameter hParameter |>.2 hFirst) -
        ((system.realization second).determinant.oneLoop
          spectralParameter hParameter).get
          ((system.realization second).determinant.oneLoop_isSome_iff
            spectralParameter hParameter |>.2 hSecond) := by
  unfold relativeOneLoop
  rw [dif_pos (system.relativeDeterminant_ne_zero_of_regular
    first second spectralParameter hParameter hFirst hSecond)]
  rw [(system.realization first).determinant.oneLoop_eq_some
      spectralParameter hParameter hFirst,
    (system.realization second).determinant.oneLoop_eq_some
      spectralParameter hParameter hSecond]
  simp only [Option.get_some]
  have hAgreement := system.agrees_with_absolute
    first second spectralParameter hParameter
  have hRelativePositive :
      0 < |system.relativeDeterminant first second spectralParameter hParameter| :=
    abs_pos.mpr (system.relativeDeterminant_ne_zero_of_regular
      first second spectralParameter hParameter hFirst hSecond)
  have hSecondPositive :
      0 < |(system.realization second).determinant.determinant
        spectralParameter hParameter| := abs_pos.mpr hSecond
  have hAbs :
      |system.relativeDeterminant first second spectralParameter hParameter| *
          |(system.realization second).determinant.determinant
            spectralParameter hParameter| =
        |(system.realization first).determinant.determinant
          spectralParameter hParameter| := by
    rw [← abs_mul, hAgreement]
  rw [← hAbs, Real.log_mul hRelativePositive.ne' hSecondPositive.ne']
  ring

/-- Relative determinant cocycle certificate. -/
theorem certificate
    (system : CanonicalScalarGraphRobinRelativeDeterminantSystem
      data traceBound parameters family Index) :
    (∀ index spectralParameter hParameter,
      system.relativeDeterminant index index spectralParameter hParameter = 1) ∧
      (∀ first second third spectralParameter hParameter,
        system.relativeDeterminant first second spectralParameter hParameter *
          system.relativeDeterminant second third spectralParameter hParameter =
        system.relativeDeterminant first third spectralParameter hParameter) :=
  ⟨system.identity, system.cocycle⟩

end CanonicalScalarGraphRobinRelativeDeterminantSystem

end
end P0EFTJanusMappingTorusScalarGraphRobinRelativeDeterminant4D
end JanusFormal
