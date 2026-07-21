import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianSpectralZeta4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianVariationalEigenprinciple4D

/-!
# Courant--Fischer min--max interface

For a semibounded compact-resolvent scalar realization, the ordered eigenvalues
should be characterized by the Rayleigh quotient on finite-dimensional trial
subspaces.  The analytic proof requires compactness of the relevant form-domain
embedding and attainment of the extrema.

This file defines the exact min--max quantities and packages the theorem that
identifies them with a positive spectral enumeration.  It then exposes the
ground-state and monotonicity consequences used by variational estimates.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarLagrangianCourantFischer4D

set_option autoImplicit false
noncomputable section

open Set Topology Module
open scoped Topology BigOperators
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarClosedGraphRealization4D
open P0EFTJanusMappingTorusScalarAbstractLagrangianBoundary4D
open P0EFTJanusMappingTorusScalarLagrangianAnalyticClosure4D
open P0EFTJanusMappingTorusScalarLagrangianVariationalEigenprinciple4D
open P0EFTJanusMappingTorusScalarLagrangianSpectralZeta4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]

private abbrev LagrangianDomain
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace) :=
  canonicalScalarClosedLagrangianDomainSubmodule
    data hClosable traceBound condition

/-- Nonzero vectors of one trial subspace. -/
def canonicalScalarTrialSubspaceNonzero
    (trial : Submodule Real
      (LagrangianDomain data hClosable traceBound condition)) :
    Set (LagrangianDomain data hClosable traceBound condition) :=
  {field | field ∈ trial ∧ field ≠ 0}

/-- Set of Rayleigh values attained by nonzero vectors of a trial subspace. -/
def canonicalScalarTrialSubspaceRayleighSet
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (trial : Submodule Real
      (LagrangianDomain data hClosable traceBound condition)) : Set Real :=
  canonicalScalarClosedLagrangianRayleighQuotient
      data hClosable traceBound condition ''
    canonicalScalarTrialSubspaceNonzero trial

/-- Supremal Rayleigh quotient on one trial subspace. -/
noncomputable def canonicalScalarTrialSubspaceRayleighSup
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (trial : Submodule Real
      (LagrangianDomain data hClosable traceBound condition)) : Real :=
  sSup (canonicalScalarTrialSubspaceRayleighSet
    data hClosable traceBound condition trial)

/-- Finite-dimensional trial spaces of dimension `index+1`. -/
def canonicalScalarCourantFischerTrialSpaces
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (index : Nat) : Set
      (Submodule Real (LagrangianDomain data hClosable traceBound condition)) :=
  {trial | Module.finrank Real trial = index + 1}

/-- Courant--Fischer min--max value. -/
noncomputable def canonicalScalarCourantFischerValue
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (index : Nat) : Real :=
  sInf (canonicalScalarTrialSubspaceRayleighSup
      data hClosable traceBound condition ''
    canonicalScalarCourantFischerTrialSpaces
      data hClosable traceBound condition index)

/-- Analytic Courant--Fischer theorem for a chosen spectral enumeration. -/
structure CanonicalScalarCourantFischerData
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (hClosable : CanonicalScalarGraphClosable data)
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (condition : CanonicalScalarHilbertLagrangianBoundaryCondition Trace)
    (closureData : CanonicalScalarLagrangianAnalyticClosureData
      data hClosable traceBound condition)
    (enumeration : CanonicalScalarPositiveSpectrumEnumeration
      data hClosable traceBound condition closureData) where
  trialSpaces_nonempty : ∀ index,
    (canonicalScalarCourantFischerTrialSpaces
      data hClosable traceBound condition index).Nonempty
  rayleigh_bddAbove : ∀ trial,
    BddAbove (canonicalScalarTrialSubspaceRayleighSet
      data hClosable traceBound condition trial)
  minmax_bddBelow : ∀ index,
    BddBelow (canonicalScalarTrialSubspaceRayleighSup
        data hClosable traceBound condition ''
      canonicalScalarCourantFischerTrialSpaces
        data hClosable traceBound condition index)
  eigenvalue_eq_minmax : ∀ index,
    enumeration.eigenvalue index =
      canonicalScalarCourantFischerValue
        data hClosable traceBound condition index
  minimizingSubspace : Nat →
    Submodule Real (LagrangianDomain data hClosable traceBound condition)
  minimizingSubspace_finrank : ∀ index,
    Module.finrank Real (minimizingSubspace index) = index + 1
  minimizingSubspace_attains : ∀ index,
    canonicalScalarTrialSubspaceRayleighSup
        data hClosable traceBound condition (minimizingSubspace index) =
      enumeration.eigenvalue index

namespace CanonicalScalarCourantFischerData

/-- Min--max values inherit monotonicity from the ordered eigenvalue enumeration. -/
theorem minmax_monotone
    (minmax : CanonicalScalarCourantFischerData
      data hClosable traceBound condition closureData enumeration) :
    Monotone (canonicalScalarCourantFischerValue
      data hClosable traceBound condition) := by
  intro first second hIndex
  rw [← minmax.eigenvalue_eq_minmax,
    ← minmax.eigenvalue_eq_minmax]
  exact enumeration.monotone hIndex

/-- Ground-state value is the first Courant--Fischer minimum. -/
theorem groundState_eq
    (minmax : CanonicalScalarCourantFischerData
      data hClosable traceBound condition closureData enumeration) :
    enumeration.eigenvalue 0 =
      canonicalScalarCourantFischerValue
        data hClosable traceBound condition 0 :=
  minmax.eigenvalue_eq_minmax 0

/-- Every later eigenvalue is bounded below by the ground state. -/
theorem groundState_le
    (minmax : CanonicalScalarCourantFischerData
      data hClosable traceBound condition closureData enumeration)
    (index : Nat) :
    enumeration.eigenvalue 0 ≤ enumeration.eigenvalue index :=
  enumeration.monotone (Nat.zero_le index)

/-- Every concrete trial subspace gives an upper bound on the corresponding
min--max eigenvalue, provided the defining infimum comparison is available. -/
theorem eigenvalue_le_trialSup
    (minmax : CanonicalScalarCourantFischerData
      data hClosable traceBound condition closureData enumeration)
    (index : Nat)
    (trial : Submodule Real
      (LagrangianDomain data hClosable traceBound condition))
    (hTrial : Module.finrank Real trial = index + 1)
    (hLower : BddBelow
      (canonicalScalarTrialSubspaceRayleighSup
          data hClosable traceBound condition ''
        canonicalScalarCourantFischerTrialSpaces
          data hClosable traceBound condition index)) :
    enumeration.eigenvalue index ≤
      canonicalScalarTrialSubspaceRayleighSup
        data hClosable traceBound condition trial := by
  rw [minmax.eigenvalue_eq_minmax]
  unfold canonicalScalarCourantFischerValue
  apply csInf_le hLower
  exact ⟨trial, hTrial, rfl⟩

/-- Courant--Fischer certificate. -/
theorem certificate
    (minmax : CanonicalScalarCourantFischerData
      data hClosable traceBound condition closureData enumeration) :
    (∀ index,
      enumeration.eigenvalue index =
        canonicalScalarCourantFischerValue
          data hClosable traceBound condition index) ∧
      Monotone (canonicalScalarCourantFischerValue
        data hClosable traceBound condition) ∧
      (∀ index,
        Module.finrank Real (minmax.minimizingSubspace index) = index + 1 ∧
        canonicalScalarTrialSubspaceRayleighSup
            data hClosable traceBound condition
              (minmax.minimizingSubspace index) =
          enumeration.eigenvalue index) :=
  ⟨minmax.eigenvalue_eq_minmax,
    minmax.minmax_monotone,
    fun index => ⟨minmax.minimizingSubspace_finrank index,
      minmax.minimizingSubspace_attains index⟩⟩

end CanonicalScalarCourantFischerData

end
end P0EFTJanusMappingTorusScalarLagrangianCourantFischer4D
end JanusFormal
