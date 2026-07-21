import Mathlib.LinearAlgebra.Determinant
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphBoundaryTripleFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphBoundarySpectrumReduction4D

/-!
# Finite-dimensional boundary determinant criterion

When the Hilbert trace space is finite-dimensional, the Robin boundary Schur
operator has a basis-independent determinant.  Its vanishing is exactly the
existence of nonzero boundary Schur-kernel data and therefore exactly the
existence of a nonzero homogeneous Robin bulk mode.

This gives a rigorous finite-boundary Evans/determinant function for every
parameter of a scalar boundary-triple family.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphFiniteBoundaryDeterminant4D

set_option autoImplicit false
noncomputable section

open Set Topology Module
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D
open P0EFTJanusMappingTorusScalarGraphBoundarySpectrumReduction4D
open P0EFTJanusMappingTorusScalarGraphBoundaryTripleFamily4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]
  [FiniteDimensional Real Trace]

/-- Basis-independent determinant of one boundary Schur operator. -/
noncomputable def canonicalScalarGraphBoundarySchurDeterminant
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) : Real :=
  LinearMap.det
    (canonicalScalarGraphBoundarySchurOperator
      data traceBound spectralParameter poissonData robin).toLinearMap

/-- Determinant zero is exactly nontrivial Schur kernel. -/
theorem canonicalScalarGraphBoundarySchurDeterminant_eq_zero_iff
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) :
    canonicalScalarGraphBoundarySchurDeterminant
        data traceBound spectralParameter poissonData robin = 0 ↔
      LinearMap.ker
        (canonicalScalarGraphBoundarySchurOperator
          data traceBound spectralParameter poissonData robin).toLinearMap ≠ ⊥ := by
  exact LinearMap.det_eq_zero_iff_ker_ne_bot

/-- Determinant zero is exactly existence of a nonzero boundary vector. -/
theorem canonicalScalarGraphBoundarySchurDeterminant_eq_zero_iff_exists
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) :
    canonicalScalarGraphBoundarySchurDeterminant
        data traceBound spectralParameter poissonData robin = 0 ↔
      ∃ boundary : LinearMap.ker
        (canonicalScalarGraphBoundarySchurOperator
          data traceBound spectralParameter poissonData robin).toLinearMap,
        boundary ≠ 0 := by
  rw [canonicalScalarGraphBoundarySchurDeterminant_eq_zero_iff]
  exact Submodule.ne_bot_iff

/-- Finite-boundary determinant criterion for nonzero homogeneous Robin bulk
modes. -/
theorem canonicalScalarGraphBoundarySchurDeterminant_eq_zero_iff_bulkMode
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) :
    canonicalScalarGraphBoundarySchurDeterminant
        data traceBound spectralParameter poissonData robin = 0 ↔
      ∃ field : canonicalScalarGraphRobinHomogeneousSolutionSubmodule
        data traceBound spectralParameter robin, field ≠ 0 := by
  rw [canonicalScalarGraphBoundarySchurDeterminant_eq_zero_iff_exists]
  exact (canonicalScalarGraphRobin_hasNonzeroSolution_iff_schurKernel
    data traceBound spectralParameter poissonData robin).symm

/-- Nonzero determinant gives trivial Robin homogeneous solution space. -/
theorem canonicalScalarGraphBoundarySchurDeterminant_ne_zero_iff_bulk_trivial
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) :
    canonicalScalarGraphBoundarySchurDeterminant
        data traceBound spectralParameter poissonData robin ≠ 0 ↔
      canonicalScalarGraphRobinHomogeneousSolutionSubmodule
        data traceBound spectralParameter robin = ⊥ := by
  rw [ne_eq, canonicalScalarGraphBoundarySchurDeterminant_eq_zero_iff_bulkMode]
  constructor
  · intro hNoMode
    apply Submodule.eq_bot_iff.mpr
    intro field hField
    by_contra hNonzero
    exact hNoMode ⟨⟨field, hField⟩, by
      intro hZero
      exact hNonzero (congrArg Subtype.val hZero)⟩
  · intro hBot hMode
    rcases hMode with ⟨field, hField⟩
    have hMembership : field.1 ∈
        canonicalScalarGraphRobinHomogeneousSolutionSubmodule
          data traceBound spectralParameter robin := field.2
    rw [hBot] at hMembership
    exact hField (Subsingleton.elim field 0)

/-- Determinant function of a finite-dimensional boundary-triple family. -/
noncomputable def CanonicalScalarGraphBoundaryTripleFamily.schurDeterminant
    {parameters : Set Real}
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (robin : Trace →L[Real] Trace)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) : Real :=
  canonicalScalarGraphBoundarySchurDeterminant
    data traceBound spectralParameter
      (family.poissonData spectralParameter hParameter) robin

/-- Family determinant criterion. -/
theorem CanonicalScalarGraphBoundaryTripleFamily.schurDeterminant_eq_zero_iff_bulkMode
    {parameters : Set Real}
    (family : CanonicalScalarGraphBoundaryTripleFamily
      data traceBound parameters)
    (robin : Trace →L[Real] Trace)
    (spectralParameter : Real) (hParameter : spectralParameter ∈ parameters) :
    family.schurDeterminant robin spectralParameter hParameter = 0 ↔
      ∃ field : canonicalScalarGraphRobinHomogeneousSolutionSubmodule
        data traceBound spectralParameter robin, field ≠ 0 :=
  canonicalScalarGraphBoundarySchurDeterminant_eq_zero_iff_bulkMode
    data traceBound spectralParameter
      (family.poissonData spectralParameter hParameter) robin

/-- Finite-boundary determinant certificate. -/
theorem canonicalScalarGraphFiniteBoundaryDeterminant_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) :
    (canonicalScalarGraphBoundarySchurDeterminant
        data traceBound spectralParameter poissonData robin = 0 ↔
      ∃ boundary : LinearMap.ker
        (canonicalScalarGraphBoundarySchurOperator
          data traceBound spectralParameter poissonData robin).toLinearMap,
        boundary ≠ 0) ∧
    (canonicalScalarGraphBoundarySchurDeterminant
        data traceBound spectralParameter poissonData robin = 0 ↔
      ∃ field : canonicalScalarGraphRobinHomogeneousSolutionSubmodule
        data traceBound spectralParameter robin, field ≠ 0) :=
  ⟨canonicalScalarGraphBoundarySchurDeterminant_eq_zero_iff_exists
      data traceBound spectralParameter poissonData robin,
    canonicalScalarGraphBoundarySchurDeterminant_eq_zero_iff_bulkMode
      data traceBound spectralParameter poissonData robin⟩

end
end P0EFTJanusMappingTorusScalarGraphFiniteBoundaryDeterminant4D
end JanusFormal
