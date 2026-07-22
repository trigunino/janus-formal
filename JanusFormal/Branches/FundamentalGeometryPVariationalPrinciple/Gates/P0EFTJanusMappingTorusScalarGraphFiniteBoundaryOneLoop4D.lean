import Mathlib.Analysis.SpecialFunctions.Log.Basic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarLagrangianFiniteSpectralPacket4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusScalarGraphFiniteBoundaryDeterminant4D

/-!
# Finite-dimensional scalar boundary one-loop determinant

For a finite-dimensional trace space, the Schur determinant defines the natural
finite boundary one-loop term

`1/2 log |det(DtN-B)|`.

The term is represented as an `Option Real`: it is undefined exactly at a
boundary crossing, equivalently exactly when a nonzero homogeneous Robin bulk
mode exists.  Basis independence is inherited from `LinearMap.det`; the file
also proves invariance under linear conjugation of boundary coordinates.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusScalarGraphFiniteBoundaryOneLoop4D

set_option autoImplicit false
noncomputable section

open Set Topology Module
open P0EFTJanusMappingTorusScalarHilbertBoundarySymplectic4D
open P0EFTJanusMappingTorusScalarOperatorGraphCompletion4D
open P0EFTJanusMappingTorusScalarGraphPoissonDirichletToNeumann4D
open P0EFTJanusMappingTorusScalarGraphBoundarySpectrumReduction4D
open P0EFTJanusMappingTorusScalarGraphFiniteBoundaryDeterminant4D

universe u v w

variable {Domain : Type u} {Ambient : Type v} {Trace : Type w}
  [AddCommGroup Domain] [Module Real Domain]
  [NormedAddCommGroup Ambient] [InnerProductSpace Real Ambient]
  [CompleteSpace Ambient]
  [NormedAddCommGroup Trace] [InnerProductSpace Real Trace]
  [CompleteSpace Trace]
  [FiniteDimensional Real Trace]

/-- Finite one-loop functional of a boundary endomorphism, undefined at zero
determinant. -/
noncomputable def canonicalScalarFiniteBoundaryOneLoop
    (operator : Trace →ₗ[Real] Trace) : Option Real :=
  if hDet : LinearMap.det operator = 0 then none
  else some ((1 / 2 : Real) * Real.log |LinearMap.det operator|)

/-- The one-loop term is defined exactly for nonzero determinant. -/
theorem canonicalScalarFiniteBoundaryOneLoop_isSome_iff
    (operator : Trace →ₗ[Real] Trace) :
    (canonicalScalarFiniteBoundaryOneLoop operator).isSome ↔
      LinearMap.det operator ≠ 0 := by
  unfold canonicalScalarFiniteBoundaryOneLoop
  split_ifs with hDet
  · simp [hDet]
  · simp [hDet]

/-- The one-loop term is undefined exactly at nontrivial kernel. -/
theorem canonicalScalarFiniteBoundaryOneLoop_eq_none_iff
    (operator : Trace →ₗ[Real] Trace) :
    canonicalScalarFiniteBoundaryOneLoop operator = none ↔
      LinearMap.ker operator ≠ ⊥ := by
  unfold canonicalScalarFiniteBoundaryOneLoop
  split_ifs with hDet
  · simp [hDet, LinearMap.det_eq_zero_iff_ker_ne_bot.mp hDet]
  · have hKer : LinearMap.ker operator = ⊥ := by
      by_contra hNe
      exact hDet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hNe)
    simp [hDet, hKer]

/-- Boundary Schur one-loop term. -/
noncomputable def canonicalScalarGraphBoundarySchurOneLoop
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) : Option Real :=
  canonicalScalarFiniteBoundaryOneLoop
    (canonicalScalarGraphBoundarySchurOperator
      data traceBound spectralParameter poissonData robin).toLinearMap

/-- Schur one-loop singularity is exactly existence of a nonzero Robin bulk
mode. -/
theorem canonicalScalarGraphBoundarySchurOneLoop_eq_none_iff_bulkMode
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) :
    canonicalScalarGraphBoundarySchurOneLoop
        data traceBound spectralParameter poissonData robin = none ↔
      ∃ field : canonicalScalarGraphRobinHomogeneousSolutionSubmodule
        data traceBound spectralParameter robin, field ≠ 0 := by
  unfold canonicalScalarGraphBoundarySchurOneLoop
  rw [canonicalScalarFiniteBoundaryOneLoop_eq_none_iff,
    ← canonicalScalarGraphBoundarySchurDeterminant_eq_zero_iff_bulkMode]
  exact LinearMap.det_eq_zero_iff_ker_ne_bot.symm

/-- One-loop value at a regular Schur point. -/
theorem canonicalScalarGraphBoundarySchurOneLoop_eq_some
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace)
    (hRegular : canonicalScalarGraphBoundarySchurDeterminant
      data traceBound spectralParameter poissonData robin ≠ 0) :
    canonicalScalarGraphBoundarySchurOneLoop
        data traceBound spectralParameter poissonData robin =
      some ((1 / 2 : Real) * Real.log
        |canonicalScalarGraphBoundarySchurDeterminant
          data traceBound spectralParameter poissonData robin|) := by
  unfold canonicalScalarGraphBoundarySchurOneLoop
    canonicalScalarFiniteBoundaryOneLoop
    canonicalScalarGraphBoundarySchurDeterminant
  split_ifs with hDet
  · exact False.elim (hRegular hDet)
  · rfl

/-- Conjugation of a boundary endomorphism. -/
def canonicalScalarFiniteBoundaryConjugate
    (equiv : Trace ≃ₗ[Real] Trace)
    (operator : Trace →ₗ[Real] Trace) : Trace →ₗ[Real] Trace :=
  equiv.toLinearMap.comp (operator.comp equiv.symm.toLinearMap)

/-- Determinant is invariant under boundary-coordinate conjugation. -/
theorem canonicalScalarFiniteBoundaryConjugate_det
    (equiv : Trace ≃ₗ[Real] Trace)
    (operator : Trace →ₗ[Real] Trace) :
    LinearMap.det (canonicalScalarFiniteBoundaryConjugate equiv operator) =
      LinearMap.det operator := by
  simpa [canonicalScalarFiniteBoundaryConjugate,
    LinearMap.comp_assoc] using LinearMap.det_conj operator equiv

/-- Finite one-loop term is invariant under boundary-coordinate conjugation. -/
theorem canonicalScalarFiniteBoundaryOneLoop_conjugate
    (equiv : Trace ≃ₗ[Real] Trace)
    (operator : Trace →ₗ[Real] Trace) :
    canonicalScalarFiniteBoundaryOneLoop
        (canonicalScalarFiniteBoundaryConjugate equiv operator) =
      canonicalScalarFiniteBoundaryOneLoop operator := by
  unfold canonicalScalarFiniteBoundaryOneLoop
  rw [canonicalScalarFiniteBoundaryConjugate_det]

/-- Finite one-loop determinant certificate. -/
theorem canonicalScalarGraphFiniteBoundaryOneLoop_certificate
    (data : CanonicalScalarHilbertGreenSystem
      (Domain := Domain) (Ambient := Ambient) (Trace := Trace))
    (traceBound : HasCanonicalScalarHilbertBoundaryGraphBound data)
    (spectralParameter : Real)
    (poissonData : CanonicalScalarGraphDirichletPoissonData
      data traceBound spectralParameter)
    (robin : Trace →L[Real] Trace) :
    (canonicalScalarGraphBoundarySchurOneLoop
        data traceBound spectralParameter poissonData robin = none ↔
      ∃ field : canonicalScalarGraphRobinHomogeneousSolutionSubmodule
        data traceBound spectralParameter robin, field ≠ 0) ∧
      ((canonicalScalarGraphBoundarySchurOneLoop
        data traceBound spectralParameter poissonData robin).isSome ↔
        canonicalScalarGraphBoundarySchurDeterminant
          data traceBound spectralParameter poissonData robin ≠ 0) := by
  constructor
  · exact canonicalScalarGraphBoundarySchurOneLoop_eq_none_iff_bulkMode
      data traceBound spectralParameter poissonData robin
  · unfold canonicalScalarGraphBoundarySchurOneLoop
      canonicalScalarGraphBoundarySchurDeterminant
    exact canonicalScalarFiniteBoundaryOneLoop_isSome_iff _

end
end P0EFTJanusMappingTorusScalarGraphFiniteBoundaryOneLoop4D
end JanusFormal
