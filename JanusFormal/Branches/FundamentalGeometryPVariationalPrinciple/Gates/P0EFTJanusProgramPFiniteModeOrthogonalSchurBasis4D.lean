import Mathlib.Topology.Algebra.Module.FiniteDimension
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeOrthogonalSchurDecomposition4D

/-!
# Orthogonal Schur data from a finite physical basis

The continuous coordinate equivalence of the finite mode subspace is not an
independent analytic object.  A basis indexed by the physical label type
`Mode` gives an algebraic equivalence with `Mode → ℝ`; finite-dimensional
continuity upgrades it canonically to a continuous linear equivalence.

This leaves only a genuine finite basis and invertibility of the automatically
extracted orthogonal-complement block.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteModeOrthogonalSchurBasis4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusProgramPFiniteModeOrthogonalSchurDecomposition4D
open P0EFTJanusProgramPFiniteModeCanonicalSchurDecomposition4D
open P0EFTJanusProgramPFiniteModeContinuousSchurBlock4D

variable {E Mode : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype Mode] [DecidableEq Mode]

private abbrev FinitePart := Mode → Real

/-- Continuous coordinates generated from an algebraic basis of a finite
subspace. -/
noncomputable def finiteModeContinuousEquivOfBasis
    (modeSubspace : Submodule Real E)
    (basis : Basis Mode Real modeSubspace) :
    FinitePart ≃L[Real] modeSubspace := by
  letI : FiniteDimensional Real modeSubspace :=
    basis.finiteDimensional_of_finite
  exact basis.equivFun.symm.toContinuousLinearEquiv

/-- Physical basis version of the orthogonal Schur packet. -/
structure FiniteModeOrthogonalSchurBasisData
    (operator : E →L[Real] E) where
  modeSubspace : Submodule Real E
  basis : Basis Mode Real modeSubspace
  complementEquiv : modeSubspaceᗮ ≃L[Real] modeSubspaceᗮ
  complementEquiv_eq :
    complementEquiv.toContinuousLinearMap =
      finiteModeCanonicalBlockD operator
        (finiteModeOrthogonalDecomposition modeSubspace
          (finiteModeContinuousEquivOfBasis modeSubspace basis))

/-- Ambient vector represented by one named basis element. -/
def FiniteModeOrthogonalSchurBasisData.modeVector
    {operator : E →L[Real] E}
    (data : FiniteModeOrthogonalSchurBasisData
      (Mode := Mode) operator)
    (mode : Mode) : E :=
  data.basis mode

/-- The named vectors are linearly independent in the ambient Hilbert space. -/
theorem FiniteModeOrthogonalSchurBasisData.modeVector_linearIndependent
    {operator : E →L[Real] E}
    (data : FiniteModeOrthogonalSchurBasisData
      (Mode := Mode) operator) :
    LinearIndependent Real data.modeVector := by
  exact data.basis.linearIndependent.map'
    data.modeSubspace.subtype data.modeSubspace.injective_subtype

/-- Convert the basis packet to the preceding orthogonal decomposition packet. -/
def FiniteModeOrthogonalSchurBasisData.toOrthogonalData
    {operator : E →L[Real] E}
    (data : FiniteModeOrthogonalSchurBasisData
      (Mode := Mode) operator) :
    FiniteModeOrthogonalSchurDecompositionData operator where
  modeSubspace := data.modeSubspace
  modeEquiv := finiteModeContinuousEquivOfBasis data.modeSubspace data.basis
  complementEquiv := data.complementEquiv
  complementEquiv_eq := data.complementEquiv_eq

/-- Complete bounded Schur packet from the physical basis. -/
def FiniteModeOrthogonalSchurBasisData.toContinuousSchurBlockData
    {operator : E →L[Real] E}
    (data : FiniteModeOrthogonalSchurBasisData
      (Mode := Mode) operator) :
    FiniteModeContinuousSchurBlockData operator Mode data.modeSubspaceᗮ :=
  data.toOrthogonalData.toContinuousSchurBlockData

/-- Public checkpoint: the finite basis and inverse of the canonical
complementary block determine the full Schur problem. -/
theorem finite_mode_orthogonal_schur_basis_gate
    (operator : E →L[Real] E)
    (data : FiniteModeOrthogonalSchurBasisData
      (Mode := Mode) operator) :
    LinearIndependent Real data.modeVector ∧
      Nonempty
        (FiniteModeContinuousSchurBlockData operator Mode
          data.modeSubspaceᗮ) :=
  ⟨data.modeVector_linearIndependent,
    ⟨data.toContinuousSchurBlockData⟩⟩

end
end P0EFTJanusProgramPFiniteModeOrthogonalSchurBasis4D
end JanusFormal
