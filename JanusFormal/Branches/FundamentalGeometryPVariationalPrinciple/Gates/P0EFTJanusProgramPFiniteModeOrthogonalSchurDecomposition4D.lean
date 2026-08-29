import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiniteModeCanonicalSchurDecomposition4D

/-!
# Orthogonal finite-mode Schur decomposition

A finite Schur reduction should not start from an arbitrary continuous
isomorphism of the full Hilbert space.  Once a finite physical mode subspace
`K` and coordinates on `K` are fixed, Hilbert geometry supplies the canonical
splitting

`E ≃L (Mode → ℝ) × Kᗮ`

by orthogonal projection.  Conjugating the displayed operator by this splitting
then determines all four Schur blocks.  The only analytic input left at the
Schur layer is invertibility of the automatically extracted complementary
block.

No finite projector is added to the operator and no auxiliary complement is
chosen: the complement is definitionally `Kᗮ`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPFiniteModeOrthogonalSchurDecomposition4D

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped InnerProductSpace
open P0EFTJanusProgramPFiniteModeCanonicalSchurDecomposition4D
open P0EFTJanusProgramPFiniteModeContinuousSchurBlock4D

variable {E Mode : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
  [Fintype Mode] [DecidableEq Mode]

private abbrev FinitePart (Mode : Type*) := Mode → Real

/-- Canonical Hilbert decomposition associated with one finite-dimensional
physical mode subspace.  Finite-dimensionality of the subspace is derived from
the coordinate equivalence rather than supplied separately. -/
noncomputable def finiteModeOrthogonalDecomposition
    (modeSubspace : Submodule Real E)
    (modeEquiv : FinitePart Mode ≃L[Real] modeSubspace) :
    E ≃L[Real] (FinitePart Mode × modeSubspaceᗮ) := by
  letI : FiniteDimensional Real modeSubspace :=
    FiniteDimensional.of_surjective modeEquiv.toLinearMap
      modeEquiv.surjective
  letI : CompleteSpace modeSubspace := by infer_instance
  exact
    { toFun := fun vector =>
        (modeEquiv.symm (modeSubspace.orthogonalProjectionOnto vector),
          modeSubspaceᗮ.orthogonalProjectionOnto vector)
      invFun := fun state =>
        ((modeEquiv state.1 : modeSubspace) : E) + (state.2 : E)
      map_add' := by
        intro first second
        apply Prod.ext
        · simp
        · simp
      map_smul' := by
        intro scalar vector
        apply Prod.ext
        · simp
        · simp
      left_inv := by
        intro vector
        simp only [modeEquiv.apply_symm_apply]
        change modeSubspace.starProjection vector +
          modeSubspaceᗮ.starProjection vector = vector
        exact modeSubspace.starProjection_add_starProjection_orthogonal vector
      right_inv := by
        intro state
        rcases state with ⟨finite, complement⟩
        apply Prod.ext
        · change modeEquiv.symm
              (modeSubspace.orthogonalProjectionOnto
                (((modeEquiv finite : modeSubspace) : E) +
                  (complement : E))) = finite
          rw [map_add]
          simp
        · change modeSubspaceᗮ.orthogonalProjectionOnto
              (((modeEquiv finite : modeSubspace) : E) +
                (complement : E)) = complement
          rw [map_add]
          simp
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }

/-- The finite and complementary coordinates reconstruct every vector exactly. -/
theorem finiteModeOrthogonalDecomposition_symm_apply_apply
    (modeSubspace : Submodule Real E)
    (modeEquiv : FinitePart Mode ≃L[Real] modeSubspace)
    (vector : E) :
    (finiteModeOrthogonalDecomposition modeSubspace modeEquiv).symm
        (finiteModeOrthogonalDecomposition modeSubspace modeEquiv vector) =
      vector :=
  (finiteModeOrthogonalDecomposition modeSubspace modeEquiv).symm_apply_apply
    vector

/-- The finite coordinate is the orthogonal projection onto the selected mode
subspace, expressed in the supplied physical coordinates. -/
@[simp]
theorem finiteModeOrthogonalDecomposition_fst
    (modeSubspace : Submodule Real E)
    [FiniteDimensional Real modeSubspace]
    (modeEquiv : FinitePart Mode ≃L[Real] modeSubspace)
    (vector : E) :
    (finiteModeOrthogonalDecomposition modeSubspace modeEquiv vector).1 =
      modeEquiv.symm (modeSubspace.orthogonalProjectionOnto vector) :=
  rfl

/-- The infinite coordinate is the orthogonal projection onto the canonical
orthogonal complement. -/
@[simp]
theorem finiteModeOrthogonalDecomposition_snd
    (modeSubspace : Submodule Real E)
    (modeEquiv : FinitePart Mode ≃L[Real] modeSubspace)
    (vector : E) :
    (finiteModeOrthogonalDecomposition modeSubspace modeEquiv vector).2 =
      modeSubspaceᗮ.orthogonalProjectionOnto vector :=
  rfl

/-- Orthogonal Schur input.  The decomposition and all four blocks are
canonical; only the inverse of the extracted complementary block remains. -/
structure FiniteModeOrthogonalSchurDecompositionData
    (operator : E →L[Real] E) where
  modeSubspace : Submodule Real E
  modeEquiv : FinitePart Mode ≃L[Real] modeSubspace
  complementEquiv : modeSubspaceᗮ ≃L[Real] modeSubspaceᗮ
  complementEquiv_eq :
    complementEquiv.toContinuousLinearMap =
      finiteModeCanonicalBlockD operator
        (finiteModeOrthogonalDecomposition modeSubspace modeEquiv)

/-- Convert the orthogonal mode packet to the existing canonical four-block
Schur data. -/
def FiniteModeOrthogonalSchurDecompositionData.toCanonical
    {operator : E →L[Real] E}
    (data : FiniteModeOrthogonalSchurDecompositionData
      (Mode := Mode) operator) :
    FiniteModeCanonicalSchurDecompositionData
      (Mode := Mode) (Complement := data.modeSubspaceᗮ) operator where
  decomposition :=
    finiteModeOrthogonalDecomposition data.modeSubspace data.modeEquiv
  complementEquiv := data.complementEquiv
  complementEquiv_eq := data.complementEquiv_eq

/-- Fully bounded Schur packet generated by orthogonal projection. -/
def FiniteModeOrthogonalSchurDecompositionData.toContinuousSchurBlockData
    {operator : E →L[Real] E}
    (data : FiniteModeOrthogonalSchurDecompositionData
      (Mode := Mode) operator) :
    FiniteModeContinuousSchurBlockData operator Mode data.modeSubspaceᗮ :=
  data.toCanonical.toContinuousSchurBlockData

/-- The complementary Schur block is exactly the restriction read from the
orthogonal decomposition. -/
theorem finiteModeOrthogonalSchur_complement_block
    {operator : E →L[Real] E}
    (data : FiniteModeOrthogonalSchurDecompositionData
      (Mode := Mode) operator) :
    data.complementEquiv.toContinuousLinearMap =
      finiteModeCanonicalBlockD operator
        (finiteModeOrthogonalDecomposition data.modeSubspace data.modeEquiv) :=
  data.complementEquiv_eq

/-- Public checkpoint: one finite physical subspace, its coordinates and
invertibility of the canonical complementary block determine the complete
bounded Schur decomposition. -/
theorem finite_mode_orthogonal_schur_decomposition_gate
    (operator : E →L[Real] E)
    (data : FiniteModeOrthogonalSchurDecompositionData
      (Mode := Mode) operator) :
    Nonempty
      (FiniteModeContinuousSchurBlockData operator Mode data.modeSubspaceᗮ) ∧
      data.complementEquiv.toContinuousLinearMap =
        finiteModeCanonicalBlockD operator
          (finiteModeOrthogonalDecomposition data.modeSubspace data.modeEquiv) :=
  ⟨⟨data.toContinuousSchurBlockData⟩, data.complementEquiv_eq⟩

end
end P0EFTJanusProgramPFiniteModeOrthogonalSchurDecomposition4D
end JanusFormal
