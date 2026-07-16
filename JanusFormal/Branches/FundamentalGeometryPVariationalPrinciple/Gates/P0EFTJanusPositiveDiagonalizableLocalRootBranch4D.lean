import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusPositiveDiagonalizableSylvesterInverse4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLorentzLocalRootBranch4D

/-!
# Local root branches at positive diagonalizable presentations

The explicit inverse Sylvester operator promotes matrix squaring to a local
homeomorphism at every supplied positive diagonalizable root.  The resulting
branch is local to that presentation; no global gluing is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveDiagonalizableLocalRootBranch4D

set_option autoImplicit false

noncomputable section

open scoped Matrix.Norms.Frobenius RightActions Topology
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveDiagonalizableRelativeRoot4D
open P0EFTJanusPositiveDiagonalizableSylvesterInverse4D
open P0EFTJanusLorentzLocalRootBranch4D

abbrev Matrix4 := P0EFTJanusPositiveDiagonalizableRelativeRoot4D.Matrix4

/-- The Sylvester operator at the selected root as a continuous linear
equivalence. -/
def positiveDiagonalizableSylvesterEquiv
    (data : PositiveDiagonalizableRelativeMatrix) : Matrix4 ≃L[Real] Matrix4 :=
  (LinearEquiv.ofBijective
    (sylvesterOperator (positiveSimilarityRoot data)).toLinearMap
    (positiveDiagonalizable_sylvester_bijective data)).toContinuousLinearEquiv

/-- The equivalence witness required by the local inverse-function gate. -/
def positiveDiagonalizableSylvesterEquivWitness
    (data : PositiveDiagonalizableRelativeMatrix) :
    SylvesterEquivWitness (positiveSimilarityRoot data) where
  equiv := positiveDiagonalizableSylvesterEquiv data
  forward_eq := rfl

/-- The inverse of the Sylvester equivalence is the transported entrywise
inverse already constructed. -/
theorem positiveDiagonalizableSylvesterEquiv_symm_apply
    (data : PositiveDiagonalizableRelativeMatrix) (target : Matrix4) :
    (positiveDiagonalizableSylvesterEquiv data).symm target =
      positiveDiagonalizableSylvesterInverse data target := by
  apply (positiveDiagonalizable_sylvester_bijective data).1
  rw [positiveDiagonalizableSylvesterInverse_right]
  change positiveDiagonalizableSylvesterEquiv data
      ((positiveDiagonalizableSylvesterEquiv data).symm target) = target
  exact (positiveDiagonalizableSylvesterEquiv data).apply_symm_apply target

/-- The genuine IFT branch of matrix square roots at the supplied
positive diagonalizable root. -/
def positiveDiagonalizableLocalRootBranch
    (data : PositiveDiagonalizableRelativeMatrix) : Matrix4 → Matrix4 :=
  localRootBranch (positiveSimilarityRoot data)
    (positiveDiagonalizableSylvesterEquivWitness data)

theorem positiveDiagonalizableLocalRootBranch_at_target
    (data : PositiveDiagonalizableRelativeMatrix) :
    positiveDiagonalizableLocalRootBranch data data.target =
      positiveSimilarityRoot data := by
  have hBase : matrixSquare (positiveSimilarityRoot data) = data.target := by
    exact positiveSimilarityRoot_square data
  rw [← hBase]
  exact localRootBranch_at_base (positiveSimilarityRoot data)
    (positiveDiagonalizableSylvesterEquivWitness data)

/-- Every sufficiently small independent target perturbation is squared back
exactly by the local branch. -/
theorem eventually_positiveDiagonalizableLocalRootBranch_square
    (data : PositiveDiagonalizableRelativeMatrix) :
    ∀ᶠ target in 𝓝 data.target,
      matrixSquare (positiveDiagonalizableLocalRootBranch data target) =
        target := by
  have hBase : matrixSquare (positiveSimilarityRoot data) = data.target := by
    exact positiveSimilarityRoot_square data
  rw [← hBase]
  exact eventually_matrixSquare_localRootBranch
    (positiveSimilarityRoot data)
    (positiveDiagonalizableSylvesterEquivWitness data)

/-- The strict derivative of the IFT branch is the explicit transported
inverse Sylvester operator. -/
theorem positiveDiagonalizableLocalRootBranch_hasStrictFDerivAt
    (data : PositiveDiagonalizableRelativeMatrix) :
    MatrixHasStrictFDerivAt (positiveDiagonalizableLocalRootBranch data)
      (positiveDiagonalizableSylvesterInverseCLM data) data.target := by
  have hBase : matrixSquare (positiveSimilarityRoot data) = data.target := by
    exact positiveSimilarityRoot_square data
  have hInverse :
      ((positiveDiagonalizableSylvesterEquiv data).symm :
        Matrix4 →L[Real] Matrix4) =
        positiveDiagonalizableSylvesterInverseCLM data := by
    apply ContinuousLinearMap.ext
    intro target
    exact positiveDiagonalizableSylvesterEquiv_symm_apply data target
  rw [← hBase, ← hInverse]
  exact localRootBranch_hasStrictFDerivAt
    (positiveSimilarityRoot data)
    (positiveDiagonalizableSylvesterEquivWitness data)

end

end P0EFTJanusPositiveDiagonalizableLocalRootBranch4D
end JanusFormal
