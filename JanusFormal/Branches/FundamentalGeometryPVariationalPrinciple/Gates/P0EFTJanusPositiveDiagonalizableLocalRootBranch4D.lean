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
open Filter

abbrev Matrix4 := P0EFTJanusPositiveDiagonalizableRelativeRoot4D.Matrix4

local instance matrix4NormedAddCommGroup : NormedAddCommGroup Matrix4 :=
  Matrix.frobeniusNormedAddCommGroup

local instance matrix4AddCommGroup : AddCommGroup Matrix4 :=
  matrix4NormedAddCommGroup.toAddCommGroup

local instance matrix4TopologicalSpace : TopologicalSpace Matrix4 :=
  matrix4NormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace

local instance matrix4NormedSpace : NormedSpace Real Matrix4 :=
  Matrix.frobeniusNormedSpace

local instance matrix4Module : Module Real Matrix4 :=
  matrix4NormedSpace.toModule

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

/-- Local IFT branches based at the same selected root have equal germs.  This
is local inverse uniqueness, not a global gluing statement. -/
theorem eventually_positiveDiagonalizableLocalRootBranch_eq_of_root_eq
    (first second : PositiveDiagonalizableRelativeMatrix)
    (hRoot : positiveSimilarityRoot first = positiveSimilarityRoot second) :
    ∀ᶠ target in 𝓝 first.target,
      positiveDiagonalizableLocalRootBranch first target =
        positiveDiagonalizableLocalRootBranch second target := by
  have hTarget : first.target = second.target := by
    calc
      first.target = positiveSimilarityRoot first *
          positiveSimilarityRoot first :=
        (positiveSimilarityRoot_square first).symm
      _ = positiveSimilarityRoot second *
          positiveSimilarityRoot second := by rw [hRoot]
      _ = second.target := positiveSimilarityRoot_square second
  have hLeftFirst :
      ∀ᶠ point in 𝓝 (positiveSimilarityRoot first),
        positiveDiagonalizableLocalRootBranch first (matrixSquare point) =
          point := by
    simpa [positiveDiagonalizableLocalRootBranch] using
      eventually_localRootBranch_matrixSquare
        (positiveSimilarityRoot first)
        (positiveDiagonalizableSylvesterEquivWitness first)
  have hContinuousSecond :
      ContinuousAt (positiveDiagonalizableLocalRootBranch second)
        second.target :=
    (positiveDiagonalizableLocalRootBranch_hasStrictFDerivAt second).continuousAt
  have hTendstoSecond :
      Tendsto (positiveDiagonalizableLocalRootBranch second)
        (𝓝 first.target) (𝓝 (positiveSimilarityRoot first)) := by
    rw [hTarget, hRoot,
      ← positiveDiagonalizableLocalRootBranch_at_target second]
    exact hContinuousSecond
  have hLeftAfterSecond := hTendstoSecond.eventually hLeftFirst
  have hRightSecond :
      ∀ᶠ target in 𝓝 first.target,
        matrixSquare (positiveDiagonalizableLocalRootBranch second target) =
          target := by
    simpa only [hTarget] using
      eventually_positiveDiagonalizableLocalRootBranch_square second
  filter_upwards [hLeftAfterSecond, hRightSecond] with target hLeft hRight
  calc
    positiveDiagonalizableLocalRootBranch first target =
        positiveDiagonalizableLocalRootBranch first
          (matrixSquare
            (positiveDiagonalizableLocalRootBranch second target)) :=
      (congrArg (positiveDiagonalizableLocalRootBranch first) hRight).symm
    _ = positiveDiagonalizableLocalRootBranch second target := hLeft

/-- Equal targets and equal ordered positive spectra determine the same local
root germ. -/
theorem eventually_positiveDiagonalizableLocalRootBranch_eq_of_same_target_and_ordered_spectrum
    (first second : PositiveDiagonalizableRelativeMatrix)
    (hTarget : first.target = second.target)
    (hSpectrum : first.eigenvalue = second.eigenvalue) :
    ∀ᶠ target in 𝓝 first.target,
      positiveDiagonalizableLocalRootBranch first target =
        positiveDiagonalizableLocalRootBranch second target :=
  eventually_positiveDiagonalizableLocalRootBranch_eq_of_root_eq first second
    (positiveSimilarityRoot_eq_of_same_target_and_ordered_spectrum
      first second hTarget hSpectrum)

/-- Equal targets whose supplied positive spectra differ by a permutation
determine the same local root germ. -/
theorem eventually_positiveDiagonalizableLocalRootBranch_eq_of_same_target_and_permuted_spectrum
    (first second : PositiveDiagonalizableRelativeMatrix)
    (permutation : Equiv.Perm (Fin 4))
    (hTarget : first.target = second.target)
    (hSpectrum : second.eigenvalue = first.eigenvalue ∘ permutation) :
    ∀ᶠ target in 𝓝 first.target,
      positiveDiagonalizableLocalRootBranch first target =
        positiveDiagonalizableLocalRootBranch second target :=
  eventually_positiveDiagonalizableLocalRootBranch_eq_of_root_eq first second
    (positiveSimilarityRoot_eq_of_same_target_and_permuted_spectrum
      first second permutation hTarget hSpectrum)

end

end P0EFTJanusPositiveDiagonalizableLocalRootBranch4D
end JanusFormal
