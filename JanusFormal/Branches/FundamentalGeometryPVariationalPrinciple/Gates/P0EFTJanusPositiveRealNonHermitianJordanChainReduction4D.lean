import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusHermitianPositiveJordanPresentation4D

/-!
# Reduction of the non-Hermitian positive sector to a Jordan-chain basis

Mathlib proves the generalized-eigenspace statements needed before choosing
chains, but does not construct a Jordan-chain basis.  This gate isolates the
missing datum at that exact lower level: one invertible matrix of chain
vectors, its intertwining equation, and one of the five partitions of four.
The inverse matrix, existing presentation package, root and Sylvester
regularity are then all derived rather than assumed.
-/

namespace JanusFormal
namespace P0EFTJanusPositiveRealNonHermitianJordanChainReduction4D

set_option autoImplicit false

noncomputable section

open Matrix
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusPositiveSingleEigenvalueJordanRoot4D
open P0EFTJanusPositiveJordanTwoPlusTwoRoot4D
open P0EFTJanusPositiveJordanThreePlusOneRoot4D
open P0EFTJanusPositiveJordanTwoPlusOnePlusOneRoot4D
open P0EFTJanusPositiveRealJordanPartitionSelector4D
open P0EFTJanusPositiveRealJordanPresentationBridge4D
open P0EFTJanusHermitianPositiveJordanPresentation4D

abbrev Matrix4 := P0EFTJanusHermitianPositiveJordanPresentation4D.Matrix4

/-- An invertible matrix of chain vectors.  The intertwining equation says
that its columns carry the supplied canonical Jordan action. -/
structure JordanChainSimilarity4 (target canonical : Matrix4) where
  change : Matrix4
  det_isUnit : IsUnit change.det
  intertwines : target * change = change * canonical

theorem JordanChainSimilarity4.inverse_mul_change
    {target canonical : Matrix4}
    (chain : JordanChainSimilarity4 target canonical) :
    chain.change⁻¹ * chain.change = 1 :=
  Matrix.nonsing_inv_mul chain.change chain.det_isUnit

theorem JordanChainSimilarity4.change_mul_inverse
    {target canonical : Matrix4}
    (chain : JordanChainSimilarity4 target canonical) :
    chain.change * chain.change⁻¹ = 1 :=
  Matrix.mul_nonsing_inv chain.change chain.det_isUnit

theorem JordanChainSimilarity4.target_eq_similarity
    {target canonical : Matrix4}
    (chain : JordanChainSimilarity4 target canonical) :
    target = chain.change * canonical * chain.change⁻¹ := by
  calc
    target = target * 1 := (mul_one target).symm
    _ = target * (chain.change * chain.change⁻¹) := by
      rw [chain.change_mul_inverse]
    _ = (target * chain.change) * chain.change⁻¹ := by
      rw [Matrix.mul_assoc]
    _ = chain.change * canonical * chain.change⁻¹ := by
      rw [chain.intertwines]

/-- Intrinsic size-four single-eigenvalue chain information. -/
structure PositiveBlock4ChainCertificate (target : Matrix4) where
  eigenvalue : PositiveEigenvalue
  fourth : scaledJordanDisplacementFourth eigenvalue.1 target = 0
  cube_ne :
    let nilpotent := target - eigenvalue.1 • (1 : Matrix4)
    nilpotent * nilpotent * nilpotent ≠ 0

/-- The exact five chain-basis alternatives in dimension four.  Unlike
`PositiveRealJordanPresentation4`, these constructors do not supply an
inverse matrix or a pre-packaged similarity target. -/
inductive PositiveRealJordanChainBasis4 (target : Matrix4) where
  | block4 : PositiveBlock4ChainCertificate target →
      PositiveRealJordanChainBasis4 target
  | block31 (triple singleton : PositiveEigenvalue) :
      JordanChainSimilarity4 target
        (canonicalJordan31Target triple singleton) →
      PositiveRealJordanChainBasis4 target
  | block22 (first second : PositiveEigenvalue) :
      JordanChainSimilarity4 target
        (canonicalJordan22Target first second) →
      PositiveRealJordanChainBasis4 target
  | block211 (pair firstSingleton secondSingleton : PositiveEigenvalue) :
      JordanChainSimilarity4 target
        (canonicalJordan211Target pair firstSingleton secondSingleton) →
      PositiveRealJordanChainBasis4 target
  | diagonal (spectrum : PositiveTargetSpectrum4) :
      JordanChainSimilarity4 target (Matrix.diagonal spectrum.1) →
      PositiveRealJordanChainBasis4 target

/-- Every lower-level chain-basis certificate assembles into the existing
unified presentation. -/
theorem positiveRealJordanChainBasis_hasPresentation
    {target : Matrix4} (certificate : PositiveRealJordanChainBasis4 target) :
    HasPositiveRealJordanPresentation target := by
  cases certificate with
  | block4 chain =>
      let single : PositiveSingleEigenvalueJordanData :=
        ⟨(chain.eigenvalue, target), chain.fourth⟩
      let strict : StrictPositiveBlock4Data := ⟨single, by
        change
          (target - chain.eigenvalue.1 • (1 : Matrix4)) *
              (target - chain.eigenvalue.1 • (1 : Matrix4)) *
            (target - chain.eigenvalue.1 • (1 : Matrix4)) ≠ 0
        exact chain.cube_ne⟩
      exact ⟨.block4 strict, rfl⟩
  | block31 triple singleton chain =>
      let data : Jordan31Data :=
        ⟨((triple, singleton), (chain.change, chain.change⁻¹)),
          chain.inverse_mul_change, chain.change_mul_inverse⟩
      refine ⟨.block31 data, ?_⟩
      simpa [presentationTarget, jordan31Target, jordan31Change,
        jordan31Inverse, tripleEigenvalue, singletonEigenvalue, data] using
        chain.target_eq_similarity.symm
  | block22 first second chain =>
      let data : Jordan22Data :=
        ⟨((first, second), (chain.change, chain.change⁻¹)),
          chain.inverse_mul_change, chain.change_mul_inverse⟩
      refine ⟨.block22 data, ?_⟩
      simpa [presentationTarget, jordan22Target, jordan22Change,
        jordan22Inverse, firstEigenvalue, secondEigenvalue, data] using
        chain.target_eq_similarity.symm
  | block211 pair firstSingleton secondSingleton chain =>
      let data : Jordan211Data :=
        ⟨((pair, firstSingleton, secondSingleton),
            (chain.change, chain.change⁻¹)),
          chain.inverse_mul_change, chain.change_mul_inverse⟩
      refine ⟨.block211 data, ?_⟩
      simpa [presentationTarget, jordan211Target, jordan211Change,
        jordan211Inverse, pairEigenvalue, firstSingletonEigenvalue,
        secondSingletonEigenvalue, data] using
        chain.target_eq_similarity.symm
  | diagonal spectrum chain =>
      let data : PositiveDiagonalPresentation4 :=
        ⟨(spectrum, (chain.change, chain.change⁻¹)),
          chain.inverse_mul_change, chain.change_mul_inverse⟩
      refine ⟨.diagonal data, ?_⟩
      simpa [presentationTarget, diagonalPresentationTarget,
        diagonalPresentationChange, diagonalPresentationInverse,
        diagonalPresentationSpectrum, data] using
        chain.target_eq_similarity.symm

/-- Exact missing Mathlib-level obligation, now restricted to the genuinely
unresolved non-Hermitian part of the positive raw spectrum. -/
def PositiveRealNonHermitianJordanChainBasisResidual4 : Prop :=
  ∀ target : Matrix4, PositiveRealSplitCharpoly4 target →
    ¬ target.IsHermitian → Nonempty (PositiveRealJordanChainBasis4 target)

theorem nonHermitianPresentationResidual_of_chainBasisResidual
    (residual : PositiveRealNonHermitianJordanChainBasisResidual4) :
    PositiveRealNonHermitianJordanPresentationResidual4 := by
  intro target hSpectrum hNonHermitian
  obtain ⟨certificate⟩ := residual target hSpectrum hNonHermitian
  exact positiveRealJordanChainBasis_hasPresentation certificate

/-- Once Mathlib supplies the chain basis, the former universal presentation
bridge follows with the Hermitian sector already discharged upstream. -/
theorem positiveRealJordanBasisBridge4_of_nonHermitianChainBasisResidual
    (residual : PositiveRealNonHermitianJordanChainBasisResidual4) :
    PositiveRealJordanBasisBridge4 :=
  positiveRealJordanBasisBridge4_iff_nonHermitianResidual.2
    (nonHermitianPresentationResidual_of_chainBasisResidual residual)

/-- Square-root and Sylvester conclusions are unconditional downstream of the
single chain-basis residual. -/
theorem positiveRealSplitSpectrum_regularRoot_of_chainBasisResidual
    (residual : PositiveRealNonHermitianJordanChainBasisResidual4)
    (target : Matrix4) (hSpectrum : PositiveRealSplitCharpoly4 target) :
    HasSylvesterRegularRealSquareRoot target :=
  positiveRealSplitSpectrum_regularRoot_reduction
    (positiveRealJordanBasisBridge4_of_nonHermitianChainBasisResidual residual)
    target hSpectrum

end

end P0EFTJanusPositiveRealNonHermitianJordanChainReduction4D
end JanusFormal
