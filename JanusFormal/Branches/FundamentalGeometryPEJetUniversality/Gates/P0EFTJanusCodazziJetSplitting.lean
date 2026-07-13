import Mathlib.Tactic.Module
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusCodazziJetExactness

namespace JanusFormal
namespace P0EFTJanusCodazziJetSplitting

set_option autoImplicit false

noncomputable section

open P0EFTJanusCodazziJetExactness

universe u v w

/-- The fully symmetric remainder of a covariant second-fundamental-form jet
relative to the canonical closed-Codazzi section. -/
def symmetricRemainder
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    (jet : CovariantSecondFundamentalJet Tangent Normal) :
    SymmetricNormalThirdJet Tangent Normal :=
  symmetricThirdJetBetweenEqualCodazzi
    (canonicalCovariantSecondFundamentalJet (reduceCodazziJet jet))
    jet
    (codazziTensor_canonical (reduceCodazziJet jet))

/-- Decomposition of a `∇II` jet into its fully symmetric part and its closed
Codazzi tensor. -/
def decomposeCodazziJet
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    (jet : CovariantSecondFundamentalJet Tangent Normal) :
    SymmetricNormalThirdJet Tangent Normal ×
      ClosedCodazziTensor Tangent Normal :=
  (symmetricRemainder jet, reduceCodazziJet jet)

/-- Reconstruction from a symmetric third-order tensor and closed Codazzi data. -/
def reconstructCodazziJet
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    (data : SymmetricNormalThirdJet Tangent Normal ×
      ClosedCodazziTensor Tangent Normal) :
    CovariantSecondFundamentalJet Tangent Normal :=
  applySymmetricThirdJet data.1
    (canonicalCovariantSecondFundamentalJet data.2)

/-- Reconstruction after decomposition returns the original `∇II` jet. -/
theorem reconstruct_decomposeCodazziJet
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    (jet : CovariantSecondFundamentalJet Tangent Normal) :
    reconstructCodazziJet (decomposeCodazziJet jet) = jet := by
  exact symmetricThirdJetBetweenEqualCodazzi_maps
    (canonicalCovariantSecondFundamentalJet (reduceCodazziJet jet))
    jet
    (codazziTensor_canonical (reduceCodazziJet jet))

/-- The closed Codazzi component of a reconstructed jet is the prescribed one. -/
theorem reduce_reconstructCodazziJet
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    (gauge : SymmetricNormalThirdJet Tangent Normal)
    (data : ClosedCodazziTensor Tangent Normal) :
    reduceCodazziJet
        (reconstructCodazziJet (gauge, data)) = data := by
  apply ClosedCodazziTensor.ext
  change
    codazziTensor
        (applySymmetricThirdJet gauge
          (canonicalCovariantSecondFundamentalJet data)) =
      data.tensor
  rw [codazziTensor_applySymmetricThirdJet]
  exact codazziTensor_canonical data

/-- The symmetric component of a reconstructed jet is the prescribed gauge
remainder. -/
theorem symmetricRemainder_reconstructCodazziJet
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    (gauge : SymmetricNormalThirdJet Tangent Normal)
    (data : ClosedCodazziTensor Tangent Normal) :
    symmetricRemainder
        (reconstructCodazziJet (gauge, data)) = gauge := by
  apply SymmetricNormalThirdJet.ext
  funext x y z
  have hReduce := reduce_reconstructCodazziJet gauge data
  simp only [symmetricRemainder,
    symmetricThirdJetBetweenEqualCodazzi,
    reconstructCodazziJet]
  rw [hReduce]
  module

/-- Decomposition after reconstruction returns the original pair. -/
theorem decompose_reconstructCodazziJet
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    (data : SymmetricNormalThirdJet Tangent Normal ×
      ClosedCodazziTensor Tangent Normal) :
    decomposeCodazziJet (reconstructCodazziJet data) = data := by
  rcases data with ⟨gauge, codazzi⟩
  apply Prod.ext
  · exact symmetricRemainder_reconstructCodazziJet gauge codazzi
  · exact reduce_reconstructCodazziJet gauge codazzi

/-- Exact algebraic splitting of first covariant second-fundamental-form jets.
The Codazzi tensor is only the quotient component; the fully symmetric third
jet remains independent data. -/
def codazziJetSplitEquiv
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal] :
    CovariantSecondFundamentalJet Tangent Normal ≃
      (SymmetricNormalThirdJet Tangent Normal ×
        ClosedCodazziTensor Tangent Normal) where
  toFun := decomposeCodazziJet
  invFun := reconstructCodazziJet
  left_inv := reconstruct_decomposeCodazziJet
  right_inv := decompose_reconstructCodazziJet

/-- Two `∇II` jets have the same Codazzi component exactly when their split
representatives differ only in the symmetric factor. -/
theorem reduceCodazziJet_eq_iff_split_second_eq
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    (first second : CovariantSecondFundamentalJet Tangent Normal) :
    reduceCodazziJet first = reduceCodazziJet second ↔
      (codazziJetSplitEquiv first).2 =
        (codazziJetSplitEquiv second).2 := by
  rfl

/-- An observable insensitive to the symmetric third-jet direction depends only
on the closed Codazzi factor of the exact splitting. -/
theorem invariant_factorization_through_split_second
    {Tangent : Type u} {Normal : Type v}
    [AddCommGroup Normal] [Module ℝ Normal]
    {Target : Type w}
    (observable : CovariantSecondFundamentalJet Tangent Normal → Target)
    (hInvariant : IsSymmetricThirdInvariant observable) :
    ∃! reduced : ClosedCodazziTensor Tangent Normal → Target,
      ∀ jet,
        observable jet = reduced (codazziJetSplitEquiv jet).2 := by
  simpa [codazziJetSplitEquiv, decomposeCodazziJet] using
    invariant_has_unique_closedCodazzi_reduction observable hInvariant

/-- Exact boundary after splitting the first covariant derivative of the second
fundamental form. -/
structure CodazziJetSplittingStatus where
  exactCodazziSequenceProved : Prop
  canonicalSectionConstructed : Prop
  symmetricRemainderConstructed : Prop
  directProductEquivalenceProved : Prop
  quotientFactorizationRecovered : Prop
  finiteDimensionalMultilinearModelsInserted : Prop
  residualOrthogonalEquivarianceProved : Prop
  actualCovariantDerivativeOfIIInserted : Prop
  ambientNormalCurvatureIdentified : Prop
  smoothJetBundleSplittingProved : Prop

/-- Closure of the geometric first-derivative splitting stage. -/
def codazziJetSplittingClosed
    (s : CodazziJetSplittingStatus) : Prop :=
  s.exactCodazziSequenceProved /\
  s.canonicalSectionConstructed /\
  s.symmetricRemainderConstructed /\
  s.directProductEquivalenceProved /\
  s.quotientFactorizationRecovered /\
  s.finiteDimensionalMultilinearModelsInserted /\
  s.residualOrthogonalEquivarianceProved /\
  s.actualCovariantDerivativeOfIIInserted /\
  s.ambientNormalCurvatureIdentified /\
  s.smoothJetBundleSplittingProved

/-- The algebraic splitting does not by itself identify its first factor with the
fully symmetric part of the genuine manifold-level covariant derivative of
`II`. -/
theorem missing_geometric_covariantDerivative_blocks_splitting
    (s : CodazziJetSplittingStatus)
    (hMissing : Not s.actualCovariantDerivativeOfIIInserted) :
    Not (codazziJetSplittingClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.1

end

end P0EFTJanusCodazziJetSplitting
end JanusFormal
