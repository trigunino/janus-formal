import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusAbelianConnectionSecondJet

namespace JanusFormal
namespace P0EFTJanusAbelianConnectionSecondJetSplitting

set_option autoImplicit false

noncomputable section

open P0EFTJanusAbelianConnectionSecondJet

universe u v

/-- Symmetric third-order gauge remainder relative to the canonical closed
curvature-derivative section. -/
def gaugeRemainder
    {Tangent : Type u}
    (jet : AbelianConnectionSecondJet Tangent) :
    AbelianGaugeThirdJet Tangent :=
  gaugeBetweenEqualCurvatureDerivatives
    (canonicalSecondJet (reduceSecondJet jet))
    jet
    (curvatureDerivative_canonicalSecondJet (reduceSecondJet jet))

/-- Decomposition of a connection second jet into pure gauge third-order data
and its closed first curvature derivative. -/
def decomposeConnectionSecondJet
    {Tangent : Type u}
    (jet : AbelianConnectionSecondJet Tangent) :
    AbelianGaugeThirdJet Tangent × ClosedCurvatureDerivative Tangent :=
  (gaugeRemainder jet, reduceSecondJet jet)

/-- Reconstruction from a symmetric gauge third jet and closed `∇F` data. -/
def reconstructConnectionSecondJet
    {Tangent : Type u}
    (data : AbelianGaugeThirdJet Tangent ×
      ClosedCurvatureDerivative Tangent) :
    AbelianConnectionSecondJet Tangent :=
  applyGaugeThird data.1 (canonicalSecondJet data.2)

/-- Reconstruction after decomposition returns the original connection second
jet. -/
theorem reconstruct_decomposeConnectionSecondJet
    {Tangent : Type u}
    (jet : AbelianConnectionSecondJet Tangent) :
    reconstructConnectionSecondJet (decomposeConnectionSecondJet jet) = jet := by
  exact gaugeBetweenEqualCurvatureDerivatives_maps
    (canonicalSecondJet (reduceSecondJet jet))
    jet
    (curvatureDerivative_canonicalSecondJet (reduceSecondJet jet))

/-- Reduction of a reconstructed connection jet returns the prescribed closed
curvature derivative. -/
theorem reduce_reconstructConnectionSecondJet
    {Tangent : Type u}
    (gauge : AbelianGaugeThirdJet Tangent)
    (data : ClosedCurvatureDerivative Tangent) :
    reduceSecondJet
        (reconstructConnectionSecondJet (gauge, data)) = data := by
  apply ClosedCurvatureDerivative.ext
  change
    curvatureDerivative
        (applyGaugeThird gauge (canonicalSecondJet data)) = data.tensor
  rw [curvatureDerivative_applyGaugeThird]
  exact curvatureDerivative_canonicalSecondJet data

/-- Gauge remainder of a reconstructed connection jet is the prescribed one. -/
theorem gaugeRemainder_reconstructConnectionSecondJet
    {Tangent : Type u}
    (gauge : AbelianGaugeThirdJet Tangent)
    (data : ClosedCurvatureDerivative Tangent) :
    gaugeRemainder
        (reconstructConnectionSecondJet (gauge, data)) = gauge := by
  apply AbelianGaugeThirdJet.ext
  funext x y z
  have hReduce := reduce_reconstructConnectionSecondJet gauge data
  change
    reduceSecondJet
      (applyGaugeThird gauge (canonicalSecondJet data)) = data at hReduce
  simp only [gaugeRemainder,
    gaugeBetweenEqualCurvatureDerivatives,
    reconstructConnectionSecondJet]
  rw [hReduce]
  ring

/-- Decomposition after reconstruction returns the original pair. -/
theorem decompose_reconstructConnectionSecondJet
    {Tangent : Type u}
    (data : AbelianGaugeThirdJet Tangent ×
      ClosedCurvatureDerivative Tangent) :
    decomposeConnectionSecondJet
        (reconstructConnectionSecondJet data) = data := by
  rcases data with ⟨gauge, curvature⟩
  apply Prod.ext
  · exact gaugeRemainder_reconstructConnectionSecondJet gauge curvature
  · exact reduce_reconstructConnectionSecondJet gauge curvature

/-- Exact splitting of abelian connection second jets into gauge and closed
curvature-derivative factors. -/
def connectionSecondJetSplitEquiv
    {Tangent : Type u} :
    AbelianConnectionSecondJet Tangent ≃
      (AbelianGaugeThirdJet Tangent ×
        ClosedCurvatureDerivative Tangent) where
  toFun := decomposeConnectionSecondJet
  invFun := reconstructConnectionSecondJet
  left_inv := reconstruct_decomposeConnectionSecondJet
  right_inv := decompose_reconstructConnectionSecondJet

/-- Equality of the reduced curvature derivative is equality of the second
factor in split coordinates. -/
theorem reduceSecondJet_eq_iff_split_second_eq
    {Tangent : Type u}
    (first second : AbelianConnectionSecondJet Tangent) :
    reduceSecondJet first = reduceSecondJet second ↔
      (connectionSecondJetSplitEquiv first).2 =
        (connectionSecondJetSplitEquiv second).2 := by
  rfl

/-- Gauge-invariant observables depend only on the closed curvature-derivative
factor of the exact splitting. -/
theorem gaugeInvariant_factorization_through_split_second
    {Tangent : Type u} {Target : Type v}
    (observable : AbelianConnectionSecondJet Tangent → Target)
    (hInvariant : IsGaugeInvariant observable) :
    ∃! reduced : ClosedCurvatureDerivative Tangent → Target,
      ∀ jet,
        observable jet = reduced (connectionSecondJetSplitEquiv jet).2 := by
  simpa [connectionSecondJetSplitEquiv, decomposeConnectionSecondJet] using
    gaugeInvariant_has_unique_closedCurvature_reduction observable hInvariant

/-- Exact boundary after splitting the first derivative of determinant-line
curvature. -/
structure AbelianConnectionSecondJetSplittingStatus where
  exactGaugeSequenceProved : Prop
  canonicalSectionConstructed : Prop
  gaugeRemainderConstructed : Prop
  directProductEquivalenceProved : Prop
  quotientFactorizationRecovered : Prop
  finiteDimensionalMultilinearModelsInserted : Prop
  residualFrameEquivarianceProved : Prop
  determinantLineConnectionInserted : Prop
  actualCovariantDerivativeOfCurvatureInserted : Prop
  smoothJetBundleSplittingProved : Prop

/-- Closure of the geometric determinant-connection splitting stage. -/
def abelianConnectionSecondJetSplittingClosed
    (s : AbelianConnectionSecondJetSplittingStatus) : Prop :=
  s.exactGaugeSequenceProved /\
  s.canonicalSectionConstructed /\
  s.gaugeRemainderConstructed /\
  s.directProductEquivalenceProved /\
  s.quotientFactorizationRecovered /\
  s.finiteDimensionalMultilinearModelsInserted /\
  s.residualFrameEquivarianceProved /\
  s.determinantLineConnectionInserted /\
  s.actualCovariantDerivativeOfCurvatureInserted /\
  s.smoothJetBundleSplittingProved

/-- The algebraic splitting does not identify its closed factor with the
covariant derivative of the actual SpinC determinant-line curvature. -/
theorem missing_determinant_connection_blocks_splitting
    (s : AbelianConnectionSecondJetSplittingStatus)
    (hMissing : Not s.determinantLineConnectionInserted) :
    Not (abelianConnectionSecondJetSplittingClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.1

end

end P0EFTJanusAbelianConnectionSecondJetSplitting
end JanusFormal
