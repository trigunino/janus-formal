import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFixedConjugateSingularFrameValuationCriterion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularMovingSimilarityZeroOverZero4D

/-! # Valuations in regularly moving conjugates of singular frames -/

namespace JanusFormal
namespace P0EFTJanusRegularMovingConjugateSingularFrameValuationCriterion4D

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology
open P0EFTJanusGlobalMonomialMatrixValuationCriterion4D
open P0EFTJanusFinitePolynomialMatrixValuationCriterion4D
open P0EFTJanusRegularMovingSimilarityZeroOverZero4D

abbrev Matrix4 := P0EFTJanusRegularMovingSimilarityZeroOverZero4D.Matrix4

def movingConjugatePath
    (change inverse path : Real → Matrix4) (t : Real) : Matrix4 :=
  change t * path t * inverse t

/-- A regular moving similarity preserves and reflects existence of a finite
matrix limit. -/
theorem exists_finite_limit_movingConjugatePath_iff
    {filter : Filter Real}
    (change inverse : Real → Matrix4)
    (limitChange limitInverse : Matrix4)
    (hRegular : RegularMovingSimilarityAt filter change inverse
      limitChange limitInverse)
    (path : Real → Matrix4) :
    (∃ candidate : Matrix4, Tendsto path filter (nhds candidate)) ↔
      ∃ candidate : Matrix4,
        Tendsto (movingConjugatePath change inverse path) filter
          (nhds candidate) := by
  constructor
  · rintro ⟨candidate, hCandidate⟩
    exact ⟨limitChange * candidate * limitInverse,
      (hRegular.change_tendsto.mul hCandidate).mul hRegular.inverse_tendsto⟩
  · rintro ⟨candidate, hCandidate⟩
    refine ⟨limitInverse * candidate * limitChange, ?_⟩
    have hBack : Tendsto
        (fun t => inverse t * movingConjugatePath change inverse path t *
          change t)
        filter (nhds (limitInverse * candidate * limitChange)) :=
      (hRegular.inverse_tendsto.mul hCandidate).mul hRegular.change_tendsto
    apply hBack.congr'
    filter_upwards with t
    simp only [movingConjugatePath]
    calc
      inverse t * (change t * path t * inverse t) * change t =
          (inverse t * change t) * path t * (inverse t * change t) := by
        noncomm_ring
      _ = path t := by rw [hRegular.leftInverse t]; simp

def movingConjugateMonomialTransport
    (change inverse : Real → Matrix4)
    (data : NonnegativeMonomialMatrixData)
    (frameExponent : Fin 4 → Nat) : Real → Matrix4 :=
  movingConjugatePath change inverse (transportedMatrix data frameExponent)

/-- Exact conjugated limit in the nonnegative monomial valuation branch. -/
theorem movingConjugateMonomialTransport_tendsto
    (change inverse : Real → Matrix4)
    (limitChange limitInverse : Matrix4)
    (hRegular : RegularMovingSimilarityAt (nhdsWithin 0 (Set.Ioi 0))
      change inverse limitChange limitInverse)
    (data : NonnegativeMonomialMatrixData)
    (frameExponent : Fin 4 → Nat)
    (hValuation : ActiveValuationsNonnegative data frameExponent) :
    Tendsto
        (movingConjugateMonomialTransport change inverse data frameExponent)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (limitChange * valuationLimit data frameExponent * limitInverse)) :=
  (hRegular.change_tendsto.mul
    (transportedMatrix_tendsto_of_activeValuationsNonnegative
      data frameExponent hValuation)).mul hRegular.inverse_tendsto

/-- The monomial valuation criterion survives every regularly moving outer
frame with convergent inverse. -/
theorem activeValuationsNonnegative_iff_exists_movingConjugate_finite_limit
    (change inverse : Real → Matrix4)
    (limitChange limitInverse : Matrix4)
    (hRegular : RegularMovingSimilarityAt (nhdsWithin 0 (Set.Ioi 0))
      change inverse limitChange limitInverse)
    (data : NonnegativeMonomialMatrixData)
    (frameExponent : Fin 4 → Nat) :
    ActiveValuationsNonnegative data frameExponent ↔
      ∃ candidate : Matrix4,
        Tendsto
          (movingConjugateMonomialTransport change inverse data frameExponent)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds candidate) := by
  rw [activeValuationsNonnegative_iff_exists_finite_limit]
  simpa [movingConjugateMonomialTransport] using
    exists_finite_limit_movingConjugatePath_iff change inverse
      limitChange limitInverse hRegular (transportedMatrix data frameExponent)

def movingConjugateFinitePolynomialTransport {ι : Type*}
    (change inverse : Real → Matrix4)
    (data : FinitePolynomialMatrixData ι)
    (frameExponent : Fin 4 → Nat) : Real → Matrix4 :=
  movingConjugatePath change inverse
    (finitePolynomialTransportedMatrix data frameExponent)

/-- Exact conjugated limit in the nonnegative finite-polynomial valuation
branch. -/
theorem movingConjugateFinitePolynomialTransport_tendsto
    {ι : Type*}
    (change inverse : Real → Matrix4)
    (limitChange limitInverse : Matrix4)
    (hRegular : RegularMovingSimilarityAt (nhdsWithin 0 (Set.Ioi 0))
      change inverse limitChange limitInverse)
    (data : FinitePolynomialMatrixData ι)
    (frameExponent : Fin 4 → Nat)
    (hValuation : FinitePolynomialValuationsNonnegative data frameExponent) :
    Tendsto
        (movingConjugateFinitePolynomialTransport change inverse data
          frameExponent)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (limitChange * finitePolynomialLimit data frameExponent *
          limitInverse)) :=
  (hRegular.change_tendsto.mul
    (finitePolynomialTransportedMatrix_tendsto
      data frameExponent hValuation)).mul hRegular.inverse_tendsto

/-- The finite-polynomial valuation criterion also survives every regularly
moving outer frame with convergent inverse. -/
theorem finitePolynomialValuationsNonnegative_iff_exists_movingConjugate_finite_limit
    {ι : Type*}
    (change inverse : Real → Matrix4)
    (limitChange limitInverse : Matrix4)
    (hRegular : RegularMovingSimilarityAt (nhdsWithin 0 (Set.Ioi 0))
      change inverse limitChange limitInverse)
    (data : FinitePolynomialMatrixData ι)
    (frameExponent : Fin 4 → Nat) :
    FinitePolynomialValuationsNonnegative data frameExponent ↔
      ∃ candidate : Matrix4,
        Tendsto
          (movingConjugateFinitePolynomialTransport change inverse data
            frameExponent)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds candidate) := by
  rw [finitePolynomialValuationsNonnegative_iff_exists_finite_limit]
  simpa [movingConjugateFinitePolynomialTransport] using
    exists_finite_limit_movingConjugatePath_iff change inverse
      limitChange limitInverse hRegular
      (finitePolynomialTransportedMatrix data frameExponent)

end
end P0EFTJanusRegularMovingConjugateSingularFrameValuationCriterion4D
end JanusFormal
