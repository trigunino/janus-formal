import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalMonomialMatrixValuationCriterion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFinitePolynomialMatrixValuationCriterion4D

/-! # Valuations in fixed conjugates of diagonal singular frames -/

namespace JanusFormal
namespace P0EFTJanusFixedConjugateSingularFrameValuationCriterion4D

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology
open P0EFTJanusGlobalMonomialMatrixValuationCriterion4D
open P0EFTJanusFinitePolynomialMatrixValuationCriterion4D

abbrev Matrix4 := P0EFTJanusGlobalMonomialMatrixValuationCriterion4D.Matrix4

/-- Transport in a singular diagonal frame, followed by a fixed change of
basis.  For non-diagonal `change`, this is a non-diagonal singular frame. -/
def fixedConjugateTransport
    (change inverse : Matrix4)
    (data : NonnegativeMonomialMatrixData)
    (frameExponent : Fin 4 → Nat) (t : Real) : Matrix4 :=
  change * transportedMatrix data frameExponent t * inverse

/-- Nonnegative active valuations give the conjugated finite limit. -/
theorem fixedConjugateTransport_tendsto_of_activeValuationsNonnegative
    (change inverse : Matrix4)
    (data : NonnegativeMonomialMatrixData)
    (frameExponent : Fin 4 → Nat)
    (hValuation : ActiveValuationsNonnegative data frameExponent) :
    Tendsto (fixedConjugateTransport change inverse data frameExponent)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (change * valuationLimit data frameExponent * inverse)) := by
  exact (tendsto_const_nhds.mul
      (transportedMatrix_tendsto_of_activeValuationsNonnegative
        data frameExponent hValuation)).mul tendsto_const_nhds

/-- A fixed invertible conjugation neither creates nor removes a finite
matrix limit. -/
theorem activeValuationsNonnegative_iff_exists_fixedConjugate_finite_limit
    (change inverse : Matrix4)
    (hLeftInverse : inverse * change = 1)
    (_hRightInverse : change * inverse = 1)
    (data : NonnegativeMonomialMatrixData)
    (frameExponent : Fin 4 → Nat) :
    ActiveValuationsNonnegative data frameExponent ↔
      ∃ candidate : Matrix4,
        Tendsto (fixedConjugateTransport change inverse data frameExponent)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds candidate) := by
  constructor
  · intro hValuation
    exact ⟨change * valuationLimit data frameExponent * inverse,
      fixedConjugateTransport_tendsto_of_activeValuationsNonnegative
        change inverse data frameExponent hValuation⟩
  · rintro ⟨candidate, hCandidate⟩
    have hBack : Tendsto
        (fun t => inverse *
          fixedConjugateTransport change inverse data frameExponent t * change)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (inverse * candidate * change)) :=
      (tendsto_const_nhds.mul hCandidate).mul tendsto_const_nhds
    have hOriginal : Tendsto (transportedMatrix data frameExponent)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (inverse * candidate * change)) := by
      apply hBack.congr'
      filter_upwards with t
      simp only [fixedConjugateTransport]
      calc
        inverse * (change * transportedMatrix data frameExponent t * inverse) *
              change =
            (inverse * change) * transportedMatrix data frameExponent t *
              (inverse * change) := by noncomm_ring
        _ = transportedMatrix data frameExponent t := by
          rw [hLeftInverse]
          simp
    exact (activeValuationsNonnegative_iff_exists_finite_limit
      data frameExponent).2 ⟨inverse * candidate * change, hOriginal⟩

/-- Fixed conjugation of a transported finite monomial sum. -/
def fixedConjugateFinitePolynomialTransport {ι : Type*}
    (change inverse : Matrix4)
    (data : FinitePolynomialMatrixData ι)
    (frameExponent : Fin 4 → Nat) (t : Real) : Matrix4 :=
  change * finitePolynomialTransportedMatrix data frameExponent t * inverse

/-- The exact finite-polynomial valuation criterion is invariant under every
fixed invertible conjugation. -/
theorem finitePolynomialValuationsNonnegative_iff_exists_fixedConjugate_finite_limit
    {ι : Type*}
    (change inverse : Matrix4)
    (hLeftInverse : inverse * change = 1)
    (_hRightInverse : change * inverse = 1)
    (data : FinitePolynomialMatrixData ι)
    (frameExponent : Fin 4 → Nat) :
    FinitePolynomialValuationsNonnegative data frameExponent ↔
      ∃ candidate : Matrix4,
        Tendsto
          (fixedConjugateFinitePolynomialTransport change inverse data
            frameExponent)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds candidate) := by
  constructor
  · intro hValuation
    refine ⟨change * finitePolynomialLimit data frameExponent * inverse, ?_⟩
    exact (tendsto_const_nhds.mul
      (finitePolynomialTransportedMatrix_tendsto
        data frameExponent hValuation)).mul tendsto_const_nhds
  · rintro ⟨candidate, hCandidate⟩
    have hBack : Tendsto
        (fun t => inverse *
          fixedConjugateFinitePolynomialTransport change inverse data
            frameExponent t * change)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (inverse * candidate * change)) :=
      (tendsto_const_nhds.mul hCandidate).mul tendsto_const_nhds
    have hOriginal : Tendsto
        (finitePolynomialTransportedMatrix data frameExponent)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (inverse * candidate * change)) := by
      apply hBack.congr'
      filter_upwards with t
      simp only [fixedConjugateFinitePolynomialTransport]
      calc
        inverse *
              (change * finitePolynomialTransportedMatrix data frameExponent t *
                inverse) * change =
            (inverse * change) *
              finitePolynomialTransportedMatrix data frameExponent t *
                (inverse * change) := by noncomm_ring
        _ = finitePolynomialTransportedMatrix data frameExponent t := by
          rw [hLeftInverse]
          simp
    exact (finitePolynomialValuationsNonnegative_iff_exists_finite_limit
      data frameExponent).2 ⟨inverse * candidate * change, hOriginal⟩

end
end P0EFTJanusFixedConjugateSingularFrameValuationCriterion4D
end JanusFormal
