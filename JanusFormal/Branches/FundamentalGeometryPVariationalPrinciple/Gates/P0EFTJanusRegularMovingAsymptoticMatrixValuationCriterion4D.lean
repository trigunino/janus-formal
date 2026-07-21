import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusAsymptoticMatrixValuationCriterion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularMovingConjugateSingularFrameValuationCriterion4D

/-! # Leading-asymptotic valuations in regularly moving singular frames -/

namespace JanusFormal
namespace P0EFTJanusRegularMovingAsymptoticMatrixValuationCriterion4D

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology
open P0EFTJanusRegularMovingSimilarityZeroOverZero4D

abbrev Matrix4 := P0EFTJanusRegularMovingSimilarityZeroOverZero4D.Matrix4
abbrev AsymptoticMatrixData :=
  P0EFTJanusAsymptoticMatrixValuationCriterion4D.AsymptoticMatrixData

def movingConjugateAsymptoticTransport
    (change inverse : Real → Matrix4)
    (data : AsymptoticMatrixData)
    (frameExponent : Fin 4 → Nat) : Real → Matrix4 :=
  P0EFTJanusRegularMovingConjugateSingularFrameValuationCriterion4D.movingConjugatePath
    change inverse
    (P0EFTJanusAsymptoticMatrixValuationCriterion4D.transportedMatrix
      data frameExponent)

/-- Exact limit after a regular moving outer conjugation. -/
theorem movingConjugateAsymptoticTransport_tendsto
    (change inverse : Real → Matrix4)
    (limitChange limitInverse : Matrix4)
    (hRegular : RegularMovingSimilarityAt (nhdsWithin 0 (Set.Ioi 0))
      change inverse limitChange limitInverse)
    (data : AsymptoticMatrixData)
    (frameExponent : Fin 4 → Nat)
    (hValuation :
      P0EFTJanusAsymptoticMatrixValuationCriterion4D.ValuationsNonnegative
        data frameExponent) :
    Tendsto
        (movingConjugateAsymptoticTransport change inverse data frameExponent)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (limitChange *
          P0EFTJanusAsymptoticMatrixValuationCriterion4D.valuationLimit
            data frameExponent * limitInverse)) :=
  (hRegular.change_tendsto.mul
    (P0EFTJanusAsymptoticMatrixValuationCriterion4D.transportedMatrix_tendsto
      data frameExponent hValuation)).mul hRegular.inverse_tendsto

/-- The exact asymptotic valuation criterion is invariant under every regular
moving outer frame whose matrix and inverse converge. -/
theorem valuationsNonnegative_iff_exists_movingConjugate_finite_limit
    (change inverse : Real → Matrix4)
    (limitChange limitInverse : Matrix4)
    (hRegular : RegularMovingSimilarityAt (nhdsWithin 0 (Set.Ioi 0))
      change inverse limitChange limitInverse)
    (data : AsymptoticMatrixData)
    (frameExponent : Fin 4 → Nat) :
    P0EFTJanusAsymptoticMatrixValuationCriterion4D.ValuationsNonnegative
        data frameExponent ↔
      ∃ candidate : Matrix4,
        Tendsto
          (movingConjugateAsymptoticTransport change inverse data frameExponent)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds candidate) := by
  rw [P0EFTJanusAsymptoticMatrixValuationCriterion4D.valuationsNonnegative_iff_exists_finite_limit]
  simpa [movingConjugateAsymptoticTransport] using
    P0EFTJanusRegularMovingConjugateSingularFrameValuationCriterion4D.exists_finite_limit_movingConjugatePath_iff
      change inverse limitChange limitInverse hRegular
      (P0EFTJanusAsymptoticMatrixValuationCriterion4D.transportedMatrix
        data frameExponent)

end
end P0EFTJanusRegularMovingAsymptoticMatrixValuationCriterion4D
end JanusFormal
