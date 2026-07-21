import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusActiveAsymptoticMatrixValuationCriterion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularMovingConjugateSingularFrameValuationCriterion4D

/-! # Active asymptotic valuations in regular moving outer frames -/

namespace JanusFormal
namespace P0EFTJanusRegularMovingActiveAsymptoticMatrixValuationCriterion4D

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology
open P0EFTJanusRegularMovingSimilarityZeroOverZero4D

abbrev Matrix4 := P0EFTJanusRegularMovingSimilarityZeroOverZero4D.Matrix4
abbrev ActiveAsymptoticMatrixData :=
  P0EFTJanusActiveAsymptoticMatrixValuationCriterion4D.ActiveAsymptoticMatrixData

def movingConjugateActiveAsymptoticTransport
    (change inverse : Real → Matrix4)
    (data : ActiveAsymptoticMatrixData)
    (frameExponent : Fin 4 → Nat) : Real → Matrix4 :=
  P0EFTJanusRegularMovingConjugateSingularFrameValuationCriterion4D.movingConjugatePath
    change inverse
    (P0EFTJanusActiveAsymptoticMatrixValuationCriterion4D.transportedMatrix
      data frameExponent)

/-- Explicit conjugated limit for active and inactive entries. -/
theorem movingConjugateActiveAsymptoticTransport_tendsto
    (change inverse : Real → Matrix4)
    (limitChange limitInverse : Matrix4)
    (hRegular : RegularMovingSimilarityAt (nhdsWithin 0 (Set.Ioi 0))
      change inverse limitChange limitInverse)
    (data : ActiveAsymptoticMatrixData)
    (frameExponent : Fin 4 → Nat)
    (hValuation :
      P0EFTJanusActiveAsymptoticMatrixValuationCriterion4D.ActiveValuationsNonnegative
        data frameExponent) :
    Tendsto
        (movingConjugateActiveAsymptoticTransport change inverse data frameExponent)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (limitChange *
          P0EFTJanusActiveAsymptoticMatrixValuationCriterion4D.valuationLimit
            data frameExponent * limitInverse)) :=
  (hRegular.change_tendsto.mul
    (P0EFTJanusActiveAsymptoticMatrixValuationCriterion4D.transportedMatrix_tendsto
      data frameExponent hValuation)).mul hRegular.inverse_tendsto

/-- A regular moving outer frame preserves and reflects the exact active
asymptotic valuation criterion. -/
theorem activeValuationsNonnegative_iff_exists_movingConjugate_finite_limit
    (change inverse : Real → Matrix4)
    (limitChange limitInverse : Matrix4)
    (hRegular : RegularMovingSimilarityAt (nhdsWithin 0 (Set.Ioi 0))
      change inverse limitChange limitInverse)
    (data : ActiveAsymptoticMatrixData)
    (frameExponent : Fin 4 → Nat) :
    P0EFTJanusActiveAsymptoticMatrixValuationCriterion4D.ActiveValuationsNonnegative
        data frameExponent ↔
      ∃ candidate : Matrix4,
        Tendsto
          (movingConjugateActiveAsymptoticTransport change inverse data frameExponent)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds candidate) := by
  rw [P0EFTJanusActiveAsymptoticMatrixValuationCriterion4D.activeValuationsNonnegative_iff_exists_finite_limit]
  simpa [movingConjugateActiveAsymptoticTransport] using
    P0EFTJanusRegularMovingConjugateSingularFrameValuationCriterion4D.exists_finite_limit_movingConjugatePath_iff
      change inverse limitChange limitInverse hRegular
      (P0EFTJanusActiveAsymptoticMatrixValuationCriterion4D.transportedMatrix
        data frameExponent)

end
end P0EFTJanusRegularMovingActiveAsymptoticMatrixValuationCriterion4D
end JanusFormal
