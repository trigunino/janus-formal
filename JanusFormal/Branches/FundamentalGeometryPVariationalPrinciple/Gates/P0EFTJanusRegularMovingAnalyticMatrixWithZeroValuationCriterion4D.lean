import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusAnalyticMatrixWithZeroValuationCriterion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusRegularMovingActiveAsymptoticMatrixValuationCriterion4D

/-! # Analytic valuations with zero entries in regular moving outer frames -/

namespace JanusFormal
namespace P0EFTJanusRegularMovingAnalyticMatrixWithZeroValuationCriterion4D

set_option autoImplicit false
noncomputable section

open Filter
open scoped Topology
open P0EFTJanusRegularMovingSimilarityZeroOverZero4D

abbrev Matrix4 := P0EFTJanusRegularMovingSimilarityZeroOverZero4D.Matrix4
abbrev AnalyticMatrixData :=
  P0EFTJanusAnalyticMatrixWithZeroValuationCriterion4D.AnalyticMatrixData

def movingConjugateAnalyticTransport
    (change inverse : Real → Matrix4)
    (data : AnalyticMatrixData)
    (frameExponent : Fin 4 → Nat) : Real → Matrix4 :=
  P0EFTJanusRegularMovingActiveAsymptoticMatrixValuationCriterion4D.movingConjugateActiveAsymptoticTransport change inverse
      data.toActiveAsymptoticMatrixData frameExponent

/-- Explicit conjugated limit, including inactive zero entries. -/
theorem movingConjugateAnalyticTransport_tendsto
    (change inverse : Real → Matrix4)
    (limitChange limitInverse : Matrix4)
    (hRegular : RegularMovingSimilarityAt (nhdsWithin 0 (Set.Ioi 0))
      change inverse limitChange limitInverse)
    (data : AnalyticMatrixData)
    (frameExponent : Fin 4 → Nat)
    (hValuation :
      P0EFTJanusAnalyticMatrixWithZeroValuationCriterion4D.ActiveValuationsNonnegative
        data frameExponent) :
    Tendsto
        (movingConjugateAnalyticTransport change inverse data frameExponent)
        (nhdsWithin 0 (Set.Ioi 0))
        (nhds (limitChange *
          P0EFTJanusAnalyticMatrixWithZeroValuationCriterion4D.valuationLimit
            data frameExponent * limitInverse)) :=
  P0EFTJanusRegularMovingActiveAsymptoticMatrixValuationCriterion4D.movingConjugateActiveAsymptoticTransport_tendsto change inverse
      limitChange limitInverse hRegular data.toActiveAsymptoticMatrixData
      frameExponent hValuation

/-- Regular moving outer conjugation preserves and reflects the exact active
analytic valuation criterion. -/
theorem activeValuationsNonnegative_iff_exists_movingConjugate_finite_limit
    (change inverse : Real → Matrix4)
    (limitChange limitInverse : Matrix4)
    (hRegular : RegularMovingSimilarityAt (nhdsWithin 0 (Set.Ioi 0))
      change inverse limitChange limitInverse)
    (data : AnalyticMatrixData)
    (frameExponent : Fin 4 → Nat) :
    P0EFTJanusAnalyticMatrixWithZeroValuationCriterion4D.ActiveValuationsNonnegative
        data frameExponent ↔
      ∃ candidate : Matrix4,
        Tendsto
          (movingConjugateAnalyticTransport change inverse data frameExponent)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds candidate) := by
  exact P0EFTJanusRegularMovingActiveAsymptoticMatrixValuationCriterion4D.activeValuationsNonnegative_iff_exists_movingConjugate_finite_limit
      change inverse limitChange limitInverse hRegular
      data.toActiveAsymptoticMatrixData frameExponent

end
end P0EFTJanusRegularMovingAnalyticMatrixWithZeroValuationCriterion4D
end JanusFormal
