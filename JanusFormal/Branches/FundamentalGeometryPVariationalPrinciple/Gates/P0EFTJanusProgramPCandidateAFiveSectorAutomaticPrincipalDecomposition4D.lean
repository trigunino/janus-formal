import Mathlib.Tactic
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPCandidateAFiveSectorSelfAdjointPrincipalResolution4D

/-!
# Automatic five-sector decomposition of the principal Hessian

The self-adjoint projection packet still stored the identity

`B(x,x) = sum diagonal blocks + sum ten symmetric cross blocks`.

For a bilinear form this identity is not analytic input.  It follows from the
resolution of the identity `sum_s P_s x = x`: expand the two arguments of
`B(sum_s P_s x, sum_t P_t x)` and regroup the twenty-five ordered terms into
five diagonal terms and ten unordered symmetric pairs.

This file removes that duplicated field.  The remaining principal data are the
genuine form, the five natural projections, five diagonal estimates and the
strict finite cross-norm inequality.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPCandidateAFiveSectorAutomaticPrincipalDecomposition4D

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

noncomputable section

open scoped BigOperators InnerProductSpace
open P0EFTJanusProgramPFiniteSelfAdjointProjectionResolution4D
open P0EFTJanusProgramPCandidateAFiveSectorPrincipalBlockDecomposition4D
open P0EFTJanusProgramPCandidateAFiveSectorSelfAdjointPrincipalResolution4D
open P0EFTJanusProgramPCandidateAFiveSectorSymmetricGarding4D
open P0EFTJanusProgramPCandidateAFiveSectorPairwiseGarding4D
open P0EFTJanusProgramPGlobalCandidateANamedZeroModeSectors4D
open P0EFTJanusProgramPCandidateAZeroModeSector4D

variable {E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace Real E]

/-- Principal Candidate-A data before storing any block-expansion identity. -/
structure CandidateAFiveSectorAutomaticPrincipalData where
  principalForm : E →L[Real] E →L[Real] Real
  principal_symmetric : ∀ first second,
    principalForm first second = principalForm second first
  resolution : FiniteSelfAdjointProjectionResolutionData
    (Sector := CandidateAZeroModeSector) (E := E)
  diagonalConstants : CandidateAFiveSectorDiagonalConstants
  diagonal_lower : ∀ sector vector,
    diagonalConstants.sectorConstant sector *
        ‖resolution.projection sector vector‖ ^ 2 ≤
      principalForm
        (resolution.projection sector vector)
        (resolution.projection sector vector)
  cross_sum_small :
    (∑ pair : CandidateACrossSectorPair,
      ‖candidateASectorSymmetricCrossForm principalForm resolution.projection
        pair‖) < diagonalConstants.sectorFloor

namespace CandidateAFiveSectorAutomaticPrincipalData

private theorem sector_univ :
    (Finset.univ : Finset CandidateAZeroModeSector) =
      { .metricDiffeomorphism, .abelianGauge, .primitiveSpinCMatter,
        .longitudinalLL, .boundaryFiniteBV } := by
  decide

private theorem crossPair_univ :
    (Finset.univ : Finset CandidateACrossSectorPair) =
      { .metricAbelian, .metricSpinC, .metricLL, .metricBoundary,
        .abelianSpinC, .abelianLL, .abelianBoundary,
        .spinCLL, .spinCBoundary, .llBoundary } := by
  decide

/-- Bilinearity and the five-sector resolution of the identity give the full
five-diagonal/ten-cross decomposition automatically. -/
theorem principal_decomposition
    (data : CandidateAFiveSectorAutomaticPrincipalData (E := E))
    (vector : E) :
    data.principalForm vector vector =
      (∑ sector : CandidateAZeroModeSector,
        data.principalForm
          (data.resolution.projection sector vector)
          (data.resolution.projection sector vector)) +
      ∑ pair : CandidateACrossSectorPair,
        candidateASectorSymmetricCrossForm data.principalForm
          data.resolution.projection pair vector vector := by
  classical
  let m := data.resolution.projection .metricDiffeomorphism vector
  let a := data.resolution.projection .abelianGauge vector
  let s := data.resolution.projection .primitiveSpinCMatter vector
  let l := data.resolution.projection .longitudinalLL vector
  let b := data.resolution.projection .boundaryFiniteBV vector
  have hsum : m + a + s + l + b = vector := by
    simpa [m, a, s, l, b, sector_univ, add_assoc] using
      data.resolution.sum_projection vector
  conv_lhs => rw [← hsum]
  simp only [map_add, ContinuousLinearMap.add_apply]
  simp [sector_univ, crossPair_univ, m, a, s, l, b,
    CandidateACrossSectorPair.first, CandidateACrossSectorPair.second,
    candidateASectorSymmetricCrossForm,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.bilinearComp_apply]
  ring

/-- Recover the previous principal-resolution packet, now with the block
identity generated rather than supplied. -/
def toSelfAdjointPrincipalResolution
    (data : CandidateAFiveSectorAutomaticPrincipalData (E := E)) :
    CandidateAFiveSectorSelfAdjointPrincipalResolutionData (E := E) where
  principalForm := data.principalForm
  principal_symmetric := data.principal_symmetric
  resolution := data.resolution
  diagonalConstants := data.diagonalConstants
  diagonal_lower := data.diagonal_lower
  cross_sum_small := data.cross_sum_small
  principal_decomposition := data.principal_decomposition

/-- Explicit principal margin. -/
def margin
    (data : CandidateAFiveSectorAutomaticPrincipalData (E := E)) : Real :=
  data.toSelfAdjointPrincipalResolution.margin

/-- Principal Gårding without a separately supplied block-decomposition
identity. -/
theorem candidateA_five_sector_automatic_principal_garding_gate
    (data : CandidateAFiveSectorAutomaticPrincipalData (E := E)) :
    0 < data.margin ∧
      ∀ vector : E,
        data.margin * ‖vector‖ ^ 2 ≤ data.principalForm vector vector :=
  data.toSelfAdjointPrincipalResolution
    |>.candidateA_five_sector_selfAdjoint_principal_resolution_garding_gate

end CandidateAFiveSectorAutomaticPrincipalData

end
end P0EFTJanusProgramPCandidateAFiveSectorAutomaticPrincipalDecomposition4D
end JanusFormal
