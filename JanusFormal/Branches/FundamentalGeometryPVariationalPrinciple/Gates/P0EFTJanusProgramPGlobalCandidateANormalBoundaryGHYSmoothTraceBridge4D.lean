import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D

variable (period : Real) (hPeriod : period ≠ 0)

theorem candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation_apply_mul
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (current : Prod
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) Real)
    (boundary : CutThroatBoundary period hPeriod) :
    candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation
        period hPeriod metric current boundary =
      Matrix.trace (normalBoundaryRealMatrixMul period hPeriod
        (fun row column =>
          candidateANormalBoundaryInducedRelativeLiftInverseFiberEvaluation
            period hPeriod metric current row column boundary)
        (fun row column =>
          candidateANormalBoundaryMetricUnitGaussRelativeEndomorphismMatrixFiberEvaluation
            period hPeriod metric current row column boundary)) := by
  rw [candidateANormalBoundaryMetricUnitGaussMeanCurvatureFiberEvaluation_apply_cut]
  exact congrArg Matrix.trace
    (candidateANormalBoundaryMatrixFieldEvaluationRingHom_mapMatrix_mul_cut
      period hPeriod boundary
      (candidateANormalBoundaryInducedRelativeLiftInverseFiberEvaluation
        period hPeriod metric current)
      (candidateANormalBoundaryMetricUnitGaussRelativeEndomorphismMatrixFiberEvaluation
        period hPeriod metric current))

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
