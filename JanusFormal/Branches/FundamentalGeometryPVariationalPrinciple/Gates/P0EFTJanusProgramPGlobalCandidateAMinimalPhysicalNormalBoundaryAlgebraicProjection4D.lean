import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaugeFixedTangentDenseRaccord4D

/-!
# Algebraic normal-boundary projection of the minimal physical tangent

The metric and normal slots of a chosen Program-P sector determine the smooth
normal-boundary core.  Its completed-core image is canonical after that sector
choice.  The independent real graph parameter remains an explicit linear map.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalNormalBoundaryAlgebraicProjection4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusCompleteVariationModuleCore4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaugeFixedTangentDenseRaccord4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev MinimalTangent
    (configuration : GlobalFieldConfiguration period hPeriod) :=
  GlobalMinimalPhysicalFieldTangent period hPeriod configuration

/-- Extract the smooth metric-normal pair of one Program-P sector. -/
def globalMinimalPhysicalNormalBoundarySmoothCoreProjectionLinearMap
    (configuration : GlobalFieldConfiguration period hPeriod)
    (sector : Sector) :
    MinimalTangent period hPeriod configuration →ₗ[Real]
      CandidateANormalBoundarySmoothCore period hPeriod where
  toFun variation :=
    ((GlobalPhysicalFieldTangent.completeVariation period hPeriod
        variation.1).fullMetricPerturbation sector,
      (GlobalPhysicalFieldTangent.completeVariation period hPeriod
        variation.1).normalDisplacement sector)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Complete the extracted smooth pair in the normal-boundary functional core. -/
def globalMinimalPhysicalNormalBoundaryFunctionalCoreProjectionLinearMap
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (configuration : GlobalFieldConfiguration period hPeriod)
    (sector : Sector) :
    MinimalTangent period hPeriod configuration →ₗ[Real]
      CandidateANormalBoundaryFunctionalCore period hPeriod metric :=
  (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric).comp
    (globalMinimalPhysicalNormalBoundarySmoothCoreProjectionLinearMap
      period hPeriod configuration sector)

/-- Add an explicitly supplied real graph parameter to the completed core.
No canonical parameter or same-action assertion is introduced here. -/
def globalMinimalPhysicalNormalBoundaryProductLinearMap
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (configuration : GlobalFieldConfiguration period hPeriod)
    (sector : Sector)
    (parameterMap : MinimalTangent period hPeriod configuration →ₗ[Real] Real) :
    MinimalTangent period hPeriod configuration →ₗ[Real]
      CandidateANormalBoundaryFunctionalCore period hPeriod metric × Real :=
  (globalMinimalPhysicalNormalBoundaryFunctionalCoreProjectionLinearMap
      period hPeriod metric configuration sector).prod parameterMap

@[simp]
theorem globalMinimalPhysicalNormalBoundaryProductLinearMap_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (configuration : GlobalFieldConfiguration period hPeriod)
    (sector : Sector)
    (parameterMap : MinimalTangent period hPeriod configuration →ₗ[Real] Real)
    (variation : MinimalTangent period hPeriod configuration) :
    globalMinimalPhysicalNormalBoundaryProductLinearMap period hPeriod metric
        configuration sector parameterMap variation =
      (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (globalMinimalPhysicalNormalBoundarySmoothCoreProjectionLinearMap
            period hPeriod configuration sector variation),
        parameterMap variation) := by
  rfl

/-- Sector extraction retracts the diagonal smooth normal-boundary insertion. -/
@[simp]
theorem globalMinimalPhysicalNormalBoundarySmoothCoreProjection_leftInverse
    (configuration : GlobalFieldConfiguration period hPeriod)
    (sector : Sector)
    (variation : CandidateANormalBoundarySmoothCore period hPeriod) :
    globalMinimalPhysicalNormalBoundarySmoothCoreProjectionLinearMap
        period hPeriod configuration sector
        (candidateANormalBoundarySmoothMinimalTangentLinearMap
          period hPeriod configuration variation) =
      variation := by
  rfl

/-- On the diagonal smooth insertion, the completed projection is exactly the
existing faithful smooth completion. -/
@[simp]
theorem globalMinimalPhysicalNormalBoundaryFunctionalCoreProjection_diagonal
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (configuration : GlobalFieldConfiguration period hPeriod)
    (sector : Sector)
    (variation : CandidateANormalBoundarySmoothCore period hPeriod) :
    globalMinimalPhysicalNormalBoundaryFunctionalCoreProjectionLinearMap
        period hPeriod metric configuration sector
        (candidateANormalBoundarySmoothMinimalTangentLinearMap
          period hPeriod configuration variation) =
      smoothToCandidateANormalBoundaryFunctionalCore
        period hPeriod metric variation := by
  rfl

/-- Gate 323: every sector admits the algebraic metric-normal retraction; an
independent real parameter may then be paired with its completed image. -/
theorem global_candidateA_minimal_physical_normal_boundary_algebraic_projection_gate
    (configuration : GlobalFieldConfiguration period hPeriod)
    (sector : Sector) :
    Function.LeftInverse
      (globalMinimalPhysicalNormalBoundarySmoothCoreProjectionLinearMap
        period hPeriod configuration sector)
      (candidateANormalBoundarySmoothMinimalTangentLinearMap
        period hPeriod configuration) :=
  globalMinimalPhysicalNormalBoundarySmoothCoreProjection_leftInverse
    period hPeriod configuration sector

end
end P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalNormalBoundaryAlgebraicProjection4D
end JanusFormal
