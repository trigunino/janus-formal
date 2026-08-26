import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaugeFixedTangentDenseRaccord4D

/-!
# Smooth normal-boundary range in the gauge-fixed tangent

The faithful smooth normal-boundary map defines an actual linear subspace of
the corrected gauge-fixed tangent.  On this range only, injectivity gives the
inverse needed to compare with the completed functional core.  The resulting
map into that core is faithful and dense.  No map from the completion back to
smooth fields is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaugeFixedSmoothTangentRange4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaugeFixedTangentDenseRaccord4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance boundaryCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance boundaryCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

/-- The genuine smooth normal-boundary directions already present in the
corrected gauge-fixed tangent. -/
abbrev CandidateANormalBoundaryGaugeFixedSmoothTangent
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :=
  LinearMap.range
    (candidateANormalBoundarySmoothGaugeFixedTangentLinearMap
      period hPeriod configuration)

/-- The smooth core is linearly equivalent to its actual tangent range. -/
def candidateANormalBoundaryGaugeFixedSmoothTangentEquiv
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    CandidateANormalBoundarySmoothCore period hPeriod ≃ₗ[Real]
      CandidateANormalBoundaryGaugeFixedSmoothTangent
        period hPeriod configuration :=
  LinearEquiv.ofInjective
    (candidateANormalBoundarySmoothGaugeFixedTangentLinearMap
      period hPeriod configuration)
    (candidateANormalBoundarySmoothGaugeFixedTangentLinearMap_injective
      period hPeriod configuration)

/-- Inclusion of the common smooth range into the full gauge-fixed tangent. -/
def candidateANormalBoundaryGaugeFixedSmoothTangentInclusion
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    CandidateANormalBoundaryGaugeFixedSmoothTangent
        period hPeriod configuration →ₗ[Real]
      GlobalGaugeFixedPhysicalFieldTangent period hPeriod configuration :=
  (LinearMap.range
    (candidateANormalBoundarySmoothGaugeFixedTangentLinearMap
      period hPeriod configuration)).subtype

/-- Realization of the common smooth tangent in the completed boundary core.
The inverse is used only on the actual smooth range. -/
def candidateANormalBoundaryGaugeFixedSmoothTangentToFunctionalCore
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    CandidateANormalBoundaryGaugeFixedSmoothTangent
        period hPeriod configuration →ₗ[Real]
      CandidateANormalBoundaryFunctionalCore period hPeriod metric :=
  (smoothToCandidateANormalBoundaryFunctionalCore
      period hPeriod metric).comp
    (candidateANormalBoundaryGaugeFixedSmoothTangentEquiv
      period hPeriod configuration).symm.toLinearMap

@[simp]
theorem candidateANormalBoundaryGaugeFixedSmoothTangentInclusion_smooth
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (variation : CandidateANormalBoundarySmoothCore period hPeriod) :
    candidateANormalBoundaryGaugeFixedSmoothTangentInclusion
        period hPeriod configuration
        (candidateANormalBoundaryGaugeFixedSmoothTangentEquiv
          period hPeriod configuration variation) =
      candidateANormalBoundarySmoothGaugeFixedTangentLinearMap
        period hPeriod configuration variation := by
  rfl

@[simp]
theorem candidateANormalBoundaryGaugeFixedSmoothTangentToFunctionalCore_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (variation : CandidateANormalBoundarySmoothCore period hPeriod) :
    candidateANormalBoundaryGaugeFixedSmoothTangentToFunctionalCore
        period hPeriod metric configuration
        (candidateANormalBoundaryGaugeFixedSmoothTangentEquiv
          period hPeriod configuration variation) =
      smoothToCandidateANormalBoundaryFunctionalCore
        period hPeriod metric variation := by
  simp [candidateANormalBoundaryGaugeFixedSmoothTangentToFunctionalCore]

theorem candidateANormalBoundaryGaugeFixedSmoothTangentToFunctionalCore_injective
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    Function.Injective
      (candidateANormalBoundaryGaugeFixedSmoothTangentToFunctionalCore
        period hPeriod metric configuration) :=
  (smoothToCandidateANormalBoundaryFunctionalCore_injective
      period hPeriod metric).comp
    (candidateANormalBoundaryGaugeFixedSmoothTangentEquiv
      period hPeriod configuration).symm.injective

theorem candidateANormalBoundaryGaugeFixedSmoothTangentToFunctionalCore_denseRange
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    DenseRange
      (candidateANormalBoundaryGaugeFixedSmoothTangentToFunctionalCore
        period hPeriod metric configuration) := by
  have hRange :
      Set.range
          (candidateANormalBoundaryGaugeFixedSmoothTangentToFunctionalCore
            period hPeriod metric configuration) =
        Set.range
          (smoothToCandidateANormalBoundaryFunctionalCore
            period hPeriod metric) := by
    ext value
    constructor
    · rintro ⟨tangent, rfl⟩
      exact ⟨
        (candidateANormalBoundaryGaugeFixedSmoothTangentEquiv
          period hPeriod configuration).symm tangent, rfl⟩
    · rintro ⟨variation, rfl⟩
      refine ⟨
        candidateANormalBoundaryGaugeFixedSmoothTangentEquiv
          period hPeriod configuration variation, ?_⟩
      exact
        candidateANormalBoundaryGaugeFixedSmoothTangentToFunctionalCore_smooth
          period hPeriod metric configuration variation
  rw [DenseRange, hRange]
  exact smoothToCandidateANormalBoundaryFunctionalCore_denseRange
    period hPeriod metric

/-- Honest common-domain checkpoint: the same smooth directions are faithful
in the full tangent and form a faithful dense domain of the boundary core. -/
theorem global_candidateA_normal_boundary_gauge_fixed_smooth_tangent_range
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    Function.Injective
        (candidateANormalBoundaryGaugeFixedSmoothTangentInclusion
          period hPeriod configuration) ∧
      Function.Injective
        (candidateANormalBoundaryGaugeFixedSmoothTangentToFunctionalCore
          period hPeriod metric configuration) ∧
      DenseRange
        (candidateANormalBoundaryGaugeFixedSmoothTangentToFunctionalCore
          period hPeriod metric configuration) :=
  ⟨Subtype.val_injective,
    candidateANormalBoundaryGaugeFixedSmoothTangentToFunctionalCore_injective
      period hPeriod metric configuration,
    candidateANormalBoundaryGaugeFixedSmoothTangentToFunctionalCore_denseRange
      period hPeriod metric configuration⟩

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaugeFixedSmoothTangentRange4D
end JanusFormal
