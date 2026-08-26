import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFullBulkSpinCD10GlobalTangentBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaugeFixedTangentDenseRaccord4D

/-!
# Full bulk and smooth normal-boundary shared-metric tangent

The two existing tangent images share the diagonal metric slot, so they are
not combined as a direct sum.  Instead this file takes their linear pullback
over equality of the bulk metric pair with the diagonal boundary metric.  The
common metric is inserted once and the remaining normal displacement once.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAFullBulkSpinCD10NormalBoundarySharedMetricTangent4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaugeFixedTangentDenseRaccord4D
open P0EFTJanusProgramPGlobalCandidateANonSpinCBulkGlobalTangentBridge4D
open P0EFTJanusProgramPGlobalCandidateAFullBulkSpinCD10GlobalTangentBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

/-! ## The smooth normal-boundary image in the legacy global tangent -/

/-- Canonical zero-nonminimal, zero-D10 realization of the smooth
normal-boundary core in `GlobalFieldTangent`. -/
def candidateANormalBoundarySmoothGlobalFieldTangentLinearMap
    (configuration : GlobalFieldConfiguration period hPeriod) :
    CandidateANormalBoundarySmoothCore period hPeriod →ₗ[Real]
      GlobalFieldTangent period hPeriod configuration :=
  (globalPhysicalFieldTangentZeroD10InclusionLinearMap
      period hPeriod).comp
    ((globalMinimalPhysicalTangentInclusionLinearMap
      period hPeriod configuration).comp
        (candidateANormalBoundarySmoothMinimalTangentLinearMap
          period hPeriod configuration))

@[simp]
theorem candidateANormalBoundarySmoothGlobalFieldTangent_metric
    (configuration : GlobalFieldConfiguration period hPeriod)
    (variation : CandidateANormalBoundarySmoothCore period hPeriod)
    (sector : Sector) :
    (GlobalFieldTangent.completeVariation period hPeriod
      (candidateANormalBoundarySmoothGlobalFieldTangentLinearMap
        period hPeriod configuration variation)).fullMetricPerturbation sector =
      variation.1 :=
  rfl

@[simp]
theorem candidateANormalBoundarySmoothGlobalFieldTangent_normal
    (configuration : GlobalFieldConfiguration period hPeriod)
    (variation : CandidateANormalBoundarySmoothCore period hPeriod)
    (sector : Sector) :
    (GlobalFieldTangent.completeVariation period hPeriod
      (candidateANormalBoundarySmoothGlobalFieldTangentLinearMap
        period hPeriod configuration variation)).normalDisplacement sector =
      variation.2 :=
  rfl

/-- The global-tangent normal image is exactly the physical shadow of the
existing gauge-fixed image. -/
@[simp]
theorem candidateANormalBoundarySmoothGlobalFieldTangent_gaugeFixed_compatibility
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (variation : CandidateANormalBoundarySmoothCore period hPeriod) :
    candidateANormalBoundarySmoothGlobalFieldTangentLinearMap
        period hPeriod configuration.physical variation =
      globalPhysicalFieldTangentZeroD10InclusionLinearMap period hPeriod
        (globalMinimalPhysicalTangentInclusionLinearMap period hPeriod
          configuration.physical
          (globalGaugeFixedPhysicalTangentPhysicalProjectionLinearMap
            period hPeriod configuration
            (candidateANormalBoundarySmoothGaugeFixedTangentLinearMap
              period hPeriod configuration variation))) :=
  rfl

/-- Forget the already shared metric and retain only the genuinely new normal
displacement coordinate. -/
def candidateANormalBoundaryPureNormalSmoothLinearMap :
    CandidateANormalBoundarySmoothCore period hPeriod →ₗ[Real]
      CandidateANormalBoundarySmoothCore period hPeriod where
  toFun variation := (0, variation.2)
  map_add' _ _ := by
    apply Prod.ext
    · simp
    · rfl
  map_smul' scalar _ := by
    apply Prod.ext
    · simp
    · rfl

/-! ## Intersection audit -/

@[simp]
theorem globalCandidateAFullBulkSpinCD10GlobalFieldTangent_normal
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis)
    (sector : Sector) :
    (GlobalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullBulkSpinCD10GlobalFieldTangentLinearMap
        period hPeriod data analysis core)).normalDisplacement sector = 0 := by
  change
    (GlobalFieldTangent.completeVariation period hPeriod
          (globalCandidateANonSpinCPhysicalBulkGlobalFieldTangentLinearMap
            period hPeriod data analysis core.1)).normalDisplacement sector +
        0 + 0 = 0
  simp [globalCandidateANonSpinCPhysicalBulkGlobalFieldTangentLinearMap,
    globalCandidateANonSpinCPhysicalBulkMinimalTangentLinearMap]
  simp [GlobalFieldTangent.completeVariation,
    globalPhysicalFieldTangentZeroD10InclusionLinearMap,
    globalMinimalPhysicalTangentInclusionLinearMap]
  change
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
          (globalMetricPerturbationMinimalPhysicalTangentLinearMap
            period hPeriod configuration core.1.1).1).normalDisplacement sector +
      (GlobalPhysicalFieldTangent.completeVariation period hPeriod
          (globalCandidateAPairedGaugePotentialMinimalTangentLinearMap
            period hPeriod data core.1.2.1).1).normalDisplacement sector +
      (GlobalPhysicalFieldTangent.completeVariation period hPeriod
          (extendedLLMinimalTangentLinearMap
            period hPeriod analysis core.1.2.2).1).normalDisplacement sector = 0
  change 0 + 0 + 0 = 0
  simp

/-- Equality of a full-bulk image with a normal-boundary image forces the
bulk metric pair to be the diagonal boundary metric. -/
theorem fullBulk_eq_normalBoundary_forces_metric_agreement
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (bulk : GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis)
    (boundary : CandidateANormalBoundarySmoothCore period hPeriod)
    (hEqual :
      globalCandidateAFullBulkSpinCD10GlobalFieldTangentLinearMap
          period hPeriod data analysis bulk =
        candidateANormalBoundarySmoothGlobalFieldTangentLinearMap
          period hPeriod configuration boundary) :
    bulk.1.1 = fun _ ↦ boundary.1 := by
  have hMetric := congrArg
    (fun tangent : GlobalFieldTangent period hPeriod configuration ↦
      (tangent.completeVariation period hPeriod).fullMetricPerturbation) hEqual
  funext sector
  have hSector := congrFun hMetric sector
  simpa only [globalCandidateAFullBulkSpinCD10GlobalFieldTangent_metric,
    candidateANormalBoundarySmoothGlobalFieldTangent_metric] using hSector

/-- The same equality forces the boundary-only normal displacement to vanish;
this is the second obstruction to a direct-sum claim. -/
theorem fullBulk_eq_normalBoundary_forces_normal_zero
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (bulk : GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis)
    (boundary : CandidateANormalBoundarySmoothCore period hPeriod)
    (hEqual :
      globalCandidateAFullBulkSpinCD10GlobalFieldTangentLinearMap
          period hPeriod data analysis bulk =
        candidateANormalBoundarySmoothGlobalFieldTangentLinearMap
          period hPeriod configuration boundary) :
    boundary.2 = 0 := by
  have hNormal := congrArg
    (fun tangent : GlobalFieldTangent period hPeriod configuration ↦
      (tangent.completeVariation period hPeriod).normalDisplacement
        Sector.plus) hEqual
  simpa only [globalCandidateAFullBulkSpinCD10GlobalFieldTangent_normal,
    candidateANormalBoundarySmoothGlobalFieldTangent_normal] using hNormal.symm

/-! ## Linear pullback on the shared metric -/

def globalCandidateAFullBulkSpinCD10MetricLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis →ₗ[Real]
      GlobalMetricPerturbationPair period hPeriod where
  toFun core := core.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def candidateANormalBoundaryDiagonalMetricLinearMap :
    CandidateANormalBoundarySmoothCore period hPeriod →ₗ[Real]
      GlobalMetricPerturbationPair period hPeriod where
  toFun variation := fun _ ↦ variation.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Difference of the two metric presentations.  Its kernel is the linear
pullback, avoiding any assertion that the two tangent images are disjoint. -/
def globalCandidateAFullBulkSpinCD10NormalBoundaryMetricDisagreementLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    (GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis ×
        CandidateANormalBoundarySmoothCore period hPeriod) →ₗ[Real]
      GlobalMetricPerturbationPair period hPeriod :=
  (globalCandidateAFullBulkSpinCD10MetricLinearMap
      period hPeriod analysis).comp
      (LinearMap.fst Real
        (GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis)
        (CandidateANormalBoundarySmoothCore period hPeriod)) -
    (candidateANormalBoundaryDiagonalMetricLinearMap period hPeriod).comp
      (LinearMap.snd Real
        (GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis)
        (CandidateANormalBoundarySmoothCore period hPeriod))

/-- Full bulk plus smooth normal-boundary data with one common metric. -/
abbrev GlobalCandidateAFullBulkSpinCD10NormalBoundarySharedMetricCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  LinearMap.ker
    (globalCandidateAFullBulkSpinCD10NormalBoundaryMetricDisagreementLinearMap
      period hPeriod analysis)

theorem globalCandidateAFullBulkSpinCD10NormalBoundarySharedMetric_agreement
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullBulkSpinCD10NormalBoundarySharedMetricCore
      period hPeriod analysis) :
    core.1.1.1.1 = fun _ ↦ core.1.2.1 := by
  have hAgreement := core.2
  change core.1.1.1.1 - (fun _ ↦ core.1.2.1) = 0 at hAgreement
  exact sub_eq_zero.mp hAgreement

/-- Insert the common metric through the full-bulk map, and add only the
normal displacement from the boundary map. -/
def globalCandidateAFullBulkSpinCD10NormalBoundarySharedMetricAmbientLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    (GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis ×
        CandidateANormalBoundarySmoothCore period hPeriod) →ₗ[Real]
      GlobalFieldTangent period hPeriod configuration :=
  (globalCandidateAFullBulkSpinCD10GlobalFieldTangentLinearMap
      period hPeriod data analysis).comp
      (LinearMap.fst Real
        (GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis)
        (CandidateANormalBoundarySmoothCore period hPeriod)) +
    ((candidateANormalBoundarySmoothGlobalFieldTangentLinearMap
        period hPeriod configuration).comp
      (candidateANormalBoundaryPureNormalSmoothLinearMap
        period hPeriod)).comp
      (LinearMap.snd Real
        (GlobalCandidateAFullBulkSpinCD10Core period hPeriod analysis)
        (CandidateANormalBoundarySmoothCore period hPeriod))

/-- Honest shared-metric realization in the common global tangent. -/
def globalCandidateAFullBulkSpinCD10NormalBoundarySharedMetricLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateAFullBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis →ₗ[Real]
      GlobalFieldTangent period hPeriod configuration :=
  (globalCandidateAFullBulkSpinCD10NormalBoundarySharedMetricAmbientLinearMap
      period hPeriod data analysis).comp
    (LinearMap.ker
      (globalCandidateAFullBulkSpinCD10NormalBoundaryMetricDisagreementLinearMap
        period hPeriod analysis)).subtype

@[simp]
theorem globalCandidateAFullBulkSpinCD10NormalBoundarySharedMetric_metric
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullBulkSpinCD10NormalBoundarySharedMetricCore
      period hPeriod analysis) :
    (GlobalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullBulkSpinCD10NormalBoundarySharedMetricLinearMap
        period hPeriod data analysis core)).fullMetricPerturbation =
      core.1.1.1.1 := by
  funext sector
  simp [globalCandidateAFullBulkSpinCD10NormalBoundarySharedMetricLinearMap,
    globalCandidateAFullBulkSpinCD10NormalBoundarySharedMetricAmbientLinearMap,
    candidateANormalBoundaryPureNormalSmoothLinearMap]
  change
    (GlobalFieldTangent.completeVariation period hPeriod
          (globalCandidateAFullBulkSpinCD10GlobalFieldTangentLinearMap
            period hPeriod data analysis core.1.1)).fullMetricPerturbation
          sector +
        (GlobalFieldTangent.completeVariation period hPeriod
          (candidateANormalBoundarySmoothGlobalFieldTangentLinearMap
            period hPeriod configuration (0, core.1.2.2)
          )).fullMetricPerturbation sector = core.1.1.1.1 sector
  rw [globalCandidateAFullBulkSpinCD10GlobalFieldTangent_metric,
    candidateANormalBoundarySmoothGlobalFieldTangent_metric]
  simp

@[simp]
theorem globalCandidateAFullBulkSpinCD10NormalBoundarySharedMetric_normal
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateAFullBulkSpinCD10NormalBoundarySharedMetricCore
      period hPeriod analysis)
    (sector : Sector) :
    (GlobalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullBulkSpinCD10NormalBoundarySharedMetricLinearMap
        period hPeriod data analysis core)).normalDisplacement sector =
      core.1.2.2 := by
  simp [globalCandidateAFullBulkSpinCD10NormalBoundarySharedMetricLinearMap,
    globalCandidateAFullBulkSpinCD10NormalBoundarySharedMetricAmbientLinearMap,
    candidateANormalBoundaryPureNormalSmoothLinearMap]
  change
    (GlobalFieldTangent.completeVariation period hPeriod
          (globalCandidateAFullBulkSpinCD10GlobalFieldTangentLinearMap
            period hPeriod data analysis core.1.1)).normalDisplacement sector +
        (GlobalFieldTangent.completeVariation period hPeriod
          (candidateANormalBoundarySmoothGlobalFieldTangentLinearMap
            period hPeriod configuration (0, core.1.2.2)
          )).normalDisplacement sector = core.1.2.2
  rw [globalCandidateAFullBulkSpinCD10GlobalFieldTangent_normal,
    candidateANormalBoundarySmoothGlobalFieldTangent_normal]
  simp

theorem globalCandidateAFullBulkSpinCD10NormalBoundarySharedMetric_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective
      (globalCandidateAFullBulkSpinCD10NormalBoundarySharedMetricLinearMap
        period hPeriod data analysis) := by
  intro first second hEqual
  have hNormal := congrArg
    (fun tangent : GlobalFieldTangent period hPeriod configuration ↦
      (tangent.completeVariation period hPeriod).normalDisplacement
        Sector.plus) hEqual
  simp only
    [globalCandidateAFullBulkSpinCD10NormalBoundarySharedMetric_normal]
    at hNormal
  have hPureCore :
      ((0, first.1.2.2) : CandidateANormalBoundarySmoothCore period hPeriod) =
        (0, second.1.2.2) :=
    Prod.ext rfl hNormal
  have hPureImage := congrArg
    (candidateANormalBoundarySmoothGlobalFieldTangentLinearMap
      period hPeriod configuration) hPureCore
  change
    globalCandidateAFullBulkSpinCD10GlobalFieldTangentLinearMap
          period hPeriod data analysis first.1.1 +
        candidateANormalBoundarySmoothGlobalFieldTangentLinearMap
          period hPeriod configuration (0, first.1.2.2) =
      globalCandidateAFullBulkSpinCD10GlobalFieldTangentLinearMap
          period hPeriod data analysis second.1.1 +
        candidateANormalBoundarySmoothGlobalFieldTangentLinearMap
          period hPeriod configuration (0, second.1.2.2) at hEqual
  rw [hPureImage] at hEqual
  have hBulk : first.1.1 = second.1.1 :=
    globalCandidateAFullBulkSpinCD10GlobalFieldTangent_injective
      period hPeriod data analysis (add_right_cancel hEqual)
  have hFirstAgreement :=
    globalCandidateAFullBulkSpinCD10NormalBoundarySharedMetric_agreement
      period hPeriod analysis first
  have hSecondAgreement :=
    globalCandidateAFullBulkSpinCD10NormalBoundarySharedMetric_agreement
      period hPeriod analysis second
  have hMetric : first.1.2.1 = second.1.2.1 := by
    calc
      first.1.2.1 = first.1.1.1.1 Sector.plus :=
        (congrFun hFirstAgreement Sector.plus).symm
      _ = second.1.1.1.1 Sector.plus :=
        congrArg (fun bulk ↦ bulk.1.1 Sector.plus) hBulk
      _ = second.1.2.1 :=
        congrFun hSecondAgreement Sector.plus
  apply Subtype.ext
  exact Prod.ext hBulk (Prod.ext hMetric hNormal)

end
end P0EFTJanusProgramPGlobalCandidateAFullBulkSpinCD10NormalBoundarySharedMetricTangent4D
end JanusFormal
