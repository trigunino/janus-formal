import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCTangentBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAFullBulkSpinCD10NormalBoundarySharedMetricTangent4D

/-!
# Full gauge-fixed bulk, SpinC, D10 and normal-boundary tangent

The gauge-fixed tangent has no D10 slot, so D10 is retained as an explicit
second target factor.  The bulk and normal-boundary sources share their
diagonal metric and are joined by a linear pullback, not a direct sum.  The
common metric is inserted once and only the normal displacement is added.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricTangent4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaugeFixedTangentDenseRaccord4D
open P0EFTJanusProgramPGlobalCandidateANonSpinCBulkGlobalTangentBridge4D
open P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCTangentBridge4D
open P0EFTJanusProgramPGlobalCandidateAFullBulkSpinCD10NormalBoundarySharedMetricTangent4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- Ambient source before imposing equality of the two metric presentations. -/
abbrev GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryAmbientCore
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  (GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod analysis ×
      ProgramPD10ModeHilbert4D
        (d10SpectralData period hPeriod
          configuration.physical.d10Completion)) ×
    CandidateANormalBoundarySmoothCore period hPeriod

/-- Gauge-fixed tangent together with the D10 factor that it cannot contain. -/
abbrev GlobalCandidateAFullGaugeFixedBulkSpinCD10TangentTarget
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :=
  GlobalGaugeFixedPhysicalFieldTangent period hPeriod configuration ×
    ProgramPD10ModeHilbert4D
      (d10SpectralData period hPeriod
        configuration.physical.d10Completion)

def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryBulkProjection
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryAmbientCore
        period hPeriod analysis →ₗ[Real]
      GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod analysis where
  toFun source := source.1.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryD10Projection
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryAmbientCore
        period hPeriod analysis →ₗ[Real]
      ProgramPD10ModeHilbert4D
        (d10SpectralData period hPeriod
          configuration.physical.d10Completion) where
  toFun source := source.1.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryNormalProjection
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryAmbientCore
        period hPeriod analysis →ₗ[Real]
      CandidateANormalBoundarySmoothCore period hPeriod where
  toFun source := source.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryBulkMetricLinearMap
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryAmbientCore
        period hPeriod analysis →ₗ[Real]
      GlobalMetricPerturbationPair period hPeriod where
  toFun source := source.1.1.1.1.metricPerturbation
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryDiagonalMetricLinearMap
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryAmbientCore
        period hPeriod analysis →ₗ[Real]
      GlobalMetricPerturbationPair period hPeriod where
  toFun source := fun _ ↦ source.2.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The pullback equation: bulk metric pair equals the diagonal boundary
metric. -/
def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryMetricDisagreementLinearMap
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryAmbientCore
        period hPeriod analysis →ₗ[Real]
      GlobalMetricPerturbationPair period hPeriod :=
  globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryBulkMetricLinearMap
      period hPeriod analysis -
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryDiagonalMetricLinearMap
      period hPeriod analysis

/-- Full gauge-fixed bulk, SpinC, D10 and boundary data with one common metric. -/
abbrev GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  LinearMap.ker
    (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryMetricDisagreementLinearMap
      period hPeriod analysis)

theorem globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetric_agreement
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core :
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis) :
    core.1.1.1.1.1.metricPerturbation = fun _ ↦ core.1.2.1 := by
  have hAgreement := core.2
  change core.1.1.1.1.1.metricPerturbation -
      (fun _ ↦ core.1.2.1) = 0 at hAgreement
  exact sub_eq_zero.mp hAgreement

/-- The tangent component: full gauge-fixed bulk plus only the pure normal
displacement. -/
def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryAmbientTangentLinearMap
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryAmbientCore
        period hPeriod analysis →ₗ[Real]
      GlobalGaugeFixedPhysicalFieldTangent period hPeriod configuration :=
  (globalCandidateAFullGaugeFixedBulkSpinCTangentLinearMap period hPeriod
      configuration data analysis).comp
      (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryBulkProjection
        period hPeriod analysis) +
    ((candidateANormalBoundarySmoothGaugeFixedTangentLinearMap
        period hPeriod configuration).comp
      (candidateANormalBoundaryPureNormalSmoothLinearMap
        period hPeriod)).comp
      (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryNormalProjection
        period hPeriod analysis)

/-- Ambient realization retaining D10 as its own exact coordinate. -/
def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryAmbientLinearMap
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryAmbientCore
        period hPeriod analysis →ₗ[Real]
      GlobalCandidateAFullGaugeFixedBulkSpinCD10TangentTarget
        period hPeriod configuration where
  toFun source :=
    (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryAmbientTangentLinearMap
        period hPeriod configuration data analysis source,
      globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryD10Projection
        period hPeriod analysis source)
  map_add' first second := by
    apply Prod.ext
    · exact
        (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryAmbientTangentLinearMap
          period hPeriod configuration data analysis).map_add first second
    · rfl
  map_smul' scalar source := by
    apply Prod.ext
    · exact
        (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryAmbientTangentLinearMap
          period hPeriod configuration data analysis).map_smul scalar source
    · rfl

/-- Honest realization of the shared-metric pullback. -/
def globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricLinearMap
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis →ₗ[Real]
      GlobalCandidateAFullGaugeFixedBulkSpinCD10TangentTarget
        period hPeriod configuration :=
  (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryAmbientLinearMap
      period hPeriod configuration data analysis).comp
    (LinearMap.ker
      (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryMetricDisagreementLinearMap
        period hPeriod analysis)).subtype

/-! ## Exact coordinate recovery -/

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCTangent_normal
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod analysis)
    (sector : Sector) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullGaugeFixedBulkSpinCTangentLinearMap period hPeriod
        configuration data analysis core).1.1).normalDisplacement sector = 0 := by
  change
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
        configuration data analysis core.1).1.1).normalDisplacement sector +
      0 = 0
  simp [globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap,
    GlobalPhysicalFieldTangent.completeVariation]
  change
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (diagonalDiffeomorphismGaugeFixedTangentLinearMap period hPeriod
        configuration core.1.1).1.1).normalDisplacement sector +
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap period hPeriod
        configuration data core.1.2.1).1.1).normalDisplacement sector +
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (extendedLLGaugeFixedTangentLinearMap period hPeriod configuration
        analysis core.1.2.2).1.1).normalDisplacement sector = 0
  change 0 + 0 + 0 = 0
  simp

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetric_metric
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core :
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricLinearMap
        period hPeriod configuration data analysis core).1.1.1
      ).fullMetricPerturbation = core.1.1.1.1.1.metricPerturbation := by
  change
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
        (globalCandidateAFullGaugeFixedBulkSpinCTangentLinearMap period hPeriod
          configuration data analysis core.1.1.1).1.1
      ).fullMetricPerturbation + 0 = _
  rw [globalCandidateAFullGaugeFixedBulkSpinCTangent_metric]
  simp

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetric_normal
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core :
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis)
    (sector : Sector) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricLinearMap
        period hPeriod configuration data analysis core).1.1.1
      ).normalDisplacement sector = core.1.2.2 := by
  simp [globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricLinearMap,
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryAmbientLinearMap,
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundaryAmbientTangentLinearMap,
    candidateANormalBoundaryPureNormalSmoothLinearMap]
  change
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullGaugeFixedBulkSpinCTangentLinearMap period hPeriod
        configuration data analysis core.1.1.1).1.1
      ).normalDisplacement sector +
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (candidateANormalBoundarySmoothGaugeFixedTangentLinearMap period hPeriod
        configuration (0, core.1.2.2)).1.1
      ).normalDisplacement sector = core.1.2.2
  rw [globalCandidateAFullGaugeFixedBulkSpinCTangent_normal,
    candidateANormalBoundarySmoothGaugeFixedTangent_normal]
  simp

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetric_gauge
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core :
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricLinearMap
        period hPeriod configuration data analysis core).1.1.1
      ).independent.gauge =
      globalCandidateAPairedGaugePotentialCoefficientLinearMap period hPeriod
        data core.1.1.1.1.2.1.potential := by
  change
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullGaugeFixedBulkSpinCTangentLinearMap period hPeriod
        configuration data analysis core.1.1.1).1.1).independent.gauge + 0 = _
  rw [globalCandidateAFullGaugeFixedBulkSpinCTangent_gauge]
  simp

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetric_llAuxMetric
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core :
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricLinearMap
        period hPeriod configuration data analysis core).1.1.1
      ).independent.llAuxMetric = core.1.1.1.1.2.2.1.1 := by
  change
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullGaugeFixedBulkSpinCTangentLinearMap period hPeriod
        configuration data analysis core.1.1.1).1.1).independent.llAuxMetric +
      0 = _
  rw [globalCandidateAFullGaugeFixedBulkSpinCTangent_llAuxMetric]
  simp

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetric_llMeasure
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core :
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricLinearMap
        period hPeriod configuration data analysis core).1.1.1
      ).independent.llMeasure = core.1.1.1.1.2.2.1.2 := by
  change
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullGaugeFixedBulkSpinCTangentLinearMap period hPeriod
        configuration data analysis core.1.1.1).1.1).independent.llMeasure +
      0 = _
  rw [globalCandidateAFullGaugeFixedBulkSpinCTangent_llMeasure]
  simp

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetric_llField
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core :
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricLinearMap
        period hPeriod configuration data analysis core).1.1.1
      ).independent.llField = core.1.1.1.1.2.2.2.toTest := by
  change
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullGaugeFixedBulkSpinCTangentLinearMap period hPeriod
        configuration data analysis core.1.1.1).1.1).independent.llField + 0 = _
  rw [globalCandidateAFullGaugeFixedBulkSpinCTangent_llField]
  simp

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetric_spinCMatter
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core :
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis) :
    (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricLinearMap
      period hPeriod configuration data analysis core).1.1.1.2 =
      programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
        core.1.1.1.2 := by
  change
    (globalCandidateAFullGaugeFixedBulkSpinCTangentLinearMap period hPeriod
      configuration data analysis core.1.1.1).1.1.2 + 0 = _
  rw [globalCandidateAFullGaugeFixedBulkSpinCTangent_spinCMatter]
  simp

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetric_abelian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core :
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis) :
    (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricLinearMap
      period hPeriod configuration data analysis core).1.2.abelian =
      core.1.1.1.1.2.1.nonminimal := by
  change
    (globalCandidateAFullGaugeFixedBulkSpinCTangentLinearMap period hPeriod
      configuration data analysis core.1.1.1).2.abelian + 0 = _
  rw [globalCandidateAFullGaugeFixedBulkSpinCTangent_abelian]
  simp

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetric_diffeomorphism
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core :
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis) :
    (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricLinearMap
      period hPeriod configuration data analysis core).1.2.diffeomorphism =
      core.1.1.1.1.1.nonminimal := by
  change
    (globalCandidateAFullGaugeFixedBulkSpinCTangentLinearMap period hPeriod
      configuration data analysis core.1.1.1).2.diffeomorphism + 0 = _
  rw [globalCandidateAFullGaugeFixedBulkSpinCTangent_diffeomorphism]
  simp

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetric_d10
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core :
      GlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricCore
        period hPeriod analysis) :
    (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricLinearMap
      period hPeriod configuration data analysis core).2 = core.1.1.2 :=
  rfl

theorem globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetric_injective
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Function.Injective
      (globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricLinearMap
        period hPeriod configuration data analysis) := by
  intro first second hEqual
  have hTangent := congrArg
    (fun target : GlobalCandidateAFullGaugeFixedBulkSpinCD10TangentTarget
      period hPeriod configuration ↦ target.1) hEqual
  have hD10 := congrArg
    (fun target : GlobalCandidateAFullGaugeFixedBulkSpinCD10TangentTarget
      period hPeriod configuration ↦ target.2) hEqual
  simp only
    [globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetric_d10]
    at hD10
  have hNormal := congrArg
    (fun tangent : GlobalGaugeFixedPhysicalFieldTangent period hPeriod
        configuration ↦
      (GlobalPhysicalFieldTangent.completeVariation period hPeriod
        tangent.1.1).normalDisplacement Sector.plus) hTangent
  simp only
    [globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetric_normal]
    at hNormal
  have hPureCore :
      ((0, first.1.2.2) : CandidateANormalBoundarySmoothCore period hPeriod) =
        (0, second.1.2.2) :=
    Prod.ext rfl hNormal
  have hPureImage := congrArg
    (candidateANormalBoundarySmoothGaugeFixedTangentLinearMap
      period hPeriod configuration) hPureCore
  change
    globalCandidateAFullGaugeFixedBulkSpinCTangentLinearMap period hPeriod
          configuration data analysis first.1.1.1 +
        candidateANormalBoundarySmoothGaugeFixedTangentLinearMap
          period hPeriod configuration (0, first.1.2.2) =
      globalCandidateAFullGaugeFixedBulkSpinCTangentLinearMap period hPeriod
          configuration data analysis second.1.1.1 +
        candidateANormalBoundarySmoothGaugeFixedTangentLinearMap
          period hPeriod configuration (0, second.1.2.2) at hTangent
  rw [hPureImage] at hTangent
  have hBulk : first.1.1.1 = second.1.1.1 :=
    globalCandidateAFullGaugeFixedBulkSpinCTangent_injective
      period hPeriod configuration data analysis (add_right_cancel hTangent)
  have hFirstAgreement :=
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetric_agreement
      period hPeriod analysis first
  have hSecondAgreement :=
    globalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetric_agreement
      period hPeriod analysis second
  have hMetric : first.1.2.1 = second.1.2.1 := by
    calc
      first.1.2.1 =
          first.1.1.1.1.1.metricPerturbation Sector.plus :=
        (congrFun hFirstAgreement Sector.plus).symm
      _ = second.1.1.1.1.1.metricPerturbation Sector.plus :=
        congrArg
          (fun bulk ↦ bulk.1.1.metricPerturbation Sector.plus) hBulk
      _ = second.1.2.1 :=
        congrFun hSecondAgreement Sector.plus
  apply Subtype.ext
  exact Prod.ext (Prod.ext hBulk hD10) (Prod.ext hMetric hNormal)

end
end P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCD10NormalBoundarySharedMetricTangent4D
end JanusFormal
