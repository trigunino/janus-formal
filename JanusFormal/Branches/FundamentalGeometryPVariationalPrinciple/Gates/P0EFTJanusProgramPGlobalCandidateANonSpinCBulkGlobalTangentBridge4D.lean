import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D

/-!
# Non-SpinC Candidate-A bulk realization in the global tangents

The diagonal diffeomorphism BRST, paired Abelian BRST and full LL smooth
factors form an honest pure subspace of the completed Candidate-A bulk graph.
Their smooth core embeds faithfully in the corrected gauge-fixed tangent.

The legacy `GlobalFieldTangent` has no typed nonminimal slots.  Its companion
map is therefore stated only on the physical zero-nonminimal core.  Both maps
preserve every displayed coordinate exactly and set only the explicitly
excluded SpinC/D10 coordinates to zero.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANonSpinCBulkGlobalTangentBridge4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalMetricTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D

variable (period : Real) (hPeriod : period ≠ 0)

/-! ## Pure non-SpinC graph core -/

/-- The three retained smooth factors of the diagonal extended bulk graph. -/
abbrev GlobalCandidateANonSpinCBulkSmoothCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  GlobalCandidateADiagonalDiffeomorphismBRSTState period hPeriod ×
    (GlobalPairedAbelianBRSTState period hPeriod ×
      GlobalFullLLSmooth period hPeriod analysis)

/-- Inclusion in the explicitly pure zero-SpinC subspace of the full smooth
bulk core. -/
def globalCandidateANonSpinCBulkCoreInclusionLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateANonSpinCBulkSmoothCore period hPeriod analysis →ₗ[Real]
      GlobalCandidateADiagonalExtendedBulkSmoothCore
        period hPeriod analysis where
  toFun core := (core.1, (core.2.1, (0, core.2.2)))
  map_add' first second := by
    ext <;> simp
  map_smul' scalar core := by
    ext <;> simp

theorem globalCandidateANonSpinCBulkCoreInclusion_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective
      (globalCandidateANonSpinCBulkCoreInclusionLinearMap
        period hPeriod analysis) := by
  intro first second hEqual
  change (first.1, (first.2.1, (0, first.2.2))) =
    (second.1, (second.2.1, (0, second.2.2))) at hEqual
  exact Prod.ext
    (congrArg
      (fun value : GlobalCandidateADiagonalExtendedBulkSmoothCore
        period hPeriod analysis => value.1) hEqual)
    (Prod.ext
      (congrArg (fun value => value.2.1) hEqual)
      (congrArg (fun value => value.2.2.2) hEqual))

/-- Faithful realization of the pure non-SpinC core in the existing completed
bulk graph. -/
def globalCandidateANonSpinCBulkSmoothEmbedding
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateANonSpinCBulkSmoothCore period hPeriod analysis →ₗ[Real]
      GlobalCandidateADiagonalExtendedBulkGraphHilbert period hPeriod metric
        massSquared data analysis :=
  (diagonalExtendedBulkSmoothEmbedding period hPeriod metric massSquared data
    analysis).comp
      (globalCandidateANonSpinCBulkCoreInclusionLinearMap
        period hPeriod analysis)

@[simp]
theorem globalCandidateANonSpinCBulkSmoothEmbedding_diffeomorphism
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateANonSpinCBulkSmoothCore period hPeriod analysis) :
    (globalCandidateANonSpinCBulkSmoothEmbedding period hPeriod metric
      massSquared data analysis core).1 =
      globalCandidateADiagonalDiffeomorphismOffShellSmoothEmbedding
        period hPeriod metric core.1 :=
  rfl

@[simp]
theorem globalCandidateANonSpinCBulkSmoothEmbedding_abelian
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateANonSpinCBulkSmoothCore period hPeriod analysis) :
    (globalCandidateANonSpinCBulkSmoothEmbedding period hPeriod metric
      massSquared data analysis core).2.1 =
      globalPairedAbelianOffShellSmoothEmbedding period hPeriod metric
        core.2.1 :=
  rfl

@[simp]
theorem globalCandidateANonSpinCBulkSmoothEmbedding_spinC
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateANonSpinCBulkSmoothCore period hPeriod analysis) :
    (globalCandidateANonSpinCBulkSmoothEmbedding period hPeriod metric
      massSquared data analysis core).2.2.1 =
      programPPrimitiveSpinCMatterGraphFiniteRealLinearMap period hPeriod
        massSquared 0 :=
  rfl

@[simp]
theorem globalCandidateANonSpinCBulkSmoothEmbedding_ll
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateANonSpinCBulkSmoothCore period hPeriod analysis) :
    (globalCandidateANonSpinCBulkSmoothEmbedding period hPeriod metric
      massSquared data analysis core).2.2.2 =
      globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis
        core.2.2 :=
  rfl

theorem globalCandidateANonSpinCBulkSmoothEmbedding_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (metric : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (massSquared : Real)
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective
      (globalCandidateANonSpinCBulkSmoothEmbedding period hPeriod metric
        massSquared data analysis) :=
  (diagonalExtendedBulkSmoothEmbedding_injective period hPeriod metric
      massSquared data analysis).comp
    (globalCandidateANonSpinCBulkCoreInclusion_injective
      period hPeriod analysis)

/-! ## Corrected gauge-fixed tangent -/

/-- The retained graph factors occupy disjoint metric, Abelian, LL and typed
nonminimal coordinates of the corrected tangent. -/
def globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateANonSpinCBulkSmoothCore period hPeriod analysis →ₗ[Real]
      GlobalGaugeFixedPhysicalFieldTangent period hPeriod configuration where
  toFun core :=
    diagonalDiffeomorphismGaugeFixedTangentLinearMap period hPeriod
        configuration core.1 +
      globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap period hPeriod
        configuration data core.2.1 +
      extendedLLGaugeFixedTangentLinearMap period hPeriod configuration
        analysis core.2.2
  map_add' first second := by
    change
      diagonalDiffeomorphismGaugeFixedTangentLinearMap period hPeriod
            configuration (first.1 + second.1) +
          globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap period hPeriod
            configuration data (first.2.1 + second.2.1) +
        extendedLLGaugeFixedTangentLinearMap period hPeriod configuration
            analysis (first.2.2 + second.2.2) =
      (diagonalDiffeomorphismGaugeFixedTangentLinearMap period hPeriod
            configuration first.1 +
          globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap period hPeriod
            configuration data first.2.1 +
        extendedLLGaugeFixedTangentLinearMap period hPeriod configuration
            analysis first.2.2) +
      (diagonalDiffeomorphismGaugeFixedTangentLinearMap period hPeriod
            configuration second.1 +
          globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap period hPeriod
            configuration data second.2.1 +
        extendedLLGaugeFixedTangentLinearMap period hPeriod configuration
            analysis second.2.2)
    simp only [map_add]
    abel
  map_smul' scalar core := by
    change
      diagonalDiffeomorphismGaugeFixedTangentLinearMap period hPeriod
            configuration (scalar • core.1) +
          globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap period hPeriod
            configuration data (scalar • core.2.1) +
        extendedLLGaugeFixedTangentLinearMap period hPeriod configuration
            analysis (scalar • core.2.2) =
      scalar •
        (diagonalDiffeomorphismGaugeFixedTangentLinearMap period hPeriod
              configuration core.1 +
            globalPairedAbelianBRSTStateGaugeFixedTangentLinearMap period hPeriod
              configuration data core.2.1 +
          extendedLLGaugeFixedTangentLinearMap period hPeriod configuration
              analysis core.2.2)
    simp only [map_smul, smul_add]

@[simp]
theorem globalCandidateANonSpinCBulkGaugeFixedTangent_metric
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : GlobalCandidateANonSpinCBulkSmoothCore period hPeriod analysis) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
        configuration data analysis core).1.1).fullMetricPerturbation =
      core.1.metricPerturbation := by
  change core.1.metricPerturbation + 0 + 0 = core.1.metricPerturbation
  simp

@[simp]
theorem globalCandidateANonSpinCBulkGaugeFixedTangent_gauge
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : GlobalCandidateANonSpinCBulkSmoothCore period hPeriod analysis) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
        configuration data analysis core).1.1).independent.gauge =
      globalCandidateAPairedGaugePotentialCoefficientLinearMap period hPeriod
        data core.2.1.potential := by
  change 0 +
      globalCandidateAPairedGaugePotentialCoefficientLinearMap period hPeriod
        data core.2.1.potential + 0 = _
  simp

@[simp]
theorem globalCandidateANonSpinCBulkGaugeFixedTangent_llAuxMetric
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : GlobalCandidateANonSpinCBulkSmoothCore period hPeriod analysis) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
        configuration data analysis core).1.1).independent.llAuxMetric =
      core.2.2.1.1 := by
  change 0 + 0 + core.2.2.1.1 = core.2.2.1.1
  simp

@[simp]
theorem globalCandidateANonSpinCBulkGaugeFixedTangent_llMeasure
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : GlobalCandidateANonSpinCBulkSmoothCore period hPeriod analysis) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
        configuration data analysis core).1.1).independent.llMeasure =
      core.2.2.1.2 := by
  change 0 + 0 + core.2.2.1.2 = core.2.2.1.2
  simp

@[simp]
theorem globalCandidateANonSpinCBulkGaugeFixedTangent_llField
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : GlobalCandidateANonSpinCBulkSmoothCore period hPeriod analysis) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
        configuration data analysis core).1.1).independent.llField =
      core.2.2.2.toTest := by
  change 0 + 0 + core.2.2.2.toTest = core.2.2.2.toTest
  simp

@[simp]
theorem globalCandidateANonSpinCBulkGaugeFixedTangent_spinCMatter
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : GlobalCandidateANonSpinCBulkSmoothCore period hPeriod analysis) :
    (globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
      configuration data analysis core).1.1.2 = 0 := by
  change 0 + 0 + 0 = 0
  simp

@[simp]
theorem globalCandidateANonSpinCBulkGaugeFixedTangent_abelian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : GlobalCandidateANonSpinCBulkSmoothCore period hPeriod analysis) :
    (globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
      configuration data analysis core).2.abelian = core.2.1.nonminimal := by
  change 0 + core.2.1.nonminimal + 0 = core.2.1.nonminimal
  simp

@[simp]
theorem globalCandidateANonSpinCBulkGaugeFixedTangent_diffeomorphism
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : GlobalCandidateANonSpinCBulkSmoothCore period hPeriod analysis) :
    (globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
      configuration data analysis core).2.diffeomorphism =
      core.1.nonminimal := by
  change core.1.nonminimal + 0 + 0 = core.1.nonminimal
  simp

theorem globalCandidateANonSpinCBulkGaugeFixedTangent_injective
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Function.Injective
      (globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
        configuration data analysis) := by
  intro first second hEqual
  have hMetric := congrArg
    (fun tangent : GlobalGaugeFixedPhysicalFieldTangent period hPeriod
        configuration =>
      (GlobalPhysicalFieldTangent.completeVariation period hPeriod
        tangent.1.1).fullMetricPerturbation) hEqual
  have hGauge := congrArg
    (fun tangent : GlobalGaugeFixedPhysicalFieldTangent period hPeriod
        configuration =>
      (GlobalPhysicalFieldTangent.completeVariation period hPeriod
        tangent.1.1).independent.gauge) hEqual
  have hAux := congrArg
    (fun tangent : GlobalGaugeFixedPhysicalFieldTangent period hPeriod
        configuration =>
      (GlobalPhysicalFieldTangent.completeVariation period hPeriod
        tangent.1.1).independent.llAuxMetric) hEqual
  have hMeasure := congrArg
    (fun tangent : GlobalGaugeFixedPhysicalFieldTangent period hPeriod
        configuration =>
      (GlobalPhysicalFieldTangent.completeVariation period hPeriod
        tangent.1.1).independent.llMeasure) hEqual
  have hField := congrArg
    (fun tangent : GlobalGaugeFixedPhysicalFieldTangent period hPeriod
        configuration =>
      (GlobalPhysicalFieldTangent.completeVariation period hPeriod
        tangent.1.1).independent.llField) hEqual
  have hAbelian := congrArg
    (fun tangent : GlobalGaugeFixedPhysicalFieldTangent period hPeriod
        configuration => tangent.2.abelian) hEqual
  have hDiffeomorphism := congrArg
    (fun tangent : GlobalGaugeFixedPhysicalFieldTangent period hPeriod
        configuration => tangent.2.diffeomorphism) hEqual
  simp only [globalCandidateANonSpinCBulkGaugeFixedTangent_metric] at hMetric
  simp only [globalCandidateANonSpinCBulkGaugeFixedTangent_gauge] at hGauge
  simp only [globalCandidateANonSpinCBulkGaugeFixedTangent_llAuxMetric] at hAux
  simp only [globalCandidateANonSpinCBulkGaugeFixedTangent_llMeasure] at hMeasure
  simp only [globalCandidateANonSpinCBulkGaugeFixedTangent_llField] at hField
  simp only [globalCandidateANonSpinCBulkGaugeFixedTangent_abelian] at hAbelian
  simp only [globalCandidateANonSpinCBulkGaugeFixedTangent_diffeomorphism]
    at hDiffeomorphism
  apply Prod.ext
  · exact GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
      hMetric hDiffeomorphism
  · apply Prod.ext
    · apply GlobalPairedAbelianBRSTState.ext
      · exact
          (globalCandidateAPairedGaugePotentialCoefficientLinearMap_injective
            period hPeriod data) hGauge
      · exact hAbelian
    · exact Prod.ext (Prod.ext hAux hMeasure)
        (LLH1Smooth.ext period hPeriod hField)

/-! ## Physical zero-nonminimal shadow in `GlobalFieldTangent` -/

/-- Physical coordinates of the same non-SpinC bulk sector.  Typed ghosts are
absent because `GlobalFieldTangent` has no such slots. -/
abbrev GlobalCandidateANonSpinCPhysicalBulkSmoothCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  GlobalMetricPerturbationPair period hPeriod ×
    ((Sector → SmoothAbelianGaugePotential period hPeriod) ×
      GlobalFullLLSmooth period hPeriod analysis)

def globalCandidateANonSpinCPhysicalBulkMinimalTangentLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateANonSpinCPhysicalBulkSmoothCore period hPeriod analysis
      →ₗ[Real] GlobalMinimalPhysicalFieldTangent period hPeriod configuration where
  toFun core :=
    globalMetricPerturbationMinimalPhysicalTangentLinearMap period hPeriod
        configuration core.1 +
      globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
        hPeriod data core.2.1 +
      extendedLLMinimalTangentLinearMap period hPeriod analysis core.2.2
  map_add' first second := by
    change
      globalMetricPerturbationMinimalPhysicalTangentLinearMap period hPeriod
            configuration (first.1 + second.1) +
          globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
            hPeriod data (first.2.1 + second.2.1) +
        extendedLLMinimalTangentLinearMap period hPeriod analysis
            (first.2.2 + second.2.2) =
      (globalMetricPerturbationMinimalPhysicalTangentLinearMap period hPeriod
            configuration first.1 +
          globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
            hPeriod data first.2.1 +
        extendedLLMinimalTangentLinearMap period hPeriod analysis first.2.2) +
      (globalMetricPerturbationMinimalPhysicalTangentLinearMap period hPeriod
            configuration second.1 +
          globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
            hPeriod data second.2.1 +
        extendedLLMinimalTangentLinearMap period hPeriod analysis second.2.2)
    simp only [map_add]
    abel
  map_smul' scalar core := by
    change
      globalMetricPerturbationMinimalPhysicalTangentLinearMap period hPeriod
            configuration (scalar • core.1) +
          globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
            hPeriod data (scalar • core.2.1) +
        extendedLLMinimalTangentLinearMap period hPeriod analysis
            (scalar • core.2.2) =
      scalar •
        (globalMetricPerturbationMinimalPhysicalTangentLinearMap period hPeriod
              configuration core.1 +
            globalCandidateAPairedGaugePotentialMinimalTangentLinearMap period
              hPeriod data core.2.1 +
          extendedLLMinimalTangentLinearMap period hPeriod analysis core.2.2)
    simp only [map_smul, smul_add]

/-- Zero-D10 realization of the physical non-SpinC bulk core in the legacy
global tangent. -/
def globalCandidateANonSpinCPhysicalBulkGlobalFieldTangentLinearMap
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    GlobalCandidateANonSpinCPhysicalBulkSmoothCore period hPeriod analysis
      →ₗ[Real] GlobalFieldTangent period hPeriod configuration :=
  (globalPhysicalFieldTangentZeroD10InclusionLinearMap period hPeriod).comp
    ((globalMinimalPhysicalTangentInclusionLinearMap period hPeriod
      configuration).comp
        (globalCandidateANonSpinCPhysicalBulkMinimalTangentLinearMap
          period hPeriod data analysis))

@[simp]
theorem globalCandidateANonSpinCPhysicalBulkGlobalFieldTangent_metric
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateANonSpinCPhysicalBulkSmoothCore period hPeriod
      analysis) :
    (GlobalFieldTangent.completeVariation period hPeriod
      (globalCandidateANonSpinCPhysicalBulkGlobalFieldTangentLinearMap
        period hPeriod data analysis core)).fullMetricPerturbation = core.1 := by
  change core.1 + 0 + 0 = core.1
  simp

@[simp]
theorem globalCandidateANonSpinCPhysicalBulkGlobalFieldTangent_gauge
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateANonSpinCPhysicalBulkSmoothCore period hPeriod
      analysis) :
    (GlobalFieldTangent.completeVariation period hPeriod
      (globalCandidateANonSpinCPhysicalBulkGlobalFieldTangentLinearMap
        period hPeriod data analysis core)).independent.gauge =
      globalCandidateAPairedGaugePotentialCoefficientLinearMap period hPeriod
        data core.2.1 := by
  change 0 +
      globalCandidateAPairedGaugePotentialCoefficientLinearMap period hPeriod
        data core.2.1 + 0 = _
  simp

@[simp]
theorem globalCandidateANonSpinCPhysicalBulkGlobalFieldTangent_llAuxMetric
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateANonSpinCPhysicalBulkSmoothCore period hPeriod
      analysis) :
    (GlobalFieldTangent.completeVariation period hPeriod
      (globalCandidateANonSpinCPhysicalBulkGlobalFieldTangentLinearMap
        period hPeriod data analysis core)).independent.llAuxMetric =
      core.2.2.1.1 := by
  change 0 + 0 + core.2.2.1.1 = core.2.2.1.1
  simp

@[simp]
theorem globalCandidateANonSpinCPhysicalBulkGlobalFieldTangent_llMeasure
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateANonSpinCPhysicalBulkSmoothCore period hPeriod
      analysis) :
    (GlobalFieldTangent.completeVariation period hPeriod
      (globalCandidateANonSpinCPhysicalBulkGlobalFieldTangentLinearMap
        period hPeriod data analysis core)).independent.llMeasure =
      core.2.2.1.2 := by
  change 0 + 0 + core.2.2.1.2 = core.2.2.1.2
  simp

@[simp]
theorem globalCandidateANonSpinCPhysicalBulkGlobalFieldTangent_llField
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateANonSpinCPhysicalBulkSmoothCore period hPeriod
      analysis) :
    (GlobalFieldTangent.completeVariation period hPeriod
      (globalCandidateANonSpinCPhysicalBulkGlobalFieldTangentLinearMap
        period hPeriod data analysis core)).independent.llField =
      core.2.2.2.toTest := by
  change 0 + 0 + core.2.2.2.toTest = core.2.2.2.toTest
  simp

@[simp]
theorem globalCandidateANonSpinCPhysicalBulkGlobalFieldTangent_spinCMatter
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateANonSpinCPhysicalBulkSmoothCore period hPeriod
      analysis) :
    (globalCandidateANonSpinCPhysicalBulkGlobalFieldTangentLinearMap
      period hPeriod data analysis core).spinCMatter period hPeriod = 0 := by
  change 0 + 0 + 0 = 0
  simp

@[simp]
theorem globalCandidateANonSpinCPhysicalBulkGlobalFieldTangent_d10
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (core : GlobalCandidateANonSpinCPhysicalBulkSmoothCore period hPeriod
      analysis) :
    (globalCandidateANonSpinCPhysicalBulkGlobalFieldTangentLinearMap
      period hPeriod data analysis core).d10Coordinates period hPeriod = 0 :=
  rfl

theorem globalCandidateANonSpinCPhysicalBulkGlobalFieldTangent_injective
    {configuration : GlobalFieldConfiguration period hPeriod}
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (data : GlobalCandidateAActionData period hPeriod configuration couplings
      NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration) :
    Function.Injective
      (globalCandidateANonSpinCPhysicalBulkGlobalFieldTangentLinearMap
        period hPeriod data analysis) := by
  intro first second hEqual
  have hMetric := congrArg
    (fun tangent : GlobalFieldTangent period hPeriod configuration =>
      (tangent.completeVariation period hPeriod).fullMetricPerturbation) hEqual
  have hGauge := congrArg
    (fun tangent : GlobalFieldTangent period hPeriod configuration =>
      (tangent.completeVariation period hPeriod).independent.gauge) hEqual
  have hAux := congrArg
    (fun tangent : GlobalFieldTangent period hPeriod configuration =>
      (tangent.completeVariation period hPeriod).independent.llAuxMetric) hEqual
  have hMeasure := congrArg
    (fun tangent : GlobalFieldTangent period hPeriod configuration =>
      (tangent.completeVariation period hPeriod).independent.llMeasure) hEqual
  have hField := congrArg
    (fun tangent : GlobalFieldTangent period hPeriod configuration =>
      (tangent.completeVariation period hPeriod).independent.llField) hEqual
  simp only [globalCandidateANonSpinCPhysicalBulkGlobalFieldTangent_metric]
    at hMetric
  simp only [globalCandidateANonSpinCPhysicalBulkGlobalFieldTangent_gauge]
    at hGauge
  simp only [globalCandidateANonSpinCPhysicalBulkGlobalFieldTangent_llAuxMetric]
    at hAux
  simp only [globalCandidateANonSpinCPhysicalBulkGlobalFieldTangent_llMeasure]
    at hMeasure
  simp only [globalCandidateANonSpinCPhysicalBulkGlobalFieldTangent_llField]
    at hField
  apply Prod.ext hMetric
  apply Prod.ext
  · exact
      (globalCandidateAPairedGaugePotentialCoefficientLinearMap_injective
        period hPeriod data) hGauge
  · exact Prod.ext (Prod.ext hAux hMeasure)
      (LLH1Smooth.ext period hPeriod hField)

end
end P0EFTJanusProgramPGlobalCandidateANonSpinCBulkGlobalTangentBridge4D
end JanusFormal
