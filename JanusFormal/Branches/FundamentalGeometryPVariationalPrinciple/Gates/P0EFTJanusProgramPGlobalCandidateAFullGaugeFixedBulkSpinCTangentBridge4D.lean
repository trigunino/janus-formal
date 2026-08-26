import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANonSpinCBulkGlobalTangentBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASpinCMatterGlobalTangentBridge4D

/-!
# Full gauge-fixed Candidate-A bulk and finite SpinC tangent

The diagonal diffeomorphism BRST block, paired Abelian BRST block, full LL
smooth core and finite primitive SpinC coefficients occupy disjoint slots of
the corrected gauge-fixed tangent.  D10 remains a separate coefficient factor,
because this tangent has no D10 slot.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCTangentBridge4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusMappingTorusPTSymmetricLLH1RieszOperator4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalGaugeTangentIntrinsicEmbedding4D
open P0EFTJanusProgramPGlobalCandidateAAbelianGaugeFixedAction4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
open P0EFTJanusProgramPGlobalCandidateAAbelianExtendedBulkGraphC2Chart4D
open P0EFTJanusProgramPGlobalCandidateADiagonalDiffeomorphismBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPGlobalCandidateANonSpinCBulkGlobalTangentBridge4D

variable (period : Real) (hPeriod : period ≠ 0)

/-- All smooth gauge-fixed bulk coordinates, with no D10 factor. -/
abbrev GlobalCandidateAFullGaugeFixedBulkSpinCCore
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration) :=
  GlobalCandidateANonSpinCBulkSmoothCore period hPeriod analysis ×
    ProgramPPrimitiveSpinCMatterFiniteCoefficients

/-- The finite SpinC coordinate in the gauge-fixed tangent, with zero typed
nonminimal component. -/
def globalCandidateASpinCFiniteGaugeFixedTangentLinearMap
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) :
    ProgramPPrimitiveSpinCMatterFiniteCoefficients →ₗ[Real]
      GlobalGaugeFixedPhysicalFieldTangent period hPeriod configuration :=
  extendedMatterGaugeFixedTangentLinearMap period hPeriod configuration

@[simp]
theorem globalCandidateASpinCFiniteGaugeFixedTangent_spinCMatter
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    (globalCandidateASpinCFiniteGaugeFixedTangentLinearMap period hPeriod
      configuration coefficients).1.1.2 =
      programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
        coefficients :=
  rfl

@[simp]
theorem globalCandidateASpinCFiniteGaugeFixedTangent_nonminimal
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (coefficients : ProgramPPrimitiveSpinCMatterFiniteCoefficients) :
    (globalCandidateASpinCFiniteGaugeFixedTangentLinearMap period hPeriod
      configuration coefficients).2 = 0 :=
  rfl

/-- Sum of the non-SpinC gauge-fixed bridge and the finite SpinC bridge. -/
def globalCandidateAFullGaugeFixedBulkSpinCTangentLinearMap
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod analysis →ₗ[Real]
      GlobalGaugeFixedPhysicalFieldTangent period hPeriod configuration where
  toFun core :=
    globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
        configuration data analysis core.1 +
      globalCandidateASpinCFiniteGaugeFixedTangentLinearMap period hPeriod
        configuration core.2
  map_add' first second := by
    change
      globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
            configuration data analysis (first.1 + second.1) +
        globalCandidateASpinCFiniteGaugeFixedTangentLinearMap period hPeriod
            configuration (first.2 + second.2) =
      (globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
            configuration data analysis first.1 +
        globalCandidateASpinCFiniteGaugeFixedTangentLinearMap period hPeriod
            configuration first.2) +
      (globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
            configuration data analysis second.1 +
        globalCandidateASpinCFiniteGaugeFixedTangentLinearMap period hPeriod
            configuration second.2)
    simp only [map_add]
    abel
  map_smul' scalar core := by
    change
      globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
            configuration data analysis (scalar • core.1) +
        globalCandidateASpinCFiniteGaugeFixedTangentLinearMap period hPeriod
            configuration (scalar • core.2) =
      scalar •
        (globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
            configuration data analysis core.1 +
          globalCandidateASpinCFiniteGaugeFixedTangentLinearMap period hPeriod
            configuration core.2)
    simp only [map_smul, smul_add]

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCTangent_metric
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod
      analysis) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullGaugeFixedBulkSpinCTangentLinearMap period hPeriod
        configuration data analysis core).1.1).fullMetricPerturbation =
      core.1.1.metricPerturbation := by
  change
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
        configuration data analysis core.1).1.1).fullMetricPerturbation + 0 = _
  rw [globalCandidateANonSpinCBulkGaugeFixedTangent_metric]
  simp

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCTangent_gauge
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod
      analysis) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullGaugeFixedBulkSpinCTangentLinearMap period hPeriod
        configuration data analysis core).1.1).independent.gauge =
      globalCandidateAPairedGaugePotentialCoefficientLinearMap period hPeriod
        data core.1.2.1.potential := by
  change
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
        configuration data analysis core.1).1.1).independent.gauge + 0 = _
  rw [globalCandidateANonSpinCBulkGaugeFixedTangent_gauge]
  simp

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCTangent_llAuxMetric
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod
      analysis) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullGaugeFixedBulkSpinCTangentLinearMap period hPeriod
        configuration data analysis core).1.1).independent.llAuxMetric =
      core.1.2.2.1.1 := by
  change
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
        configuration data analysis core.1).1.1).independent.llAuxMetric + 0 = _
  rw [globalCandidateANonSpinCBulkGaugeFixedTangent_llAuxMetric]
  simp

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCTangent_llMeasure
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod
      analysis) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullGaugeFixedBulkSpinCTangentLinearMap period hPeriod
        configuration data analysis core).1.1).independent.llMeasure =
      core.1.2.2.1.2 := by
  change
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
        configuration data analysis core.1).1.1).independent.llMeasure + 0 = _
  rw [globalCandidateANonSpinCBulkGaugeFixedTangent_llMeasure]
  simp

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCTangent_llField
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod
      analysis) :
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateAFullGaugeFixedBulkSpinCTangentLinearMap period hPeriod
        configuration data analysis core).1.1).independent.llField =
      core.1.2.2.2.toTest := by
  change
    (GlobalPhysicalFieldTangent.completeVariation period hPeriod
      (globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
        configuration data analysis core.1).1.1).independent.llField + 0 = _
  rw [globalCandidateANonSpinCBulkGaugeFixedTangent_llField]
  simp

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCTangent_spinCMatter
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod
      analysis) :
    (globalCandidateAFullGaugeFixedBulkSpinCTangentLinearMap period hPeriod
      configuration data analysis core).1.1.2 =
      programPPrimitiveSpinCMatterSmoothFiniteSynthesis period hPeriod
        core.2 := by
  change
    (globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
      configuration data analysis core.1).1.1.2 +
      (globalCandidateASpinCFiniteGaugeFixedTangentLinearMap period hPeriod
        configuration core.2).1.1.2 = _
  rw [globalCandidateANonSpinCBulkGaugeFixedTangent_spinCMatter,
    globalCandidateASpinCFiniteGaugeFixedTangent_spinCMatter]
  simp

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCTangent_abelian
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod
      analysis) :
    (globalCandidateAFullGaugeFixedBulkSpinCTangentLinearMap period hPeriod
      configuration data analysis core).2.abelian = core.1.2.1.nonminimal := by
  change
    (globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
      configuration data analysis core.1).2.abelian + 0 = _
  rw [globalCandidateANonSpinCBulkGaugeFixedTangent_abelian]
  simp

@[simp]
theorem globalCandidateAFullGaugeFixedBulkSpinCTangent_diffeomorphism
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (core : GlobalCandidateAFullGaugeFixedBulkSpinCCore period hPeriod
      analysis) :
    (globalCandidateAFullGaugeFixedBulkSpinCTangentLinearMap period hPeriod
      configuration data analysis core).2.diffeomorphism =
      core.1.1.nonminimal := by
  change
    (globalCandidateANonSpinCBulkGaugeFixedTangentLinearMap period hPeriod
      configuration data analysis core.1).2.diffeomorphism + 0 = _
  rw [globalCandidateANonSpinCBulkGaugeFixedTangent_diffeomorphism]
  simp

theorem globalCandidateAFullGaugeFixedBulkSpinCTangent_injective
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Function.Injective
      (globalCandidateAFullGaugeFixedBulkSpinCTangentLinearMap period hPeriod
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
  have hSpinC := congrArg
    (fun tangent : GlobalGaugeFixedPhysicalFieldTangent period hPeriod
        configuration => tangent.1.1.2) hEqual
  have hAbelian := congrArg
    (fun tangent : GlobalGaugeFixedPhysicalFieldTangent period hPeriod
        configuration => tangent.2.abelian) hEqual
  have hDiffeomorphism := congrArg
    (fun tangent : GlobalGaugeFixedPhysicalFieldTangent period hPeriod
        configuration => tangent.2.diffeomorphism) hEqual
  simp only [globalCandidateAFullGaugeFixedBulkSpinCTangent_metric] at hMetric
  simp only [globalCandidateAFullGaugeFixedBulkSpinCTangent_gauge] at hGauge
  simp only [globalCandidateAFullGaugeFixedBulkSpinCTangent_llAuxMetric] at hAux
  simp only [globalCandidateAFullGaugeFixedBulkSpinCTangent_llMeasure]
    at hMeasure
  simp only [globalCandidateAFullGaugeFixedBulkSpinCTangent_llField] at hField
  simp only [globalCandidateAFullGaugeFixedBulkSpinCTangent_spinCMatter]
    at hSpinC
  simp only [globalCandidateAFullGaugeFixedBulkSpinCTangent_abelian] at hAbelian
  simp only [globalCandidateAFullGaugeFixedBulkSpinCTangent_diffeomorphism]
    at hDiffeomorphism
  apply Prod.ext
  · apply Prod.ext
    · exact GlobalCandidateADiagonalDiffeomorphismBRSTState.ext
        hMetric hDiffeomorphism
    · apply Prod.ext
      · exact GlobalPairedAbelianBRSTState.ext
          ((globalCandidateAPairedGaugePotentialCoefficientLinearMap_injective
            period hPeriod data) hGauge) hAbelian
      · exact Prod.ext (Prod.ext hAux hMeasure)
          (LLH1Smooth.ext period hPeriod hField)
  · exact
      (programPPrimitiveSpinCMatterSmoothFiniteSynthesis_injective
        period hPeriod) hSpinC

end
end P0EFTJanusProgramPGlobalCandidateAFullGaugeFixedBulkSpinCTangentBridge4D
end JanusFormal
