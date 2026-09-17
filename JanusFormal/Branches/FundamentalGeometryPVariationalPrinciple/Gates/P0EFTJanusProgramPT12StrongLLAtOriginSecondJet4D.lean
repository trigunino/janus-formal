import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLWeakFirstVariation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalFullLLGraphRiesz4D

/-! The genuine nonlinear strong LL action has the same LL-only second jet at
the physical background as the completed H11 LL graph action. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12StrongLLAtOriginSecondJet4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 1200000
noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPCommonGeometricDomain4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLWeakFirstVariation4D
open P0EFTJanusProgramPGlobalFullLLGraphRiesz4D
open P0EFTJanusProgramPGlobalLLAuxMeasureSameActionHessian4D
open P0EFTJanusFullLLSameActionFredholmRestriction4D
open P0EFTJanusMatterRobinFullLLReducedFredholmBlock4D
open P0EFTJanusCommonMatterRobinLLReducedNaturalFredholmBlock4D
open P0EFTJanusFullLLHessianExplicitAdditivity4D
open P0EFTJanusFullLLVariationalAPI4D
open P0EFTJanusDifferentialLLFullCurveActionDecomposition4D
open P0EFTJanusIntegratedPTFullLLHessianVariation4D
open P0EFTJanusLLMeasureFieldTwoParameterDensity4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat := MappingTorus (fixedEquatorData period hPeriod)

local instance : ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveThroat period hPeriod) := borel _
local instance : BorelSpace (EffectiveThroat period hPeriod) where measurable_eq := rfl
local instance : IsFiniteMeasure (intrinsicCanonicalThroatVolumeMeasure period hPeriod) :=
  intrinsicCanonicalThroatVolumeMeasure_isFinite period hPeriod

/-- The LL-only Hessian of the authentic strong action at its tangent origin
is the actual full three-slot LL Hessian at the physical background. -/
theorem strongLLAction_second_fderiv_at_zero
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (first second : RegularGeneralMetricC2PairedMinimalPhysicalStrongLLTest
      period hPeriod) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    (fderiv Real
      (fun state => fderiv Real
        (regularGeneralMetricC2PairedMinimalPhysicalLLAction period hPeriod
          configuration.physical) state)
      (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration.physical))
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
        hPeriod configuration.physical first)
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
        hPeriod configuration.physical second) =
      fullLLHessian period hPeriod (canonicalDivergenceFreeLLFrame period hPeriod)
        (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
          configuration.physical 0)
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection period
          hPeriod first)
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection period
          hPeriod second)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let action := regularGeneralMetricC2PairedMinimalPhysicalLLAction period hPeriod
    configuration.physical
  let dFirst := regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection
    period hPeriod configuration.physical first
  let dSecond := regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection
    period hPeriod configuration.physical second
  let fields := regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period
    hPeriod configuration.physical 0
  let frame := canonicalDivergenceFreeLLFrame period hPeriod
  let mu := intrinsicCanonicalThroatVolumeMeasure period hPeriod
  have hSmooth : ContDiff Real ∞ action :=
    regularGeneralMetricC2PairedMinimalPhysicalLLAction_contDiff period hPeriod
      configuration data analysis realization plusBase minusBase
  have hC2 : ContDiffAt Real 2 action 0 :=
    hSmooth.contDiffAt.of_le (m := 2) (by
      exact (show (2 : ℕ∞ω) ≤ ∞ from WithTop.coe_le_coe.mpr le_top))
  have hGradientDiff : DifferentiableAt Real
      (fun state => fderiv Real action state) 0 :=
    (hC2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hLine : HasDerivAt (fun t : Real => t • dFirst) dFirst 0 := by
    simpa using (hasDerivAt_id (0 : Real)).smul_const dFirst
  have hComposite := hGradientDiff.hasFDerivAt.comp_hasDerivAt_of_eq
    0 hLine (by simp)
  have hApplied := hComposite.clm_apply
    (hasDerivAt_const (x := (0 : Real)) dSecond)
  have hSecondLine : HasDerivAt
      (fun t : Real => fderiv Real action (t • dFirst) dSecond)
      ((fderiv Real (fun state => fderiv Real action state) 0) dFirst dSecond)
      0 := by
    simpa using hApplied
  have hCurve : ∀ t : Real,
      regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
          configuration.physical (t • dFirst) =
        differentialLLFullCurve period hPeriod fields first.1 first.2.1
          first.2.2 t := by
    intro t
    simpa [dFirst, fields] using
      regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput_strongLLLine
        period hPeriod configuration
          (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
            configuration.physical) first t
  have hEulerCurve :
      (fun t : Real => fderiv Real action (t • dFirst) dSecond) =
        fullLLEulerAlong period hPeriod frame fields
          (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection
            period hPeriod second)
          (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection
            period hPeriod first) mu := by
    funext t
    rw [show fderiv Real action (t • dFirst) dSecond =
        fullLLEuler period hPeriod frame
          (regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period
            hPeriod configuration.physical (t • dFirst))
          (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection
            period hPeriod second) mu from
      regularGeneralMetricC2PairedMinimalPhysicalLLAction_fderiv_apply_strongLLDirection
        period hPeriod configuration data analysis realization plusBase
          minusBase (t • dFirst) second]
    rw [hCurve t]
    rfl
  rw [hEulerCurve] at hSecondLine
  have hLL := fullLLEuler_second_direction_hasDerivAt period hPeriod frame
    fields
    (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection period
      hPeriod second)
    (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection period
      hPeriod first) mu
  have hEq := hSecondLine.unique hLL
  simpa [action, dFirst, dSecond, fields, frame, mu,
    fullLLHessian_symmetric period hPeriod frame fields
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection period
        hPeriod second)
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection period
        hPeriod first) mu] using hEq

private theorem strongLLAPIDirection_smooth_eq_fullLLDirection
    {configuration : GlobalFieldConfiguration period hPeriod}
    (analysis : GlobalAnalysisData period hPeriod configuration)
    (direction : GlobalFullLLSmooth period hPeriod analysis) :
    regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection period
        hPeriod (direction.1.1, (direction.1.2, direction.2.toTest)) =
      globalCandidateAFullLLDirection period hPeriod direction := by
  simp [regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection,
    globalCandidateAFullLLDirection, addDirection,
    globalCandidateALLAuxMeasureDirection, fullLLFredholmDirection,
    fullRobinLLDirection, commonRobinLLDirection] <;> rfl

/-- On every smooth three-slot LL core pair, the strong action's physical
background Hessian is precisely the completed H11 LL graph form. -/
theorem strongLLAction_second_fderiv_eq_graph_on_smooth
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (first second : GlobalFullLLSmooth period hPeriod analysis) :
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
      period hPeriod configuration data analysis realization plusBase minusBase
        (canonicalDivergenceFreeLLFrame period hPeriod)
    (fderiv Real
      (fun state => fderiv Real
        (regularGeneralMetricC2PairedMinimalPhysicalLLAction period hPeriod
          configuration.physical) state)
      (0 : GlobalMinimalPhysicalFieldTangent period hPeriod
        configuration.physical))
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
        hPeriod configuration.physical
        (first.1.1, (first.1.2, first.2.toTest)))
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLLDirection period
        hPeriod configuration.physical
        (second.1.1, (second.1.2, second.2.toTest))) =
      globalCandidateAFullLLGraphForm period hPeriod data analysis
        (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis first)
        (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis second) := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  rw [strongLLAction_second_fderiv_at_zero period hPeriod configuration data
    analysis realization plusBase minusBase
    (first.1.1, (first.1.2, first.2.toTest))
    (second.1.1, (second.1.2, second.2.toTest))]
  have hZeroIndependent :
      (0 : ProgramPCompleteVariation4D period hPeriod).independent = 0 := rfl
  have hFields :
      regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput period hPeriod
          configuration.physical 0 = data.boundary.llFields period hPeriod := by
    apply IndependentFields.ext <;>
      simp [regularGeneralMetricC2PairedMinimalPhysicalLLFieldsInput,
        P0EFTJanusProgramPGlobalBoundaryCompletion4D.GlobalBoundaryVariationData.llFields,
        GlobalPhysicalFieldTangent.completeVariation, hZeroIndependent]
    · change configuration.physical.coefficientFields.llAuxMetric + 0 =
        configuration.physical.coefficientFields.llAuxMetric
      simp
    · change configuration.physical.coefficientFields.llMeasure + 0 =
        configuration.physical.coefficientFields.llMeasure
      simp
    · change configuration.physical.coefficientFields.llField + 0 =
        configuration.physical.coefficientFields.llField
      simp
  rw [hFields]
  calc
    fullLLHessian period hPeriod (canonicalDivergenceFreeLLFrame period hPeriod)
        (data.boundary.llFields period hPeriod)
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection period
          hPeriod (first.1.1, (first.1.2, first.2.toTest)))
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLLAPIDirection period
          hPeriod (second.1.1, (second.1.2, second.2.toTest)))
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) =
      fullLLHessian period hPeriod (canonicalDivergenceFreeLLFrame period hPeriod)
        (data.boundary.llFields period hPeriod)
        (globalCandidateAFullLLDirection period hPeriod first)
        (globalCandidateAFullLLDirection period hPeriod second)
        (intrinsicCanonicalThroatVolumeMeasure period hPeriod) := by
          rw [strongLLAPIDirection_smooth_eq_fullLLDirection period hPeriod
            analysis first]
          rw [strongLLAPIDirection_smooth_eq_fullLLDirection period hPeriod
            analysis second]
    _ = globalCandidateAFullLLSameActionHessian period hPeriod data first second := rfl
    _ = globalCandidateAFullLLGraphForm period hPeriod data analysis
        (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis first)
        (globalCandidateAFullLLSmoothEmbedding period hPeriod data analysis second) := by
          rw [globalCandidateAFullLLGraphForm_apply]
          exact (globalCandidateAFullLLContinuousHessian_smooth period hPeriod
            data analysis first second).symm

end
end P0EFTJanusProgramPT12StrongLLAtOriginSecondJet4D
end JanusFormal
