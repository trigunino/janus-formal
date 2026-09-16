import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LocalPhysicalHessianDirectionalZero4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCTotalEuler4D

/-! The concrete paired strong chart has no physical mixed Hessian against a
pure SpinC direction, at every admissible point. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12StrongSpinCPhysicalMixedHessianZero4D

set_option autoImplicit false
set_option maxHeartbeats 600000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open Set Filter MeasureTheory
open scoped Manifold ContDiff Topology
open P0EFTJanusConvexHelmholtzReconstruction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusCanonicalDivergenceFreeLLFrame4D
open P0EFTJanusMappingTorusCanonicalVolumeH1Trace4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusPTSymmetricDifferentialLLStrongEquation4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalBoundaryCompletion4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionChart4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPFullCoupledHelmholtzAssembly4D
open P0EFTJanusProgramPGlobalEulerLagrange4D
open P0EFTJanusProgramPGlobalEulerLagrangeBlockDecomposition4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSeparatingPDEResidual4D
open P0EFTJanusProgramPGlobalEulerLagrangeMinimalPhysicalSevenBulkSystem4D
open P0EFTJanusProgramPGlobalEulerLagrangeMatterGraphMaximalSpectralResidual4D
open P0EFTJanusProgramPPrimitiveSpinCMatterGraphSameActionHessian4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartRegularMetric4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartMaxwell4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedGaugeCoefficientMaxwellAction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalConstantBoundaryC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalInteractionC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMatterC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalMetricGaugeCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLLC0FirstJetProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedFixedVolumeEinsteinHilbertC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedEinsteinHilbertActionBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalNineBlockC24D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongComponentPDEBlockPairing4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEightSectorEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongEulerNineBlockDecomposition4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongGaugeReducedCoupledResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLWeakFirstVariation4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldWeakResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLLFieldStrongEquation4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCSpectralAugmentedResidual4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongSpinCTotalEuler4D
open P0EFTJanusProgramPT12LocalPhysicalHessianDirectionalZero4D
open P0EFTJanusFullLLVariationalAPI4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

private theorem physical_gradient_zero_of_block_gradients_zero
    {Model : Type*} [NormedAddCommGroup Model] [NormedSpace Real Model]
    (blocks : FullCoupledActionBlocks Model) (point direction : Model)
    (hC2 : FullCoupledC2At blocks point)
    (hCandidate : actionGradient blocks.candidateA point direction = 0)
    (hRobin : actionGradient blocks.robin point direction = 0)
    (hEHPlus : actionGradient blocks.einsteinHilbertPlus point direction = 0)
    (hEHMinus : actionGradient blocks.einsteinHilbertMinus point direction = 0)
    (hMaxwellPlus : actionGradient blocks.maxwellPlus point direction = 0)
    (hMaxwellMinus : actionGradient blocks.maxwellMinus point direction = 0)
    (hFinite : actionGradient blocks.finiteBV point direction = 0) :
    actionGradient (fullCoupledPhysicalAction blocks) point direction = 0 := by
  have hA := hC2.candidateA.differentiableAt (by norm_num)
  have hR := hC2.robin.differentiableAt (by norm_num)
  have hEP := hC2.einsteinHilbertPlus.differentiableAt (by norm_num)
  have hEM := hC2.einsteinHilbertMinus.differentiableAt (by norm_num)
  have hMP := hC2.maxwellPlus.differentiableAt (by norm_num)
  have hMM := hC2.maxwellMinus.differentiableAt (by norm_num)
  have hF := hC2.finiteBV.differentiableAt (by norm_num)
  unfold actionGradient fullCoupledPhysicalAction at *
  change fderiv Real
      ((((((blocks.candidateA + blocks.robin) + blocks.einsteinHilbertPlus) +
        blocks.einsteinHilbertMinus) + blocks.maxwellPlus) +
        blocks.maxwellMinus) + blocks.finiteBV) point direction = 0
  rw [fderiv_add (((((hA.add hR).add hEP).add hEM).add hMP).add hMM) hF,
    fderiv_add ((((hA.add hR).add hEP).add hEM).add hMP) hMM,
    fderiv_add (((hA.add hR).add hEP).add hEM) hMP,
    fderiv_add ((hA.add hR).add hEP) hEM,
    fderiv_add (hA.add hR) hEP,
    fderiv_add hA hR]
  simp [hCandidate, hRobin, hEHPlus, hEHMinus, hMaxwellPlus,
    hMaxwellMinus, hFinite]

/-- On the concrete paired strong chart, every mixed physical Hessian with a
pure smooth SpinC second slot vanishes. -/
theorem strong_spinC_physical_mixed_hessian_zero
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
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (point other : GlobalMinimalPhysicalFieldTangent period hPeriod
      configuration.physical)
    (hPoint : point ∈
      regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain period
        hPeriod configuration.physical plusBase minusBase)
    (test : ProgramPPrimitiveSpinCMatterSmoothField period hPeriod) :
    globalCandidateALocalPhysicalHessian period hPeriod
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure)
      point other
        (regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection
          period hPeriod configuration.physical test) = 0 := by
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedAddCommGroup
    period hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  letI := globalMinimalPhysicalPairedMetricGaugeLLStrongNormedSpace period
    hPeriod configuration data analysis realization plusBase minusBase
      (canonicalDivergenceFreeLLFrame period hPeriod)
  let chart :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure
  let blocks :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleActionBlocks
      period hPeriod configuration.physical couplings data plusBase minusBase
        hBase measure
  let direction :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongSpinCMatterDirection period
      hPeriod configuration.physical test
  have hOpen :=
    regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain_strong_isOpen
      period hPeriod configuration data analysis realization plusBase minusBase
  have hPointChart : point ∈ chart.family.domain := hPoint
  have hEuler :
      (fun state : chart.Model =>
        actionGradient
          (fullCoupledPhysicalAction
            (globalCandidateAActionBlocks period hPeriod
              (chart.family.toActionFamily period hPeriod 0
                chart.zero_mem_domain) measure)) state direction) =ᶠ[𝓝 point]
        fun _ => (0 : Real) := by
    filter_upwards [hOpen.mem_nhds hPoint] with current hCurrent
    change actionGradient (fullCoupledPhysicalAction blocks) current direction = 0
    have hC2 : FullCoupledC2At blocks current :=
      fullCoupledC2WithinAt_toAt
        (regularGeneralMetricC2PairedMinimalPhysicalNineBlockC2WithinAt
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure current hCurrent) hOpen hCurrent
    have hCandidate :
        actionGradient blocks.candidateA current direction = 0 := by
      simpa [blocks, direction] using
        (regularGeneralMetricC2PairedMinimalPhysicalCandidateA_actionGradient_strongSpinC_eq_zero
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure current hCurrent test)
    have hRobin : actionGradient blocks.robin current direction = 0 := by
      have h :=
        regularGeneralMetricC2PairedMinimalPhysicalRobin_actionGradient_eq_zero
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure current hCurrent
      simpa [blocks, direction] using congrArg
        (fun f : GlobalMinimalPhysicalFieldTangent period hPeriod
          configuration.physical →L[Real] Real => f direction) h
    have hEinstein :=
      regularGeneralMetricC2PairedMinimalPhysicalEinsteinHilbert_actionGradient_strongSpinC_eq_zero
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure current hCurrent test
    have hEHPlus :
        actionGradient blocks.einsteinHilbertPlus current direction = 0 := by
      simpa [blocks, direction] using hEinstein.1
    have hEHMinus :
        actionGradient blocks.einsteinHilbertMinus current direction = 0 := by
      simpa [blocks, direction] using hEinstein.2
    have hMaxwell :=
      regularGeneralMetricC2PairedMinimalPhysicalMaxwell_actionGradient_strongSpinC_eq_zero
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure current hCurrent test
    have hMaxwellPlus :
        actionGradient blocks.maxwellPlus current direction = 0 := by
      simpa [blocks, direction] using hMaxwell.1
    have hMaxwellMinus :
        actionGradient blocks.maxwellMinus current direction = 0 := by
      simpa [blocks, direction] using hMaxwell.2
    have hFinite : actionGradient blocks.finiteBV current direction = 0 := by
      have h :=
        regularGeneralMetricC2PairedMinimalPhysicalFiniteBV_actionGradient_eq_zero
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure current hCurrent
      simpa [blocks, direction] using congrArg
        (fun f : GlobalMinimalPhysicalFieldTangent period hPeriod
          configuration.physical →L[Real] Real => f direction) h
    exact physical_gradient_zero_of_block_gradients_zero blocks current
      direction hC2 hCandidate hRobin hEHPlus hEHMinus hMaxwellPlus
        hMaxwellMinus hFinite
  exact localPhysicalHessian_second_slot_zero_of_eventually_euler_zero
    period hPeriod chart point hPointChart direction hEuler other

end
end P0EFTJanusProgramPT12StrongSpinCPhysicalMixedHessianZero4D
end JanusFormal
