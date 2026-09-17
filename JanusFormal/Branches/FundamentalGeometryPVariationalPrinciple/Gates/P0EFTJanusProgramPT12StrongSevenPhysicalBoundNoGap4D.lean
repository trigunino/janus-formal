import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongMatterLLSameActionBridge4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12StrongToH11PhysicalSecondJet4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D

/-! An H11 seven-block bound on the concrete strong chart excludes the H12 gap. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12StrongSevenPhysicalBoundNoGap4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalGraphProjections4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBoundedExtension4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedLorentzChartCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalLocalActionFamilyCenter4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleLocalActionFamily4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalStrongLocalEuler4D
open P0EFTJanusProgramPT12StrongMatterLLSameActionBridge4D
open P0EFTJanusProgramPT12StrongToH11PhysicalSecondJet4D

attribute [local instance]
  actualKernelNormedAddCommGroup
  actualKernelInnerProductSpace
  actualKernelNormedSpace
  actualKernelModule
  actualKernelCompleteSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- A seven-block H11 core bound for the centered strong chart rules out the
augmented H12 kernel-complement gap. -/
theorem no_augmented_kernelComplementGap_of_strong_seven_physical_bound
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    [IsFiniteMeasure measure]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (realization : ProgramPPrimitiveSpinCMatterSmoothGraphRealization4D
      period hPeriod couplings.matterMassSquared)
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hBase : RegularGeneralMetricC2PairedLorentzChartBaseCompatible
      period hPeriod plusBase minusBase)
    (hCenter : RegularGeneralMetricC2PairedMinimalPhysicalCenterCompatible
      period hPeriod configuration.physical plusBase minusBase hBase)
    (bound : GlobalCandidateASevenPhysicalCoreBound4D period hPeriod
      configuration data analysis
      (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
        period hPeriod configuration data analysis realization plusBase
          minusBase hBase measure)
      (strongMatterLLSameActionBridge period hPeriod configuration data
        analysis realization plusBase minusBase hBase hCenter measure)) :
    SelfAdjointKernelComplementGapData
      (globalCandidateAActualKernelOperator period hPeriod configuration data
        analysis
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure)
        (strongMatterLLSameActionBridge period hPeriod configuration data
          analysis realization plusBase minusBase hBase hCenter measure)
        (globalCandidateASevenPhysicalCommonDomainExtension_of_bound period
          hPeriod configuration data analysis
          (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
            period hPeriod configuration data analysis realization plusBase
              minusBase hBase measure)
          (strongMatterLLSameActionBridge period hPeriod configuration data
            analysis realization plusBase minusBase hBase hCenter measure)
          bound))
      (globalCandidateAActualKernelOperator_isSelfAdjoint period hPeriod
        configuration data analysis
        (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
          period hPeriod configuration data analysis realization plusBase
            minusBase hBase measure)
        (strongMatterLLSameActionBridge period hPeriod configuration data
          analysis realization plusBase minusBase hBase hCenter measure)
        (globalCandidateASevenPhysicalCommonDomainExtension_of_bound period
          hPeriod configuration data analysis
          (regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
            period hPeriod configuration data analysis realization plusBase
              minusBase hBase measure)
          (strongMatterLLSameActionBridge period hPeriod configuration data
            analysis realization plusBase minusBase hBase hCenter measure)
          bound)) → False := by
  let chart :=
    regularGeneralMetricC2PairedMinimalPhysicalStrongLocalVariationalChart
      period hPeriod configuration data analysis realization plusBase minusBase
        hBase measure
  let sameAction := strongMatterLLSameActionBridge period hPeriod configuration
    data analysis realization plusBase minusBase hBase hCenter measure
  let physical := globalCandidateASevenPhysicalCommonDomainExtension_of_bound
    period hPeriod configuration data analysis chart sameAction bound
  let bridge : StrongToH11PhysicalSecondJet period hPeriod configuration data
      analysis realization chart sameAction plusBase minusBase hBase := by
    refine { point := 0, point_mem := ?_, physical_second_jet := ?_ }
    · exact zero_mem_regularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomain
        period hPeriod configuration.physical plusBase minusBase hBase
    · intro first second
      rfl
  exact no_augmented_kernelComplementGap_of_strong_second_jet period hPeriod
    configuration data analysis realization chart sameAction physical plusBase
      minusBase hBase bridge

end
end P0EFTJanusProgramPT12StrongSevenPhysicalBoundNoGap4D
end JanusFormal
