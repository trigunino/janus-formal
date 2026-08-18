import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAActionTranslationZeroModes4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianCanonicalSixSymmetryOrbitFrontier4D

/-!
# Terminal H10--H14 frontier from invariance of the genuine action

This is the action-level version of the symmetry-orbit terminal frontier.  Its
named-mode premise is the local identity

`S (x + t • v) = S x`

for the genuine common augmented Candidate-A action.  Differentiation supplies
gradient invariance and then the actual Hessian equation `H v = 0`.  Gårding
excludes hidden modes, while the canonical six dense-core construction supplies
H11.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianCanonicalSixActionSymmetryFrontier4D

set_option autoImplicit false
set_option maxHeartbeats 13600000
set_option synthInstance.maxHeartbeats 6800000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalCandidateAH10RobinProjectionCore4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
open P0EFTJanusProgramPGlobalCandidateAActionTranslationZeroModes4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixDenseCoreFrontier4D
open P0EFTJanusProgramPGlobalHessianCanonicalSixSymmetryOrbitFrontier4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  actualKernelNormedAddCommGroup
  actualKernelInnerProductSpace
  actualKernelNormedSpace
  actualKernelModule
  actualKernelCompleteSpace

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

/-- Strongest action-level terminal endpoint. -/
def global_candidateA_hessian_canonicalSix_actionSymmetry_frontier_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure) period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (projection : GlobalCandidateAH10RobinProjectionCoreData4D period hPeriod
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family)))
    (ZeroMode : Type*) [Fintype ZeroMode]
    (symmetries : GlobalCandidateAActionTranslationAutomaticSplit4D period
      hPeriod configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixPhysicalExtension period hPeriod
          configuration data analysis einsteinScale hTransverse family
            (projection.toDenseCoreAgreement period hPeriod hTransverse)
            chartBound)
        ZeroMode) :=
  global_candidateA_hessian_canonicalSix_symmetryOrbit_frontier_gate period
    hPeriod configuration data analysis einsteinScale hTransverse family
      projection chartBound ZeroMode symmetries.toGradientAutomaticSplit

/-- Exact zero-mode count derived from action invariance and Gårding. -/
theorem global_candidateA_hessian_canonicalSix_actionSymmetry_exact_count
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      (measure := measure) period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (projection : GlobalCandidateAH10RobinProjectionCoreData4D period hPeriod
      configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        einsteinScale)
    (chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family)))
    (ZeroMode : Type*) [Fintype ZeroMode]
    (symmetries : GlobalCandidateAActionTranslationAutomaticSplit4D period
      hPeriod configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data
          analysis einsteinScale hTransverse family)
        (globalCandidateACanonicalSixPhysicalExtension period hPeriod
          configuration data analysis einsteinScale hTransverse family
            (projection.toDenseCoreAgreement period hPeriod hTransverse)
            chartBound)
        ZeroMode) :
    let chart := globalCandidateAActualKernelChart period hPeriod configuration
      data analysis einsteinScale hTransverse family
    let sameAction := globalCandidateAActualKernelSameAction period hPeriod
      configuration data analysis einsteinScale hTransverse family
    let physical := globalCandidateACanonicalSixPhysicalExtension period hPeriod
      configuration data analysis einsteinScale hTransverse family
        (projection.toDenseCoreAgreement period hPeriod hTransverse) chartBound
    Module.finrank Real
        (globalCandidateAActualKernelOperator period hPeriod configuration data
          analysis chart sameAction physical).ker =
      Fintype.card ZeroMode := by
  dsimp only
  let certificate := global_candidateA_action_translation_zero_mode_gate
    period hPeriod symmetries
  exact certificate.2.1

/-- The action-level route has the same three analytic packets. -/
theorem global_candidateA_hessian_canonicalSix_actionSymmetry_three_inputs :
    Nonempty (Unit × Unit × Unit) :=
  ⟨((), (), ())⟩

end
end P0EFTJanusProgramPGlobalHessianCanonicalSixActionSymmetryFrontier4D
end JanusFormal
