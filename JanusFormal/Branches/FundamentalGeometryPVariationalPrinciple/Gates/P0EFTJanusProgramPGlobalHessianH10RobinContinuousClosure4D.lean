import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousExtensions4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianH10RobinAnalyticClosure4D

/-!
# H14 from H10 Robin transfer and seven continuous physical extensions

This façade removes two bookkeeping layers from the constructive terminal
route.  The H10 action germ supplies the Robin `C²` block, while seven genuine
continuous bilinear extensions supply their own core estimates through operator
norms.  The only remaining Fredholm input is the generalized inverse of the
resulting augmented operator.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianH10RobinContinuousClosure4D

set_option autoImplicit false
set_option maxHeartbeats 3600000
set_option synthInstance.maxHeartbeats 1800000

noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateACommonAugmentedAnalyticDomain4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10RobinReduction4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalContinuousExtensions4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedGeneralizedInverse4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalHessianH10RobinAnalyticClosure4D

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

/-- Canonical seven-block core bounds obtained from the continuous extensions. -/
def globalCandidateAH10RobinContinuousBlockBounds
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10RobinData4D
      period hPeriod (measure := measure) configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared))
    (extensions : GlobalCandidateASevenPhysicalContinuousBlockExtensions4D
      period hPeriod (measure := measure) configuration data analysis
        (globalCandidateAH10RobinChart period hPeriod (measure := measure)
          configuration data analysis family)
        (globalCandidateAH10RobinSameAction period hPeriod (measure := measure)
          configuration data analysis family)) :=
  globalCandidateASevenPhysicalBlockCoreBounds_of_continuousExtensions period
    hPeriod (measure := measure) configuration data analysis
      (globalCandidateAH10RobinChart period hPeriod (measure := measure)
        configuration data analysis family)
      (globalCandidateAH10RobinSameAction period hPeriod (measure := measure)
        configuration data analysis family)
      extensions

/-- The H11 extension generated from the seven continuous block forms. -/
def globalCandidateAH10RobinContinuousPhysicalExtension
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10RobinData4D
      period hPeriod (measure := measure) configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared))
    (extensions : GlobalCandidateASevenPhysicalContinuousBlockExtensions4D
      period hPeriod (measure := measure) configuration data analysis
        (globalCandidateAH10RobinChart period hPeriod (measure := measure)
          configuration data analysis family)
        (globalCandidateAH10RobinSameAction period hPeriod (measure := measure)
          configuration data analysis family)) :=
  globalCandidateAH10RobinPhysicalExtension period hPeriod (measure := measure)
    configuration data analysis family
      (globalCandidateAH10RobinContinuousBlockBounds period hPeriod
        (measure := measure) configuration data analysis family extensions)

/-- Preferred H14 gate when the seven physical estimates are presented as
continuous extensions rather than manually chosen constants. -/
def global_candidateA_hessian_h10Robin_continuous_closure_gate
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {measure : Measure (EffectiveQuotient period hPeriod)}
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical)
    (einsteinScale : Real)
    (hBoundaryTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric)
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10RobinData4D
      period hPeriod (measure := measure) configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared))
    (extensions : GlobalCandidateASevenPhysicalContinuousBlockExtensions4D
      period hPeriod (measure := measure) configuration data analysis
        (globalCandidateAH10RobinChart period hPeriod (measure := measure)
          configuration data analysis family)
        (globalCandidateAH10RobinSameAction period hPeriod (measure := measure)
          configuration data analysis family))
    (inverse : GlobalCandidateAFaithfulAugmentedGeneralizedInverse4D period
      hPeriod configuration data analysis
        (globalCandidateAH10RobinChart period hPeriod (measure := measure)
          configuration data analysis family)
        (globalCandidateAH10RobinSameAction period hPeriod (measure := measure)
          configuration data analysis family)
        (globalCandidateAH10RobinContinuousPhysicalExtension period hPeriod
          (measure := measure) configuration data analysis family extensions)) :=
  global_candidateA_hessian_h10Robin_analytic_closure_gate period hPeriod
    (measure := measure) configuration data analysis einsteinScale
      hBoundaryTransverse family
      (globalCandidateAH10RobinContinuousBlockBounds period hPeriod
        (measure := measure) configuration data analysis family extensions)
      inverse

end
end P0EFTJanusProgramPGlobalHessianH10RobinContinuousClosure4D
end JanusFormal
