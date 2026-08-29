import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10RobinReduction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianConstructiveAnalyticClosure4D

/-!
# H14 closure with the Robin block reconstructed from H10

This is the preferred composition after the normal-boundary same-action germ is
available.  The local Candidate-A family supplies `C²` regularity for only six
non-Robin physical blocks.  H10 transports the completed boundary regularity to
the actual Robin action, after which the existing seven-block H11 estimate and
H12 generalized inverse route apply unchanged.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianH10RobinAnalyticClosure4D

set_option autoImplicit false
set_option maxHeartbeats 3200000
set_option synthInstance.maxHeartbeats 1600000

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
open P0EFTJanusProgramPGlobalCandidateAAugmentedGeneralizedInverse4D
open P0EFTJanusProgramPGlobalHessianConstructiveAnalyticClosure4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D

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

/-- Convert the H10-supplied family only once for all downstream constructors. -/
def globalCandidateAH10RobinPhysicalC2Family
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
          couplings.matterMassSquared)) :=
  family.toPhysicalC2 period hPeriod (measure := measure)

/-- Canonical chart produced after the H10 Robin transfer. -/
def globalCandidateAH10RobinChart
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
          couplings.matterMassSquared)) :=
  globalCandidateAHessianConstructiveChart period hPeriod configuration data
    analysis
      (globalCandidateAH10RobinPhysicalC2Family period hPeriod
        (measure := measure) configuration data analysis family)

/-- Canonical matter--LL same-action bridge produced from the same family. -/
def globalCandidateAH10RobinSameAction
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
          couplings.matterMassSquared)) :=
  globalCandidateAHessianConstructiveSameAction period hPeriod configuration
    data analysis
      (globalCandidateAH10RobinPhysicalC2Family period hPeriod
        (measure := measure) configuration data analysis family)

/-- Seven-block H11 extension for an H10-supplied family. -/
def globalCandidateAH10RobinPhysicalExtension
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
    (bounds : GlobalCandidateASevenPhysicalBlockCoreBounds4D period hPeriod
      configuration data analysis
        (globalCandidateAH10RobinChart period hPeriod (measure := measure)
          configuration data analysis family)
        (globalCandidateAH10RobinSameAction period hPeriod (measure := measure)
          configuration data analysis family)) :=
  globalCandidateAHessianConstructivePhysicalExtension period hPeriod
    configuration data analysis
      (globalCandidateAH10RobinPhysicalC2Family period hPeriod
        (measure := measure) configuration data analysis family)
      bounds

/-- Repackage H10 Robin data, seven block bounds and the generalized inverse
into the existing three-input terminal interface. -/
def globalCandidateAH10RobinAnalyticInputs
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
    (bounds : GlobalCandidateASevenPhysicalBlockCoreBounds4D period hPeriod
      configuration data analysis
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
        (globalCandidateAH10RobinPhysicalExtension period hPeriod
          (measure := measure) configuration data analysis family bounds)) :
    GlobalCandidateAHessianDiracGreenBoundedInputs4D (measure := measure)
      period hPeriod
      configuration data analysis :=
  globalCandidateAHessianConstructiveAnalyticInputs period hPeriod
    (measure := measure)
    configuration data analysis
      (globalCandidateAH10RobinPhysicalC2Family period hPeriod
        (measure := measure) configuration data analysis family)
      bounds inverse

/-- Terminal H14 gate in which the Robin regularity and Hessian identity are
not independent inputs but consequences of the H10 same-action action germ. -/
def global_candidateA_hessian_h10Robin_analytic_closure_gate
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
    (bounds : GlobalCandidateASevenPhysicalBlockCoreBounds4D period hPeriod
      configuration data analysis
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
        (globalCandidateAH10RobinPhysicalExtension period hPeriod
          (measure := measure) configuration data analysis family bounds)) :=
  global_candidateA_hessian_diracGreen_bounded_closure_gate period hPeriod
    configuration data analysis einsteinScale hBoundaryTransverse
      (globalCandidateAH10RobinAnalyticInputs period hPeriod
        (measure := measure) configuration data analysis family bounds inverse)

end
end P0EFTJanusProgramPGlobalHessianH10RobinAnalyticClosure4D
end JanusFormal
