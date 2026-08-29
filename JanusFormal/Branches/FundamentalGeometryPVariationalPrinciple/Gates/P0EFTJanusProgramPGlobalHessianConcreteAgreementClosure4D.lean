import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalAgreement4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianBoundaryProjectionClosure4D

/-!
# Terminal H14 closure from the concrete boundary chart and dense agreements

This façade combines the two strongest reductions presently available before
H12:

* the local Robin block is the pullback of the genuine completed H10 action by
  the bounded metric-normal boundary projection already carried by the
  physical chart;
* the seven H11 extensions are supplied only as continuous bilinear forms with
  exact dense-core agreement.  Their symmetry is derived from the symmetry of
  the actual `C²` second Frechet derivatives.

The remaining H12 packet is the orthogonal finite-defect coercivity datum.  The
global shifted bound, shifted self-adjointness, dense range, surjectivity,
bounded inverse, generalized inverse, finite defects and Fredholm/index-zero
conclusions are all reconstructed downstream.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianConcreteAgreementClosure4D

set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option synthInstance.maxHeartbeats 3000000

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
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyBoundaryProjection4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalExtensions4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalCanonicalAgreement4D
open P0EFTJanusProgramPGlobalCandidateAAugmentedOrthogonalCoerciveShift4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalHessianBoundaryProjectionClosure4D

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

/-- Canonical symmetric H11 packet reconstructed from continuity and exact
agreement with the seven physical second derivatives on the dense core. -/
def globalCandidateAConcreteCanonicalExtensions
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
      period hPeriod (measure := measure) configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (extensions : GlobalCandidateASevenPhysicalCanonicalContinuousAgreements4D
      period hPeriod (measure := measure) configuration data analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hTransverse family)) :=
  extensions.toCanonical period hPeriod

/-- H11 physical extension generated from the agreement-only packet. -/
def globalCandidateAConcretePhysicalExtension
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
      period hPeriod (measure := measure) configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (extensions : GlobalCandidateASevenPhysicalCanonicalContinuousAgreements4D
      period hPeriod (measure := measure) configuration data analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hTransverse family)) :=
  globalCandidateABoundaryProjectionPhysicalExtension period hPeriod
    configuration data analysis einsteinScale hTransverse family
      (globalCandidateAConcreteCanonicalExtensions period hPeriod configuration
        data analysis einsteinScale hTransverse family extensions)

/-- Strongest current H14 gate: concrete H10 boundary projection, H11 agreement
only, and orthogonal finite-defect coercivity. -/
def global_candidateA_hessian_concreteAgreement_closure_gate
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
    (family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod (measure := measure) configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale)
    (extensions : GlobalCandidateASevenPhysicalCanonicalContinuousAgreements4D
      period hPeriod (measure := measure) configuration data analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hBoundaryTransverse family))
    (shift : GlobalCandidateAAugmentedOrthogonalCoerciveShift4D period hPeriod
      (measure := measure) configuration data analysis
        (globalCandidateABoundaryProjectionChart period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateABoundaryProjectionSameAction period hPeriod
          configuration data analysis einsteinScale hBoundaryTransverse family)
        (globalCandidateAConcretePhysicalExtension period hPeriod configuration
          data analysis einsteinScale hBoundaryTransverse family extensions)) :=
  global_candidateA_hessian_boundaryProjection_closure_gate period hPeriod
    (measure := measure) configuration data analysis einsteinScale
      hBoundaryTransverse family
      (globalCandidateAConcreteCanonicalExtensions period hPeriod configuration
        data analysis einsteinScale hBoundaryTransverse family extensions)
      shift

end
end P0EFTJanusProgramPGlobalHessianConcreteAgreementClosure4D
end JanusFormal
