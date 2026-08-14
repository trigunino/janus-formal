import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPNaturalEllipticRepresentationMetric4D

/-!
# Concrete metric geometry for the represented Candidate-A D11 family

The D11 analytic status previously stored "smooth fibre metrics chosen" and
"natural bundle metrics chosen" only as propositions.  For the preferred
Candidate-A route both can be tied to data already present:

* the represented source/target section metrics are the pullback of the actual
  Candidate-A Hilbert inner product;
* the two global regular Lorentz metrics and their Maxwell lines are the exact
  geometric data used by the Candidate-A action.

This file packages those objects without asserting a global natural connection,
which remains a separate geometric theorem.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorConcreteNaturalMetrics4D

set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option synthInstance.maxHeartbeats 16000000
noncomputable section

open Set Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D
open P0EFTJanusProgramPNaturalEllipticRepresentationMetric4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance effectiveQuotientChartedSpace : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance effectiveQuotientIsManifold : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance effectiveQuotientMeasurableSpace : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance effectiveQuotientBorelSpace : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D period hPeriod configuration data analysis
      (diracGreenClosureMatterRealization period hPeriod couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data analysis
        (globalCandidateAActualKernelChart period hPeriod configuration data analysis einsteinScale hTransverse family)
        (globalCandidateAActualKernelSameAction period hPeriod configuration data analysis einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type*} [Fintype ZeroMode] [DecidableEq ZeroMode]
    {fold : Fold} {Index : Type*}

/-- Data-bearing metric packet for the exact D11 representation of Candidate-A. -/
structure GlobalHessianPreferredFiveSectorConcreteNaturalMetricData4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (bridge : GlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D period hPeriod input) where
  representedMetrics :
    NaturalEllipticRepresentationMetricData bridge.representation
  plusGravity : P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D.
    RegularEinsteinHilbertMetric period hPeriod
  minusGravity : P0EFTJanusMappingTorusIntrinsicEinsteinHilbertAction4D.
    RegularEinsteinHilbertMetric period hPeriod
  plusMaxwell : P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D.
    RegularIntrinsicMaxwellLine period hPeriod plusGravity.metric
  minusMaxwell : P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D.
    RegularIntrinsicMaxwellLine period hPeriod minusGravity.metric
  plusGravity_eq : plusGravity = data.plusGravity
  minusGravity_eq : minusGravity = data.minusGravity

/-- Canonical concrete metric packet: no metric choice beyond the existing
Candidate-A action data is introduced. -/
def globalHessianPreferredFiveSectorConcreteNaturalMetricData
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (bridge : GlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D period hPeriod input) :
    GlobalHessianPreferredFiveSectorConcreteNaturalMetricData4D period hPeriod input bridge where
  representedMetrics := bridge.representation.canonicalMetricData
  plusGravity := data.plusGravity
  minusGravity := data.minusGravity
  plusMaxwell := data.plusMaxwell
  minusMaxwell := data.minusMaxwell
  plusGravity_eq := rfl
  minusGravity_eq := rfl

/-- The represented state metric is smooth in the family parameter. -/
theorem candidateARepresentedMetric_contDiff
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (bridge : GlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D period hPeriod input)
    (first second : GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data analysis) :
    ContDiff Real ∞ (fun parameter : Real =>
      NaturalEllipticOperatorRepresentationData.representedStatePairing
        parameter first second) :=
  NaturalEllipticOperatorRepresentationData.representedStatePairing_contDiff first second

/-- Public constructive metric checkpoint. -/
theorem global_hessian_preferred_five_sector_concrete_natural_metric_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (bridge : GlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D period hPeriod input) :
    Nonempty (GlobalHessianPreferredFiveSectorConcreteNaturalMetricData4D period hPeriod input bridge) ∧
    (∀ first second : GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data analysis,
      ContDiff Real ∞ (fun parameter : Real =>
        NaturalEllipticOperatorRepresentationData.representedStatePairing
          parameter first second)) :=
  ⟨⟨globalHessianPreferredFiveSectorConcreteNaturalMetricData period hPeriod input bridge⟩,
    candidateARepresentedMetric_contDiff period hPeriod input bridge⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorConcreteNaturalMetrics4D
end JanusFormal
