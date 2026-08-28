import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorConcreteNaturalMetrics4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalAnalyticPathUpgrade4D

/-!
# Concrete metric version of the Candidate-A D11 path geometry

The represented section metrics and the two regular gravitational/Maxwell
metric packets are now actual Lean data.  Consequently the two D11 metric
status fields are no longer freely supplied propositions in the preferred
path geometry.

The remaining geometric obstruction is stated honestly: construction of a
global natural connection compatible with the local Levi--Civita/gauge data.
The current Program-P geometry constructs the relevant local coefficients but
not yet their global overlap descent.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorConcreteNaturalPathGeometry4D

set_option autoImplicit false
set_option maxHeartbeats 34000000
set_option synthInstance.maxHeartbeats 17000000
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalAnalyticPathUpgrade4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorConcreteNaturalMetrics4D
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

/-- Preferred path geometry after replacing both metric status flags by one
concrete Candidate-A metric packet. -/
structure GlobalHessianPreferredFiveSectorConcreteNaturalPathGeometryData4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (bridge : GlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D period hPeriod input) where
  metricData :
    GlobalHessianPreferredFiveSectorConcreteNaturalMetricData4D period hPeriod input bridge
  naturalConnectionsConstructed : Prop
  naturalConnectionsConstructed_proof : naturalConnectionsConstructed
  normalRootBoundaryDomainsIncluded : Prop
  gaugeEquivariantFamilyConstructed : Prop

namespace GlobalHessianPreferredFiveSectorConcreteNaturalPathGeometryData4D

/-- Forget to the older status-style path geometry.  Its two metric propositions
are now inhabited by an explicit metric object. -/
def toStatusGeometry
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (bridge : GlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D period hPeriod input)
    (geometry : GlobalHessianPreferredFiveSectorConcreteNaturalPathGeometryData4D period hPeriod input bridge) :
    GlobalHessianPreferredFiveSectorNaturalPathGeometryData4D period hPeriod input bridge where
  smoothFiberMetricsChosen :=
    Nonempty (NaturalEllipticRepresentationMetricData bridge.representation)
  smoothFiberMetricsChosen_proof := ⟨geometry.metricData.representedMetrics⟩
  naturalBundleMetricsChosen :=
    Nonempty (GlobalHessianPreferredFiveSectorConcreteNaturalMetricData4D
      period hPeriod input bridge)
  naturalBundleMetricsChosen_proof := ⟨geometry.metricData⟩
  naturalConnectionsConstructed := geometry.naturalConnectionsConstructed
  naturalConnectionsConstructed_proof := geometry.naturalConnectionsConstructed_proof
  normalRootBoundaryDomainsIncluded := geometry.normalRootBoundaryDomainsIncluded
  gaugeEquivariantFamilyConstructed := geometry.gaugeEquivariantFamilyConstructed

/-- The ordinary D11 Quillen input now closes from concrete metrics plus the one
remaining global-connection theorem. -/
theorem concreteNaturalPathGeometry_closes_quillen_input
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (bridge : GlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D period hPeriod input)
    (geometry : GlobalHessianPreferredFiveSectorConcreteNaturalPathGeometryData4D period hPeriod input bridge) :
    P0EFTJanusQuillenFamilyCanonicity.ellipticFamilyInputClosed
      (P0EFTJanusNaturalFamilyQuillenBridge.toEllipticFamilyInputStatus
        (candidateANaturalAnalyticPathUpgrade period hPeriod input bridge
          (geometry.toStatusGeometry period hPeriod input bridge))) :=
  candidateANaturalAnalyticPathUpgrade_closes_quillen_input
    period hPeriod input bridge
      (geometry.toStatusGeometry period hPeriod input bridge)

/-- Public constructive-metric path checkpoint. -/
theorem global_hessian_preferred_five_sector_concrete_natural_path_geometry_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (bridge : GlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D period hPeriod input)
    (geometry : GlobalHessianPreferredFiveSectorConcreteNaturalPathGeometryData4D period hPeriod input bridge) :
    Nonempty (NaturalEllipticRepresentationMetricData bridge.representation) ∧
    Nonempty (GlobalHessianPreferredFiveSectorConcreteNaturalMetricData4D period hPeriod input bridge) ∧
    geometry.naturalConnectionsConstructed ∧
    P0EFTJanusQuillenFamilyCanonicity.ellipticFamilyInputClosed
      (P0EFTJanusNaturalFamilyQuillenBridge.toEllipticFamilyInputStatus
        (candidateANaturalAnalyticPathUpgrade period hPeriod input bridge
          (geometry.toStatusGeometry period hPeriod input bridge))) :=
  ⟨⟨geometry.metricData.representedMetrics⟩,
    ⟨geometry.metricData⟩,
    geometry.naturalConnectionsConstructed_proof,
    geometry.concreteNaturalPathGeometry_closes_quillen_input period hPeriod input bridge⟩

end GlobalHessianPreferredFiveSectorConcreteNaturalPathGeometryData4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorConcreteNaturalPathGeometry4D
end JanusFormal
