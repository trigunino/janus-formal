import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorConcreteNaturalMetrics4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D

/-!
# Concrete connection-descent data for the preferred Candidate-A geometry

The canonical quotient-atlas transition theorem proves the genuine
Levi--Civita transformation law, including the second derivative of the
coordinate change.  Hence the plus/minus local Levi--Civita coefficients of the
actual Candidate-A metrics form an honest atlas-descent packet; no freely
supplied overlap compatibility proposition is needed.

The same packet retains the global Abelian gauge potentials and regular Maxwell
lines already used by the Candidate-A action.  This is a data-bearing
connection frontier, not a Boolean "connection constructed" flag.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorConcreteNaturalConnections4D

set_option autoImplicit false
set_option maxHeartbeats 34000000
set_option synthInstance.maxHeartbeats 17000000
noncomputable section

open Set Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGlobalAnalysisDomain4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D
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

/-- Actual atlas-descent data for the two gravitational Levi--Civita
connections together with the global Abelian gauge potentials. -/
structure GlobalHessianPreferredFiveSectorConcreteNaturalConnectionData4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) where
  plusTransition : ∀
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate),
    HolonomicLeviCivitaTransitionAgreement period hPeriod
      data.plusGravity.metric.metric firstPatch secondPatch
        firstCoordinate secondCoordinate
  minusTransition : ∀
    (firstPatch secondPatch : SmoothHolonomicFrameChart4 period hPeriod)
    (firstCoordinate secondCoordinate : Vector4)
    (samePoint : firstPatch.coordinateMap firstCoordinate =
      secondPatch.coordinateMap secondCoordinate),
    HolonomicLeviCivitaTransitionAgreement period hPeriod
      data.minusGravity.metric.metric firstPatch secondPatch
        firstCoordinate secondCoordinate
  plusGaugePotential :
    P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D.
      SmoothAbelianGaugePotential period hPeriod
  minusGaugePotential :
    P0EFTJanusMappingTorusIntrinsicAbelianMaxwellAction4D.
      SmoothAbelianGaugePotential period hPeriod
  plusGaugePotential_eq : plusGaugePotential = data.plusMaxwell.potential
  minusGaugePotential_eq : minusGaugePotential = data.minusMaxwell.potential

/-- Canonical connection-descent packet generated entirely from the existing
Candidate-A action data and the real quotient-atlas transition theorem. -/
def globalHessianPreferredFiveSectorConcreteNaturalConnectionData
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    GlobalHessianPreferredFiveSectorConcreteNaturalConnectionData4D period hPeriod input where
  plusTransition := by
    intro firstPatch secondPatch firstCoordinate secondCoordinate samePoint
    exact canonicalHolonomicLeviCivitaTransitionAgreement period hPeriod
      data.plusGravity.metric.metric firstPatch secondPatch
        firstCoordinate secondCoordinate samePoint
  minusTransition := by
    intro firstPatch secondPatch firstCoordinate secondCoordinate samePoint
    exact canonicalHolonomicLeviCivitaTransitionAgreement period hPeriod
      data.minusGravity.metric.metric firstPatch secondPatch
        firstCoordinate secondCoordinate samePoint
  plusGaugePotential := data.plusMaxwell.potential
  minusGaugePotential := data.minusMaxwell.potential
  plusGaugePotential_eq := rfl
  minusGaugePotential_eq := rfl

/-- Public constructive connection-descent checkpoint. -/
theorem global_hessian_preferred_five_sector_concrete_natural_connection_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod configuration data analysis
      einsteinScale hTransverse family chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :
    Nonempty (GlobalHessianPreferredFiveSectorConcreteNaturalConnectionData4D
      period hPeriod input) :=
  ⟨globalHessianPreferredFiveSectorConcreteNaturalConnectionData
    period hPeriod input⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorConcreteNaturalConnections4D
end JanusFormal
