import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D

/-!
# Sector-covariant D11 representation of Candidate-A

A sector-preserving pointwise representation is upgraded here by requiring the
represented D11 source and target pullbacks to commute with the same five
physical projectors used by H12/H14.  Hence changing geometric representatives
cannot mix the physical sectors either.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorCovariance4D

set_option autoImplicit false
set_option maxHeartbeats 38000000
set_option synthInstance.maxHeartbeats 19000000
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D

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

variable
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    {configuration : GlobalGaugeFixedFieldConfiguration period hPeriod}
    {data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace}
    {analysis : GlobalAnalysisData period hPeriod configuration.physical}
    {einsteinScale : Real}
    {hTransverse : HasNoTangentialRadical period hPeriod
      data.plusGravity.metric.metric}
    {family : ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
      period hPeriod configuration data analysis
        (diracGreenClosureMatterRealization period hPeriod
          couplings.matterMassSquared) einsteinScale}
    {chartBound : DenseCoreChartMapBound
      (globalCandidateASevenPhysicalCoreEmbedding period hPeriod configuration
        data analysis)
      (globalCandidateACanonicalSixCoreToChart period hPeriod configuration data
        analysis
          (globalCandidateAActualKernelChart period hPeriod configuration data
            analysis einsteinScale hTransverse family)
          (globalCandidateAActualKernelSameAction period hPeriod configuration
            data analysis einsteinScale hTransverse family))}
    {Metric Abelian Matter Longitudinal Boundary : Type*}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type*} [Fintype ZeroMode] [DecidableEq ZeroMode]
    {fold : Fold} {Index : Type*}

/-- Exact sector-preserving D11 representation plus sector-preserving geometric
pullbacks. -/
structure GlobalHessianPreferredFiveSectorNaturalEllipticSectorCovariance4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index) : Prop where
  sectorRepresentation :
    GlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
      period hPeriod input
  pullback : FiveSectorNaturalRepresentationPullbackData
    sectorRepresentation.bridge.representation
    (preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input)
    sectorRepresentation.sectorRefinement

namespace GlobalHessianPreferredFiveSectorNaturalEllipticSectorCovariance4D

/-- Represented source pullback commutes with every physical projector. -/
theorem sourcePullback_commutes
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (data : GlobalHessianPreferredFiveSectorNaturalEllipticSectorCovariance4D
      period hPeriod input) :=
  data.pullback.source_commutes

/-- Represented target pullback commutes with every physical projector. -/
theorem targetPullback_commutes
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (data : GlobalHessianPreferredFiveSectorNaturalEllipticSectorCovariance4D
      period hPeriod input) :=
  data.pullback.target_commutes

/-- Public sector-covariant D11 representation checkpoint. -/
theorem global_hessian_preferred_five_sector_natural_elliptic_sector_covariance_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (data : GlobalHessianPreferredFiveSectorNaturalEllipticSectorCovariance4D
      period hPeriod input) :
    (∀ parameter,
      data.sectorRepresentation.bridge.representation.representedNaturalOperator
          parameter =
        fun state => input.familyIndex.baseFamily.actualOperator parameter state) ∧
    (∀ {first second : Real}
      (morphism : P0EFTJanusSpinCImmersionCategory.AdmissibleMorphism
        data.sectorRepresentation.bridge.immersionCategory
        (data.sectorRepresentation.bridge.representation.objectAt first)
        (data.sectorRepresentation.bridge.representation.objectAt second))
      (sector : FivePhysicalSector)
      (state : GlobalCandidateAFaithfulSameActionHilbert period hPeriod
        configuration data analysis),
      (preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input).
          sectorProjector sector
          (data.sectorRepresentation.bridge.representation.
            representedSourcePullback morphism state) =
        data.sectorRepresentation.bridge.representation.
          representedSourcePullback morphism
          ((preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input).
            sectorProjector sector state)) ∧
    (∀ {first second : Real}
      (morphism : P0EFTJanusSpinCImmersionCategory.AdmissibleMorphism
        data.sectorRepresentation.bridge.immersionCategory
        (data.sectorRepresentation.bridge.representation.objectAt first)
        (data.sectorRepresentation.bridge.representation.objectAt second))
      (sector : FivePhysicalSector)
      (state : GlobalCandidateAFaithfulSameActionHilbert period hPeriod
        configuration data analysis),
      (preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input).
          sectorProjector sector
          (data.sectorRepresentation.bridge.representation.
            representedTargetPullback morphism state) =
        data.sectorRepresentation.bridge.representation.
          representedTargetPullback morphism
          ((preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input).
            sectorProjector sector state)) :=
  ⟨data.sectorRepresentation.representedNaturalOperator_eq_actual
      period hPeriod input,
    data.pullback.source_commutes,
    data.pullback.target_commutes⟩

end GlobalHessianPreferredFiveSectorNaturalEllipticSectorCovariance4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorCovariance4D
end JanusFormal
