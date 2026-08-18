import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D

/-!
# Sector-preserving D11 representation of the preferred Candidate-A Hessian

The generic exact D11 representation is now constrained by the literal
five-sector completion geometry already used by the preferred H12/H14 route.
No second Hilbert decomposition is supplied.

The representation equivalences must factor through

`frontier.analytic.geometry.coordinates.coordinates`,

the same isometric decomposition whose projectors enter the actual Hessian
commutation, reduced Pythagoras and coercive gap proofs.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D

set_option autoImplicit false
set_option maxHeartbeats 36000000
set_option synthInstance.maxHeartbeats 18000000
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
open P0EFTJanusProgramPGlobalLocalVariationalChart4D
open P0EFTJanusProgramPGlobalCandidateAMatterLLSameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalActionFamilyH10Reduction4D
open P0EFTJanusProgramPGlobalCandidateACanonicalSixDenseCore4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPGlobalHessianDiracGreenBoundedClosure4D
open P0EFTJanusProgramPGlobalCandidateASevenPhysicalBlockBounds4D
open P0EFTJanusProgramPGlobalHessianActualKernelFrontier4D
open P0EFTJanusProgramPGlobalCandidateAFaithfulFredholmSum4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusCircleDiracHeatTraceCancellation

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertNormedAddCommGroup
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertInnerProductSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertNormedSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertModule
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertCompleteSpace

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

variable {measure : Measure (EffectiveQuotient period hPeriod)}

local instance (priority := 40000) preferredCandidateAHilbertModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*} [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (GlobalHessianPreferredFiveSectorBismutFreedHilbert4D period hPeriod
        configuration data analysis) :=
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertModule
    period hPeriod configuration data analysis

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
      (measure := measure) period hPeriod configuration data analysis
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
    {Metric Abelian Matter Longitudinal Boundary : Type}
    [NormedAddCommGroup Metric] [InnerProductSpace Real Metric]
    [NormedAddCommGroup Abelian] [InnerProductSpace Real Abelian]
    [NormedAddCommGroup Matter] [InnerProductSpace Real Matter]
    [NormedAddCommGroup Longitudinal] [InnerProductSpace Real Longitudinal]
    [NormedAddCommGroup Boundary] [InnerProductSpace Real Boundary]
    {ZeroMode : Type} [Fintype ZeroMode] [DecidableEq ZeroMode]
    {fold : Fold} {Index : Type*}

/-- The unique five-sector Hilbert coordinates already embedded in the H12/H14
basepoint closure. -/
def preferredCandidateAFiveSectorHilbertCoordinates
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index) :
    FiveSectorHilbertCoordinates
      (E := GlobalHessianPreferredFiveSectorBismutFreedHilbert4D period hPeriod
        configuration data analysis)
      (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary) :=
  input.familyIndex.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.frontier.analytic.geometry.coordinates.coordinates

/-- Exact D11 representation together with proof that its source and target
coordinates factor through the one physical five-sector Candidate-A isometry. -/
structure GlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index) where
  bridge : GlobalHessianPreferredFiveSectorNaturalEllipticRepresentation4D
    period hPeriod input
  sectorRefinement : FiveSectorNaturalRepresentationRefinementData.{0, 0, 0, 0, 0, 0,
    0, 0, 0, 0, 0, 0, 0, 0, 0, 0}
    bridge.representation (preferredCandidateAFiveSectorHilbertCoordinates
      period hPeriod input)

namespace GlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D

/-- The refined representation still conjugates the D11 operator to the exact
Candidate-A actual Hessian. -/
theorem representedNaturalOperator_eq_actual
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (refined : GlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
      period hPeriod input)
    (parameter : Real) :
    refined.bridge.representation.representedNaturalOperator parameter =
      fun state => input.familyIndex.baseFamily.actualOperator parameter state :=
  refined.bridge.representedNaturalOperator_eq_actual period hPeriod input parameter

/-- Source sections recover exactly their five physical coordinates in the same
Hilbert decomposition used by the actual Hessian projectors. -/
def source_allCoordinates
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (refined : GlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
      period hPeriod input)
    (parameter : Real)
    (sectionValue : refined.bridge.naturalFamily.sourceFunctor.Section
      (refined.bridge.representation.objectAt parameter)) :=
  refined.sectorRefinement.source_allCoordinates
    refined.bridge.representation
    (preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input)
    parameter sectionValue

/-- Target sections obey the same five-sector factorization. -/
def target_allCoordinates
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (refined : GlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
      period hPeriod input)
    (parameter : Real)
    (sectionValue : refined.bridge.naturalFamily.targetFunctor.Section
      (refined.bridge.representation.objectAt parameter)) :=
  refined.sectorRefinement.target_allCoordinates
    refined.bridge.representation
    (preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input)
    parameter sectionValue

/-- Public sector-preserving D11/Candidate-A representation checkpoint. -/
theorem global_hessian_preferred_five_sector_natural_elliptic_sector_representation_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (refined : GlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
      period hPeriod input) :
    (∀ parameter,
      refined.bridge.representation.representedNaturalOperator parameter =
        fun state => input.familyIndex.baseFamily.actualOperator parameter state) ∧
    (∀ parameter,
      refined.bridge.representation.sourceEquiv parameter =
        (refined.sectorRefinement.sourceProductEquiv parameter).trans
          ((refined.sectorRefinement.sourceSectorCoordinates parameter).ambientEquiv
              (preferredCandidateAFiveSectorHilbertCoordinates
                period hPeriod input))) ∧
    (∀ parameter,
      refined.bridge.representation.targetEquiv parameter =
        (refined.sectorRefinement.targetProductEquiv parameter).trans
          ((refined.sectorRefinement.targetSectorCoordinates parameter).ambientEquiv
              (preferredCandidateAFiveSectorHilbertCoordinates
                period hPeriod input))) :=
  ⟨refined.representedNaturalOperator_eq_actual period hPeriod input,
    refined.sectorRefinement.sourceEquiv_agreement,
    refined.sectorRefinement.targetEquiv_agreement⟩

end GlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
end JanusFormal
