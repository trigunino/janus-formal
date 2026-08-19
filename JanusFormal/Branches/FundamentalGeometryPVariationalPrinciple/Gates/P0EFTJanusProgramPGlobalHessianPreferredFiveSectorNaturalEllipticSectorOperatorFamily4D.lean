import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorCovariance4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorRepresentedOperatorCoordinates4D

/-!
# Five-sector natural operator family representing Candidate-A

The exact D11 representation is now required to satisfy three independent
physical constraints:

* source/target coordinates factor through the one H12/H14 five-sector isometry;
* represented geometric pullbacks preserve those sectors;
* the natural operator itself is componentwise in the corresponding source and
  target sector section types.

The resulting fixed-Hilbert formula is therefore an exact five-block formula
for the genuine `actualOperator a` at every represented parameter.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000
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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorCovariance4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationOperatorFactorization4D
open P0EFTJanusProgramPFiveSectorRepresentedOperatorCoordinates4D
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

/-- Sector-covariant D11 representation together with an exact componentwise
factorization of its natural operator. -/
structure GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index) where
  covariance :
    GlobalHessianPreferredFiveSectorNaturalEllipticSectorCovariance4D
      period hPeriod input
  operatorFactorization :
    FiveSectorNaturalRepresentationOperatorFactorizationData
      covariance.sectorRepresentation.bridge.representation
      (preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input)
      covariance.sectorRepresentation.sectorRefinement

namespace GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D

private abbrev Coordinates
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index) :=
  preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input

/-- Exact five-block formula for the genuine Candidate-A family in the one
fixed H12/H14 Hilbert coordinate system. -/
theorem actualOperator_blockFormula
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (operatorFamily : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : Real)
    (state : P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.GlobalHessianPreferredFiveSectorBismutFreedHilbert4D period hPeriod
      configuration data analysis) :
    (Coordinates period hPeriod input).decomposition
        (input.familyIndex.baseFamily.actualOperator parameter state) =
      fiveSectorMetricAxis
          (operatorFamily.operatorFactorization.representedMetricBlock
            operatorFamily.covariance.sectorRepresentation.bridge.representation
            (Coordinates period hPeriod input)
            operatorFamily.covariance.sectorRepresentation.sectorRefinement parameter
            (fiveSectorMetricCoordinate
              ((Coordinates period hPeriod input).decomposition state))) +
        fiveSectorAbelianAxis
          (operatorFamily.operatorFactorization.representedAbelianBlock
            operatorFamily.covariance.sectorRepresentation.bridge.representation
            (Coordinates period hPeriod input)
            operatorFamily.covariance.sectorRepresentation.sectorRefinement parameter
            (fiveSectorAbelianCoordinate
              ((Coordinates period hPeriod input).decomposition state))) +
        fiveSectorMatterAxis
          (operatorFamily.operatorFactorization.representedMatterBlock
            operatorFamily.covariance.sectorRepresentation.bridge.representation
            (Coordinates period hPeriod input)
            operatorFamily.covariance.sectorRepresentation.sectorRefinement parameter
            (fiveSectorMatterCoordinate
              ((Coordinates period hPeriod input).decomposition state))) +
        fiveSectorLongitudinalAxis
          (operatorFamily.operatorFactorization.representedLongitudinalBlock
            operatorFamily.covariance.sectorRepresentation.bridge.representation
            (Coordinates period hPeriod input)
            operatorFamily.covariance.sectorRepresentation.sectorRefinement parameter
            (fiveSectorLongitudinalCoordinate
              ((Coordinates period hPeriod input).decomposition state))) +
        fiveSectorBoundaryAxis
          (operatorFamily.operatorFactorization.representedBoundaryBlock
            operatorFamily.covariance.sectorRepresentation.bridge.representation
            (Coordinates period hPeriod input)
            operatorFamily.covariance.sectorRepresentation.sectorRefinement parameter
            (fiveSectorBoundaryCoordinate
              ((Coordinates period hPeriod input).decomposition state))) := by
  have hOperator := congrArg (fun operator => operator state)
    (operatorFamily.covariance.sectorRepresentation.bridge.representedNaturalOperator_eq_actual
      period hPeriod input parameter)
  calc
    _ = (Coordinates period hPeriod input).decomposition
        (operatorFamily.covariance.sectorRepresentation.bridge.representation.representedNaturalOperator
          parameter state) :=
      congrArg (Coordinates period hPeriod input).decomposition hOperator.symm
    _ = _ :=
      P0EFTJanusProgramPFiveSectorRepresentedOperatorCoordinates4D.FiveSectorNaturalRepresentationOperatorFactorizationData.representedNaturalOperator_blockFormula
        operatorFamily.covariance.sectorRepresentation.bridge.representation
        (Coordinates period hPeriod input)
        operatorFamily.covariance.sectorRepresentation.sectorRefinement
        operatorFamily.operatorFactorization parameter state

/-- Public all-parameter five-sector D11/Candidate-A checkpoint. -/
theorem global_hessian_preferred_five_sector_natural_elliptic_sector_operator_family_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index)
    (operatorFamily : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) :
    (∀ parameter,
      operatorFamily.covariance.sectorRepresentation.bridge.representation.representedNaturalOperator
          parameter =
        fun state => input.familyIndex.baseFamily.actualOperator parameter state) ∧
    (∀ parameter state,
      (Coordinates period hPeriod input).decomposition
          (input.familyIndex.baseFamily.actualOperator parameter state) =
        fiveSectorMetricAxis
            (operatorFamily.operatorFactorization.representedMetricBlock
              operatorFamily.covariance.sectorRepresentation.bridge.representation
              (Coordinates period hPeriod input)
              operatorFamily.covariance.sectorRepresentation.sectorRefinement parameter
              (fiveSectorMetricCoordinate
                ((Coordinates period hPeriod input).decomposition state))) +
          fiveSectorAbelianAxis
            (operatorFamily.operatorFactorization.representedAbelianBlock
              operatorFamily.covariance.sectorRepresentation.bridge.representation
              (Coordinates period hPeriod input)
              operatorFamily.covariance.sectorRepresentation.sectorRefinement parameter
              (fiveSectorAbelianCoordinate
                ((Coordinates period hPeriod input).decomposition state))) +
          fiveSectorMatterAxis
            (operatorFamily.operatorFactorization.representedMatterBlock
              operatorFamily.covariance.sectorRepresentation.bridge.representation
              (Coordinates period hPeriod input)
              operatorFamily.covariance.sectorRepresentation.sectorRefinement parameter
              (fiveSectorMatterCoordinate
                ((Coordinates period hPeriod input).decomposition state))) +
          fiveSectorLongitudinalAxis
            (operatorFamily.operatorFactorization.representedLongitudinalBlock
              operatorFamily.covariance.sectorRepresentation.bridge.representation
              (Coordinates period hPeriod input)
              operatorFamily.covariance.sectorRepresentation.sectorRefinement parameter
              (fiveSectorLongitudinalCoordinate
                ((Coordinates period hPeriod input).decomposition state))) +
          fiveSectorBoundaryAxis
            (operatorFamily.operatorFactorization.representedBoundaryBlock
              operatorFamily.covariance.sectorRepresentation.bridge.representation
              (Coordinates period hPeriod input)
              operatorFamily.covariance.sectorRepresentation.sectorRefinement parameter
              (fiveSectorBoundaryCoordinate
                ((Coordinates period hPeriod input).decomposition state)))) :=
  ⟨operatorFamily.covariance.sectorRepresentation.representedNaturalOperator_eq_actual
      period hPeriod input,
    operatorFamily.actualOperator_blockFormula period hPeriod input⟩

end GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
end JanusFormal
