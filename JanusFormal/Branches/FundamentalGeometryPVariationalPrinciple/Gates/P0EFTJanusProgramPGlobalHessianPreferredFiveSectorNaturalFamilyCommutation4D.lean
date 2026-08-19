import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorComponentwiseProductMap4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorHilbertProjectorCoordinates4D

/-!
# All-parameter sector commutation from the natural D11 factorization

At H12 the actual Candidate-A Hessian is known to commute with the five physical
projectors at the base parameter.  A sectorwise D11 operator factorization gives
a stronger family statement.

Because every `actualOperator a` is a continuous linear map, its five represented
component maps vanish at zero.  The componentwise product map therefore commutes
with each raw coordinate projector, and conjugating back through the one
H12/H14 Hilbert isometry proves

`H_a P_s = P_s H_a`

for every represented parameter.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalFamilyCommutation4D

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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPFiveSectorComponentwiseProductMap4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorHilbertProjectorCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationOperatorFactorization4D
open P0EFTJanusProgramPFiveSectorRepresentedOperatorCoordinates4D
open P0EFTJanusProgramPFiveSectorRepresentedOperatorCoordinates4D.FiveSectorNaturalRepresentationOperatorFactorizationData
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

private abbrev Coordinates
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index) :=
  preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input

/-- Apply one preferred physical-sector projector without exposing its
instance-sensitive continuous-linear-map representation. -/
def preferredSectorProjectorApply
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (sector : FivePhysicalSector)
    (state : P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.GlobalHessianPreferredFiveSectorBismutFreedHilbert4D period hPeriod
      configuration data analysis) :=
  (Coordinates period hPeriod input).sectorProjector sector state

@[simp]
theorem preferredSectorProjectorApply_zero
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (sector : FivePhysicalSector) :
    preferredSectorProjectorApply period hPeriod input sector
        (0 : P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.GlobalHessianPreferredFiveSectorBismutFreedHilbert4D period hPeriod
          configuration data analysis) = 0 := by
  unfold preferredSectorProjectorApply
  exact ContinuousLinearMap.map_zero _

theorem continuous_preferredSectorProjectorApply
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (sector : FivePhysicalSector) :
    Continuous (preferredSectorProjectorApply period hPeriod input sector) := by
  unfold preferredSectorProjectorApply
  exact (Coordinates period hPeriod input).sectorProjector sector |>.continuous

private def MetricBlock
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) (parameter : Real) : Metric → Metric :=
  natural.operatorFactorization.representedMetricBlock
    natural.covariance.sectorRepresentation.bridge.representation
    (Coordinates period hPeriod input)
    natural.covariance.sectorRepresentation.sectorRefinement parameter

private def AbelianBlock
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) (parameter : Real) : Abelian → Abelian :=
  natural.operatorFactorization.representedAbelianBlock
    natural.covariance.sectorRepresentation.bridge.representation
    (Coordinates period hPeriod input)
    natural.covariance.sectorRepresentation.sectorRefinement parameter

private def MatterBlock
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) (parameter : Real) : Matter → Matter :=
  natural.operatorFactorization.representedMatterBlock
    natural.covariance.sectorRepresentation.bridge.representation
    (Coordinates period hPeriod input)
    natural.covariance.sectorRepresentation.sectorRefinement parameter

private def LongitudinalBlock
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) (parameter : Real) : Longitudinal → Longitudinal :=
  natural.operatorFactorization.representedLongitudinalBlock
    natural.covariance.sectorRepresentation.bridge.representation
    (Coordinates period hPeriod input)
    natural.covariance.sectorRepresentation.sectorRefinement parameter

private def BoundaryBlock
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) (parameter : Real) : Boundary → Boundary :=
  natural.operatorFactorization.representedBoundaryBlock
    natural.covariance.sectorRepresentation.bridge.representation
    (Coordinates period hPeriod input)
    natural.covariance.sectorRepresentation.sectorRefinement parameter

private theorem metricBlock_zero
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) (parameter : Real) :
    MetricBlock period hPeriod input natural parameter 0 = 0 := by
  have h := representedNaturalOperator_metricCoordinate
    natural.covariance.sectorRepresentation.bridge.representation
    (Coordinates period hPeriod input)
    natural.covariance.sectorRepresentation.sectorRefinement
    natural.operatorFactorization parameter
    (0 : P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.GlobalHessianPreferredFiveSectorBismutFreedHilbert4D period hPeriod configuration
      data analysis)
  rw [natural.covariance.sectorRepresentation.bridge.representedNaturalOperator_eq_actual
    period hPeriod input parameter] at h
  simpa [MetricBlock] using h.symm

private theorem abelianBlock_zero
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) (parameter : Real) :
    AbelianBlock period hPeriod input natural parameter 0 = 0 := by
  have h := representedNaturalOperator_abelianCoordinate
    natural.covariance.sectorRepresentation.bridge.representation
    (Coordinates period hPeriod input)
    natural.covariance.sectorRepresentation.sectorRefinement
    natural.operatorFactorization parameter
    (0 : P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.GlobalHessianPreferredFiveSectorBismutFreedHilbert4D period hPeriod configuration
      data analysis)
  rw [natural.covariance.sectorRepresentation.bridge.representedNaturalOperator_eq_actual
    period hPeriod input parameter] at h
  simpa [AbelianBlock] using h.symm

private theorem matterBlock_zero
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) (parameter : Real) :
    MatterBlock period hPeriod input natural parameter 0 = 0 := by
  have h := representedNaturalOperator_matterCoordinate
    natural.covariance.sectorRepresentation.bridge.representation
    (Coordinates period hPeriod input)
    natural.covariance.sectorRepresentation.sectorRefinement
    natural.operatorFactorization parameter
    (0 : P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.GlobalHessianPreferredFiveSectorBismutFreedHilbert4D period hPeriod configuration
      data analysis)
  rw [natural.covariance.sectorRepresentation.bridge.representedNaturalOperator_eq_actual
    period hPeriod input parameter] at h
  simpa [MatterBlock] using h.symm

private theorem longitudinalBlock_zero
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) (parameter : Real) :
    LongitudinalBlock period hPeriod input natural parameter 0 = 0 := by
  have h := representedNaturalOperator_longitudinalCoordinate
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.operatorFactorization parameter
      (0 : P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.GlobalHessianPreferredFiveSectorBismutFreedHilbert4D period hPeriod configuration
        data analysis)
  rw [natural.covariance.sectorRepresentation.bridge.representedNaturalOperator_eq_actual
    period hPeriod input parameter] at h
  simpa [LongitudinalBlock] using h.symm

private theorem boundaryBlock_zero
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) (parameter : Real) :
    BoundaryBlock period hPeriod input natural parameter 0 = 0 := by
  have h := representedNaturalOperator_boundaryCoordinate
    natural.covariance.sectorRepresentation.bridge.representation
    (Coordinates period hPeriod input)
    natural.covariance.sectorRepresentation.sectorRefinement
    natural.operatorFactorization parameter
    (0 : P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.GlobalHessianPreferredFiveSectorBismutFreedHilbert4D period hPeriod configuration
      data analysis)
  rw [natural.covariance.sectorRepresentation.bridge.representedNaturalOperator_eq_actual
    period hPeriod input parameter] at h
  simpa [BoundaryBlock] using h.symm

private theorem actualOperator_componentwise
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) (parameter : Real)
    (state : P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.GlobalHessianPreferredFiveSectorBismutFreedHilbert4D period hPeriod
      configuration data analysis) :
    (Coordinates period hPeriod input).decomposition
        (input.familyIndex.baseFamily.actualOperator parameter state) =
      fiveSectorComponentwiseMap
        (MetricBlock period hPeriod input natural parameter)
        (AbelianBlock period hPeriod input natural parameter)
        (MatterBlock period hPeriod input natural parameter)
        (LongitudinalBlock period hPeriod input natural parameter)
        (BoundaryBlock period hPeriod input natural parameter)
        ((Coordinates period hPeriod input).decomposition state) := by
  rw [natural.actualOperator_blockFormula period hPeriod input parameter state]
  rcases (Coordinates period hPeriod input).decomposition state with
    ⟨metric, abelian, matter, longitudinal, boundary⟩
  simp [fiveSectorComponentwiseMap, MetricBlock, AbelianBlock, MatterBlock,
    LongitudinalBlock, BoundaryBlock, fiveSectorMetricAxis,
    fiveSectorAbelianAxis, fiveSectorMatterAxis, fiveSectorLongitudinalAxis,
    fiveSectorBoundaryAxis, fiveSectorMetricCoordinate,
    fiveSectorAbelianCoordinate, fiveSectorMatterCoordinate,
    fiveSectorLongitudinalCoordinate, fiveSectorBoundaryCoordinate]

private theorem decomposition_sectorProjector_eq_raw
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (sector : FivePhysicalSector)
    (state : P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.GlobalHessianPreferredFiveSectorBismutFreedHilbert4D period hPeriod
      configuration data analysis) :
    (Coordinates period hPeriod input).decomposition
        ((Coordinates period hPeriod input).sectorProjector sector state) =
      fiveSectorProductProjector sector
        ((Coordinates period hPeriod input).decomposition state) := by
  cases sector <;>
    simp [fiveSectorProductProjector,
      FiveSectorHilbertCoordinates.decomposition_sectorProjector,
      fiveSectorMetricAxis, fiveSectorAbelianAxis, fiveSectorMatterAxis,
      fiveSectorLongitudinalAxis, fiveSectorBoundaryAxis,
      fiveSectorMetricCoordinate, fiveSectorAbelianCoordinate,
      fiveSectorMatterCoordinate, fiveSectorLongitudinalCoordinate,
      fiveSectorBoundaryCoordinate] <;> rfl

/-- Every member of the represented Candidate-A family commutes with the same
five physical projectors. -/
theorem actualOperator_commutes_sectorProjector
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (parameter : Real) (sector : FivePhysicalSector)
    (state : P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.GlobalHessianPreferredFiveSectorBismutFreedHilbert4D period hPeriod
      configuration data analysis) :
    input.familyIndex.baseFamily.actualOperator parameter
        (preferredSectorProjectorApply period hPeriod input sector state) =
      preferredSectorProjectorApply period hPeriod input sector
        (input.familyIndex.baseFamily.actualOperator parameter state) := by
  unfold preferredSectorProjectorApply
  apply (Coordinates period hPeriod input).decomposition.injective
  rw [actualOperator_componentwise period hPeriod input natural parameter]
  rw [decomposition_sectorProjector_eq_raw period hPeriod input]
  rw [fiveSectorComponentwiseMap_commutes_projector
    (MetricBlock period hPeriod input natural parameter)
    (AbelianBlock period hPeriod input natural parameter)
    (MatterBlock period hPeriod input natural parameter)
    (LongitudinalBlock period hPeriod input natural parameter)
    (BoundaryBlock period hPeriod input natural parameter)
    (metricBlock_zero period hPeriod input natural parameter)
    (abelianBlock_zero period hPeriod input natural parameter)
    (matterBlock_zero period hPeriod input natural parameter)
    (longitudinalBlock_zero period hPeriod input natural parameter)
    (boundaryBlock_zero period hPeriod input natural parameter)]
  rw [← actualOperator_componentwise period hPeriod input natural parameter state]
  rw [← decomposition_sectorProjector_eq_raw period hPeriod input]

/-- Public family-wide sector commutation checkpoint. -/
theorem global_hessian_preferred_five_sector_natural_family_commutation_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input) :
    ∀ parameter sector state,
      input.familyIndex.baseFamily.actualOperator parameter
          (preferredSectorProjectorApply period hPeriod input sector state) =
        preferredSectorProjectorApply period hPeriod input sector
          (input.familyIndex.baseFamily.actualOperator parameter state) :=
  actualOperator_commutes_sectorProjector period hPeriod input natural

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalFamilyCommutation4D
end JanusFormal
