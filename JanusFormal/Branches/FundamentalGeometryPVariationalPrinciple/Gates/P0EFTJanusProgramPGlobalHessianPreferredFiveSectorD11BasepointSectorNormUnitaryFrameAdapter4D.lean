import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrameAdapter4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismBasepointSectorNorm4D

/-!
# Basepoint-sector norm adapter for the preferred D11 unitary frame

Only the five sectorwise norm identities for `reverseLinear 0 parameter` are
needed to make the canonical D11 frame unitary.  This avoids constructing the
stronger pairwise metric packet.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11BasepointSectorNormUnitaryFrameAdapter4D

set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option synthInstance.maxHeartbeats 8000000
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
open P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionCoordinates4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11PreNamedKernelBasepointAdapter4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrameAdapter4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
open P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D
open P0EFTJanusProgramPFiveSectorOrthogonalProductPythagoras4D
open P0EFTJanusProgramPFiveSectorL2NaturalRepresentationPullbackBridge4D
open P0EFTJanusProgramPFiveSectorL2OrthogonalProductCoordinatesBridge4D
open P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamily4D
open P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismBasepointSectorNorm4D
open P0EFTJanusProgramPOperatorNormDifferentiableLinearTransport4D
open P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrame4D
open P0EFTJanusProgramPUnitaryNaturalRepresentationAdmissibleIsomorphismFrame4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusCircleDiracHeatTraceCancellation

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  commonHilbertNormedAddCommGroup
  commonHilbertInnerProductSpace
  commonHilbertNormedSpace
  commonHilbertModule
  commonHilbertCompleteSpace
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
    BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

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

private abbrev Frontier
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index) :=
  input.familyIndex.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.frontier

private abbrev Coordinates
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index) :=
  preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input

private abbrev Resolution
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold
          Index) :=
  globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution period hPeriod
    (Frontier period hPeriod input)

/-- The five basepoint-sector norm identities imply norm preservation for the
whole canonical D11 linear frame. -/
theorem preNamedLinearFrame_reverse_norm_map_of_basepointSectorNorms
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (isomorphisms : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback)
    (metric_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((Resolution period hPeriod input).projection
            .metricDiffeomorphism state)‖ =
        ‖(Resolution period hPeriod input).projection
          .metricDiffeomorphism state‖)
    (abelian_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((Resolution period hPeriod input).projection .abelianGauge state)‖ =
        ‖(Resolution period hPeriod input).projection .abelianGauge state‖)
    (matter_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((Resolution period hPeriod input).projection
            .primitiveSpinCMatter state)‖ =
        ‖(Resolution period hPeriod input).projection
          .primitiveSpinCMatter state‖)
    (longitudinal_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((Resolution period hPeriod input).projection .longitudinalLL state)‖ =
        ‖(Resolution period hPeriod input).projection .longitudinalLL state‖)
    (boundary_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((Resolution period hPeriod input).projection .boundaryFiniteBV state)‖ =
        ‖(Resolution period hPeriod input).projection .boundaryFiniteBV state‖)
    (parameter : Real) (state) :
    ‖(globalHessianPreferredFiveSectorD11PreNamedLinearFrame period hPeriod
      (Frontier period hPeriod input)
      natural.covariance.sectorRepresentation.bridge.representation
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback isomorphisms).reverseLinear parameter state‖ =
      ‖state‖ := by
  let coordinates := Coordinates period hPeriod input
  let resolution := Resolution period hPeriod input
  let reverse_projection_norm_map : ∀ current sector state,
      ‖isomorphisms.reverseLinear 0 current
          (resolution.projection sector state)‖ =
        ‖resolution.projection sector state‖ := by
    intro current sector state
    cases sector with
    | metricDiffeomorphism => exact metric_norm_map current state
    | abelianGauge => exact abelian_norm_map current state
    | primitiveSpinCMatter => exact matter_norm_map current state
    | longitudinalLL => exact longitudinal_norm_map current state
    | boundaryFiniteBV => exact boundary_norm_map current state
  let sectorNorm :=
    LinearNaturalRepresentationAdmissibleIsomorphismBasepointSectorNormData.ofOrthogonalProduct
      natural.covariance.sectorRepresentation.bridge.representation coordinates
        natural.covariance.sectorRepresentation.sectorRefinement
          natural.covariance.pullback isomorphisms resolution
            (globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution_decomposition
              period hPeriod (Frontier period hPeriod input))
            reverse_projection_norm_map
  change ‖isomorphisms.reverseLinear 0 parameter state‖ = ‖state‖
  exact sectorNorm.reverse_norm_map
    natural.covariance.sectorRepresentation.bridge.representation coordinates
      natural.covariance.sectorRepresentation.sectorRefinement
        natural.covariance.pullback isomorphisms resolution parameter state

/-- The canonical unitary frame built from only the five basepoint-sector norm
identities. -/
def basepointSectorNormUnitaryFrame
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (isomorphisms : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback)
    (metric_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((Resolution period hPeriod input).projection
            .metricDiffeomorphism state)‖ =
        ‖(Resolution period hPeriod input).projection
          .metricDiffeomorphism state‖)
    (abelian_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((Resolution period hPeriod input).projection .abelianGauge state)‖ =
        ‖(Resolution period hPeriod input).projection .abelianGauge state‖)
    (matter_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((Resolution period hPeriod input).projection
            .primitiveSpinCMatter state)‖ =
        ‖(Resolution period hPeriod input).projection
          .primitiveSpinCMatter state‖)
    (longitudinal_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((Resolution period hPeriod input).projection .longitudinalLL state)‖ =
        ‖(Resolution period hPeriod input).projection .longitudinalLL state‖)
    (boundary_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((Resolution period hPeriod input).projection .boundaryFiniteBV state)‖ =
        ‖(Resolution period hPeriod input).projection .boundaryFiniteBV state‖) :
    UnitaryNaturalRepresentationAdmissibleIsomorphismFrameData
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback :=
  globalHessianPreferredFiveSectorD11PreNamedUnitaryFrame period hPeriod
    (Frontier period hPeriod input)
    natural.covariance.sectorRepresentation.bridge.representation
    natural.covariance.sectorRepresentation.sectorRefinement
    natural.covariance.pullback isomorphisms
    (preNamedLinearFrame_reverse_norm_map_of_basepointSectorNorms period hPeriod
      input natural isomorphisms metric_norm_map abelian_norm_map matter_norm_map
        longitudinal_norm_map boundary_norm_map)

/-- Close the preferred D11 operator-norm frame directly from the five
basepoint-sector norm identities. -/
def globalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame_of_basepointSectorNorms
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (isomorphisms : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback)
    (metric_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((Resolution period hPeriod input).projection
            .metricDiffeomorphism state)‖ =
        ‖(Resolution period hPeriod input).projection
          .metricDiffeomorphism state‖)
    (abelian_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((Resolution period hPeriod input).projection .abelianGauge state)‖ =
        ‖(Resolution period hPeriod input).projection .abelianGauge state‖)
    (matter_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((Resolution period hPeriod input).projection
            .primitiveSpinCMatter state)‖ =
        ‖(Resolution period hPeriod input).projection
          .primitiveSpinCMatter state‖)
    (longitudinal_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((Resolution period hPeriod input).projection .longitudinalLL state)‖ =
        ‖(Resolution period hPeriod input).projection .longitudinalLL state‖)
    (boundary_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((Resolution period hPeriod input).projection .boundaryFiniteBV state)‖ =
        ‖(Resolution period hPeriod input).projection .boundaryFiniteBV state‖)
    (operatorRegularity : OperatorNormDifferentiableUnitaryFrameData
      ((basepointSectorNormUnitaryFrame period hPeriod input natural isomorphisms
        metric_norm_map abelian_norm_map matter_norm_map longitudinal_norm_map
          boundary_norm_map).frame
        natural.covariance.sectorRepresentation.bridge.representation
        (Coordinates period hPeriod input)
        natural.covariance.sectorRepresentation.sectorRefinement
        natural.covariance.pullback)) :
    GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural where
  unitaryFrame := basepointSectorNormUnitaryFrame period hPeriod input natural
    isomorphisms metric_norm_map abelian_norm_map matter_norm_map
      longitudinal_norm_map boundary_norm_map
  operatorRegularity := operatorRegularity

/-- Linear-transport regularity supplies the operator derivative for the
basepoint-sector unitary frame. -/
def globalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame_of_basepointSectorNormTransport
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (isomorphisms : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback)
    (metric_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((Resolution period hPeriod input).projection
            .metricDiffeomorphism state)‖ =
        ‖(Resolution period hPeriod input).projection
          .metricDiffeomorphism state‖)
    (abelian_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((Resolution period hPeriod input).projection .abelianGauge state)‖ =
        ‖(Resolution period hPeriod input).projection .abelianGauge state‖)
    (matter_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((Resolution period hPeriod input).projection
            .primitiveSpinCMatter state)‖ =
        ‖(Resolution period hPeriod input).projection
          .primitiveSpinCMatter state‖)
    (longitudinal_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((Resolution period hPeriod input).projection .longitudinalLL state)‖ =
        ‖(Resolution period hPeriod input).projection .longitudinalLL state‖)
    (boundary_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((Resolution period hPeriod input).projection .boundaryFiniteBV state)‖ =
        ‖(Resolution period hPeriod input).projection .boundaryFiniteBV state‖)
    (regularity : OperatorNormDifferentiableLinearTransportData
      (fun parameter vector =>
        isomorphisms.transport
          natural.covariance.sectorRepresentation.bridge.representation
          (Coordinates period hPeriod input)
          natural.covariance.sectorRepresentation.sectorRefinement
          natural.covariance.pullback 0 parameter vector)) :
    GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural :=
  globalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame_of_basepointSectorNorms
    period hPeriod input natural isomorphisms metric_norm_map abelian_norm_map
      matter_norm_map longitudinal_norm_map boundary_norm_map
      (operatorNormUnitaryFrameData_of_linearTransportAgreement
        ((basepointSectorNormUnitaryFrame period hPeriod input natural
          isomorphisms metric_norm_map abelian_norm_map matter_norm_map
            longitudinal_norm_map boundary_norm_map).frame
          natural.covariance.sectorRepresentation.bridge.representation
          (Coordinates period hPeriod input)
          natural.covariance.sectorRepresentation.sectorRefinement
          natural.covariance.pullback)
        regularity (fun _ _ => rfl))

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11BasepointSectorNormUnitaryFrameAdapter4D
end JanusFormal
