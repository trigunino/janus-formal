import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11PreNamedKernelBasepointAdapter4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D

/-!
# Metric/operator-norm adapter for the preferred D11 unitary frame

The pairwise represented D11 isomorphisms already determine the basepoint
linear frame.  Metric compatibility upgrades it to a unitary frame, and one
operator-norm derivative supplies the final global frame packet.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrameAdapter4D

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
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorRepresentation4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11PreNamedKernelBasepointAdapter4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
open P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamily4D
open P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamilyMetric4D
open P0EFTJanusProgramPOperatorNormDifferentiableLinearTransport4D
open P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrame4D
open P0EFTJanusProgramPUnitaryNaturalRepresentationAdmissibleIsomorphismFrame4D
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

/-- The canonical basepoint unitary frame generated by pairwise D11
isomorphisms and their metric compatibility. -/
def metricUnitaryFrame
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
    (metric : LinearNaturalRepresentationAdmissibleIsomorphismFamilyMetricData
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback isomorphisms) :
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
    (globalHessianPreferredFiveSectorD11PreNamedLinearFrame_reverse_norm_map
      period hPeriod (Frontier period hPeriod input)
      natural.covariance.sectorRepresentation.bridge.representation
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback isomorphisms metric)

/-- Metric compatibility and one operator-norm derivative close the preferred
D11 unitary-frame packet. -/
def globalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame_of_metric
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
    (metric : LinearNaturalRepresentationAdmissibleIsomorphismFamilyMetricData
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback isomorphisms)
    (operatorRegularity : OperatorNormDifferentiableUnitaryFrameData
      ((metricUnitaryFrame period hPeriod input natural isomorphisms metric).frame
        natural.covariance.sectorRepresentation.bridge.representation
        (Coordinates period hPeriod input)
        natural.covariance.sectorRepresentation.sectorRefinement
        natural.covariance.pullback)) :
    GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural where
  unitaryFrame := metricUnitaryFrame period hPeriod input natural isomorphisms
    metric
  operatorRegularity := operatorRegularity

/-- A differentiable continuous-linear representative transfers to any
pointwise equal unitary frame. -/
def operatorNormUnitaryFrameData_of_linearTransportAgreement
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace Real E]
    {transport : Real → E → E}
    (frame : Real → E ≃ₗᵢ[Real] E)
    (regularity : OperatorNormDifferentiableLinearTransportData transport)
    (agreement : ∀ parameter vector,
      frame parameter vector = transport parameter vector) :
    OperatorNormDifferentiableUnitaryFrameData frame where
  derivative := regularity.derivative
  hasDerivAt_frame := by
    intro parameter
    have operator_eq : unitaryFrameOperator frame = regularity.operator := by
      funext current
      ext vector
      exact (agreement current vector).trans
        (regularity.operator_apply current vector).symm
    rw [operator_eq]
    exact regularity.hasDerivAt_operator parameter

/-- Linear-transport form of the adapter.  The same operator-norm packet can
also discharge every transported-vector differentiability premise upstream. -/
def globalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame_of_metricTransport
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
    (metric : LinearNaturalRepresentationAdmissibleIsomorphismFamilyMetricData
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback isomorphisms)
    (regularity : OperatorNormDifferentiableLinearTransportData
      (fun parameter vector =>
        isomorphisms.transport
          natural.covariance.sectorRepresentation.bridge.representation
          (Coordinates period hPeriod input)
          natural.covariance.sectorRepresentation.sectorRefinement
          natural.covariance.pullback 0 parameter vector)) :
    GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural :=
  globalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame_of_metric
    period hPeriod input natural isomorphisms metric
      (operatorNormUnitaryFrameData_of_linearTransportAgreement
        ((metricUnitaryFrame period hPeriod input natural isomorphisms metric).frame
          natural.covariance.sectorRepresentation.bridge.representation
          (Coordinates period hPeriod input)
          natural.covariance.sectorRepresentation.sectorRefinement
          natural.covariance.pullback)
        regularity (fun _ _ => rfl))

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrameAdapter4D
end JanusFormal
