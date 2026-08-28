import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrameCommutation4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D

/-!
# Five-sector preservation of the operator-norm D11 connection

The represented D11 unitary frame already commutes with every projector from
the single preferred five-sector Candidate-A Hilbert decomposition.  Since the
frame is differentiable in operator norm, differentiation preserves these
commutation equations.

Consequently

```text
F'_a P_s = P_s F'_a,
(F_a⁻¹ F'_a) P_s = P_s (F_a⁻¹ F'_a),
(F'_a F_a⁻¹) P_s = P_s (F'_a F_a⁻¹)
```

for all five physical sectors.  Together with skew-adjointness, this identifies
the D11 frame connection as a five-block diagonal metric connection on the one
preferred Candidate-A Hilbert completion.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormSectorConnection4D

set_option autoImplicit false
set_option maxHeartbeats 170000000
set_option synthInstance.maxHeartbeats 85000000
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
open P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrame4D
open P0EFTJanusProgramPOperatorNormDifferentiableUnitaryFrameCommutation4D
open P0EFTJanusProgramPUnitaryNaturalRepresentationAdmissibleIsomorphismFrame4D
open P0EFTJanusProgramPFiveSectorHilbertCoordinates4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
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
    BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

private abbrev CandidateAHilbert
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :=
  GlobalCandidateAFaithfulSameActionHilbert period hPeriod configuration data
    analysis

local instance (priority := 30000) candidateAHilbertNormedAddCommGroup
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedAddCommGroup
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedAddCommGroup
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAHilbertInnerProductSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    InnerProductSpace Real
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkInnerProductSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAHilbertNormedSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    NormedSpace Real
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkNormedSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAHilbertModule
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    Module Real
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkModule
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

local instance (priority := 30000) candidateAHilbertCompleteSpace
    {couplings : GlobalCandidateAActionCouplings}
    {NonNullFace NullFace : Type*}
    [Fintype NonNullFace] [Fintype NullFace]
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (data : GlobalCandidateAActionData period hPeriod configuration.physical
      couplings NonNullFace NullFace)
    (analysis : GlobalAnalysisData period hPeriod configuration.physical) :
    CompleteSpace
      (CandidateAHilbert period hPeriod configuration data analysis) :=
  P0EFTJanusProgramPGlobalCandidateADiagonalExtendedBulkL2Riesz4D.diagonalL2ExtendedBulkCompleteSpace
    period hPeriod (globalCandidateAMetricBySector period hPeriod data)
      couplings.matterMassSquared data analysis

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

private abbrev Coordinates
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :=
  preferredCandidateAFiveSectorHilbertCoordinates period hPeriod input

private def d11Frame
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural) :=
  frame.unitaryFrame.frame
    natural.covariance.sectorRepresentation.bridge.representation
    (Coordinates period hPeriod input)
    natural.covariance.sectorRepresentation.sectorRefinement
    natural.covariance.pullback

/-- The represented D11 frame commutes with one selected physical projector. -/
def sectorFrameCommutation
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (sector : FivePhysicalSector) :
    FrameCommutesWithFixedOperatorData
      (d11Frame period hPeriod input natural frame)
      ((Coordinates period hPeriod input).sectorProjector sector) where
  commute := by
    intro parameter
    ext state
    exact frame.unitaryFrame.frame_commutes_sectorProjector
      natural.covariance.sectorRepresentation.bridge.representation
      (Coordinates period hPeriod input)
      natural.covariance.sectorRepresentation.sectorRefinement
      natural.covariance.pullback parameter sector state

/-- The frame derivative is block-diagonal in the five physical sectors. -/
theorem frameDerivative_commutes_sectorProjector
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (parameter : Real) (sector : FivePhysicalSector) :
    (frame.operatorRegularity.derivative parameter).comp
        ((Coordinates period hPeriod input).sectorProjector sector) =
      ((Coordinates period hPeriod input).sectorProjector sector).comp
        (frame.operatorRegularity.derivative parameter) :=
  frame.operatorRegularity.derivative_commutes_fixedOperator
    ((Coordinates period hPeriod input).sectorProjector sector)
    (sectorFrameCommutation period hPeriod input natural frame sector) parameter

/-- The fixed-coordinate D11 connection preserves every physical sector. -/
theorem leftConnection_commutes_sectorProjector
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (parameter : Real) (sector : FivePhysicalSector) :
    (frame.operatorRegularity.leftLogDerivative parameter).comp
        ((Coordinates period hPeriod input).sectorProjector sector) =
      ((Coordinates period hPeriod input).sectorProjector sector).comp
        (frame.operatorRegularity.leftLogDerivative parameter) :=
  frame.operatorRegularity.leftLogDerivative_commutes_fixedOperator
    ((Coordinates period hPeriod input).sectorProjector sector)
    (sectorFrameCommutation period hPeriod input natural frame sector) parameter

/-- The moving-coordinate D11 connection also preserves every physical sector. -/
theorem rightConnection_commutes_sectorProjector
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural)
    (parameter : Real) (sector : FivePhysicalSector) :
    (frame.operatorRegularity.rightLogDerivative parameter).comp
        ((Coordinates period hPeriod input).sectorProjector sector) =
      ((Coordinates period hPeriod input).sectorProjector sector).comp
        (frame.operatorRegularity.rightLogDerivative parameter) :=
  frame.operatorRegularity.rightLogDerivative_commutes_fixedOperator
    ((Coordinates period hPeriod input).sectorProjector sector)
    (sectorFrameCommutation period hPeriod input natural frame sector) parameter

/-- Public five-sector D11 connection checkpoint. -/
theorem global_hessian_preferred_five_sector_D11_operator_norm_sector_connection_gate
    (input : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    (natural : GlobalHessianPreferredFiveSectorNaturalEllipticSectorOperatorFamily4D
      period hPeriod input)
    (frame : GlobalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame4D
      period hPeriod input natural) :
    (∀ parameter sector,
      (frame.operatorRegularity.derivative parameter).comp
          ((Coordinates period hPeriod input).sectorProjector sector) =
        ((Coordinates period hPeriod input).sectorProjector sector).comp
          (frame.operatorRegularity.derivative parameter)) ∧
    (∀ parameter sector,
      (frame.operatorRegularity.leftLogDerivative parameter).comp
          ((Coordinates period hPeriod input).sectorProjector sector) =
        ((Coordinates period hPeriod input).sectorProjector sector).comp
          (frame.operatorRegularity.leftLogDerivative parameter)) ∧
    (∀ parameter sector,
      (frame.operatorRegularity.rightLogDerivative parameter).comp
          ((Coordinates period hPeriod input).sectorProjector sector) =
        ((Coordinates period hPeriod input).sectorProjector sector).comp
          (frame.operatorRegularity.rightLogDerivative parameter)) ∧
    (∀ parameter,
      IsRealSkewAdjointOperator
        (frame.operatorRegularity.leftLogDerivative parameter)) ∧
    (∀ parameter,
      IsRealSkewAdjointOperator
        (frame.operatorRegularity.rightLogDerivative parameter)) :=
  ⟨frameDerivative_commutes_sectorProjector period hPeriod input natural frame,
    leftConnection_commutes_sectorProjector period hPeriod input natural frame,
    rightConnection_commutes_sectorProjector period hPeriod input natural frame,
    frame.operatorRegularity.leftLogDerivative_skew,
    frame.operatorRegularity.rightLogDerivative_skew⟩

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11OperatorNormSectorConnection4D
end JanusFormal
