import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPProductThroatLongTimeD11NamedKernelTerminalAdapter4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11NaturalEllipticSectorOperatorFamilyAdapter4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11BasepointSectorNormUnitaryFrameAdapter4D

/-!
# Constructed-natural basepoint-sector product-throat terminal

The canonical orthogonal resolution and five norm identities for
`reverseLinear 0 parameter` replace the stronger pairwise metric packet.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPProductThroatLongTimeD11ConstructedNaturalBasepointSectorNormTransportTerminal4D

set_option autoImplicit false
set_option maxHeartbeats 448000000
set_option synthInstance.maxHeartbeats 224000000
noncomputable section

open Filter Set Topology MeasureTheory
open scoped BigOperators Manifold ContDiff InnerProductSpace
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusSpinCImmersionCategory
open P0EFTJanusNaturalEllipticFamilyExistence
open P0EFTJanusProgramPNaturalEllipticOperatorRepresentation4D
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
open P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
open P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamily4D
open P0EFTJanusProgramPOperatorNormDifferentiableLinearTransport4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSpectralCutReferenceAtlas4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11PreNamedKernelBasepointAdapter4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11NamedKernelFamilyAdapter4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11NaturalEllipticSectorOperatorFamilyAdapter4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11BasepointSectorNormUnitaryFrameAdapter4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedProductThroatLongTimeSpectralReferenceAtlas4D
open P0EFTJanusCircleDiracHeatTraceCancellation

attribute [local instance]
  GlobalCandidateALocalVariationalChart.normedAddCommGroup
  GlobalCandidateALocalVariationalChart.normedSpace
  commonHilbertNormedAddCommGroup
  commonHilbertInnerProductSpace
  commonHilbertNormedSpace
  commonHilbertModule
  commonHilbertCompleteSpace
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelNormedAddCommGroup
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelInnerProductSpace
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelNormedSpace
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelModule
  P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D.actualKernelCompleteSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertNormedAddCommGroup
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertInnerProductSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertNormedSpace
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertModule
  P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D.candidateAHilbertCompleteSpace

variable (period : Real) (hPeriod : period ≠ 0)

universe x y z

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
    {Slice : Type x} {ShortCutoff : Type y} {LongCutoff : Type z}
    [MeasurableSpace Slice]
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

private abbrev CanonicalResolution
    (atlas : GlobalHessianPreferredFiveSectorSpectralCutReferenceAtlas4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index) :=
  globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution period hPeriod
    atlas.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.frontier

/-- Construct the named closure, natural family and operator-norm frame from
five basepoint-sector norm identities and one regular transport. -/
def globalHessianPreferredFiveSectorProductThroatLongTimeTerminal_of_constructedNaturalBasepointSectorNormTransport
    (sliceMeasure : Measure Slice) [IsProbabilityMeasure sliceMeasure]
    (shortCutoffFilter : Filter ShortCutoff) [NeBot shortCutoffFilter]
    (longCutoffFilter : Filter LongCutoff) [NeBot longCutoffFilter]
    (atlas : GlobalHessianPreferredFiveSectorSpectralCutReferenceAtlas4D
      period hPeriod configuration data analysis einsteinScale hTransverse family
        chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index)
    {immersionCategory : SpinCImmersionCategory}
    {ellipticFamily : NaturalEllipticOperatorFamily immersionCategory}
    (representation : NaturalEllipticOperatorRepresentationData
      immersionCategory ellipticFamily
        (fun parameter state => atlas.baseFamily.actualOperator parameter state))
    (refinement : FiveSectorNaturalRepresentationRefinementData representation
      (atlas.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.frontier.analytic.geometry.coordinates.coordinates))
    (pullback : FiveSectorNaturalRepresentationPullbackData representation
      (atlas.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.frontier.analytic.geometry.coordinates.coordinates)
        refinement)
    (isomorphisms : LinearNaturalRepresentationAdmissibleIsomorphismFamilyData
      representation
        (atlas.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.frontier.analytic.geometry.coordinates.coordinates)
          refinement pullback)
    (metric_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((CanonicalResolution period hPeriod atlas).projection
            .metricDiffeomorphism state)‖ =
        ‖(CanonicalResolution period hPeriod atlas).projection
          .metricDiffeomorphism state‖)
    (abelian_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((CanonicalResolution period hPeriod atlas).projection
            .abelianGauge state)‖ =
        ‖(CanonicalResolution period hPeriod atlas).projection
          .abelianGauge state‖)
    (matter_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((CanonicalResolution period hPeriod atlas).projection
            .primitiveSpinCMatter state)‖ =
        ‖(CanonicalResolution period hPeriod atlas).projection
          .primitiveSpinCMatter state‖)
    (longitudinal_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((CanonicalResolution period hPeriod atlas).projection
            .longitudinalLL state)‖ =
        ‖(CanonicalResolution period hPeriod atlas).projection
          .longitudinalLL state‖)
    (boundary_norm_map : ∀ parameter state,
      ‖isomorphisms.reverseLinear 0 parameter
          ((CanonicalResolution period hPeriod atlas).projection
            .boundaryFiniteBV state)‖ =
        ‖(CanonicalResolution period hPeriod atlas).projection
          .boundaryFiniteBV state‖)
    (regularity : OperatorNormDifferentiableLinearTransportData
      (fun parameter vector =>
        isomorphisms.transport representation
          (atlas.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.frontier.analytic.geometry.coordinates.coordinates)
            refinement pullback 0 parameter vector)) :=
  let transported_vector_differentiable := fun mode =>
    regularity.differentiable_apply
      (globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis
        (period := period) (hPeriod := hPeriod)
        (operator := atlas.baseFamily.actualOperator)
        (operator_zero := atlas.baseFamily.actual_zero)
        (baseKernelBasis :=
          atlas.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.basis)
        mode).1
  let closure :=
    globalHessianPreferredFiveSectorD11NamedKernelFamilyClosure period hPeriod
      atlas representation refinement pullback isomorphisms
        transported_vector_differentiable
  fun
    (spectral :
      GlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedProductThroatLongTimeSpectralReferenceData
        period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter closure) =>
    let natural :=
      globalHessianPreferredFiveSectorD11NaturalEllipticSectorOperatorFamily
        period hPeriod closure representation refinement pullback isomorphisms
    let frame :=
      globalHessianPreferredFiveSectorD11OperatorNormUnitaryFrame_of_basepointSectorNormTransport
        period hPeriod closure natural isomorphisms metric_norm_map
          abelian_norm_map matter_norm_map longitudinal_norm_map boundary_norm_map
            regularity
    P0EFTJanusProgramPProductThroatLongTimeD11NamedKernelTerminalAdapter4D.globalHessianPreferredFiveSectorProductThroatLongTimeTerminal_of_d11NamedKernel
      period hPeriod sliceMeasure shortCutoffFilter longCutoffFilter atlas
        representation refinement pullback isomorphisms
          transported_vector_differentiable natural frame spectral

end
end P0EFTJanusProgramPProductThroatLongTimeD11ConstructedNaturalBasepointSectorNormTransportTerminal4D
end JanusFormal
