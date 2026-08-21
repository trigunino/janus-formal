import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11NamedKernelFamilyAdapter4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPFiveSectorL2AdmissibleFrameTrueKernelBasisGlobalBridge4D

/-!
# Named D11 kernel family from a basepoint frame

The generic frame bridge generates coherent pairwise kernel transports from a
single represented frame `0 → parameter`.  Thus the named closure does not
need a pairwise admissible-isomorphism family.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11BasepointFrameNamedKernelFamilyAdapter4D

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 500000
noncomputable section

open Set Topology MeasureTheory
open scoped Manifold ContDiff InnerProductSpace
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
open P0EFTJanusProgramPGlobalCandidateAFiveSectorCompletionCoordinates4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationRefinement4D
open P0EFTJanusProgramPFiveSectorNaturalRepresentationPullback4D
open P0EFTJanusProgramPFiveSectorOrthogonalProductResolution4D
open P0EFTJanusProgramPFiveSectorL2OrthogonalProductCoordinatesBridge4D
open P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFrame4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramBridge4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramGlobalBridge4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramGlobalBridge4D.FiveSectorL2AdmissibleFrameKernelGramData
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameTrueKernelBasisGlobalBridge4D
open P0EFTJanusProgramPFiniteIntertwiningOperatorKernelTransport4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11PreNamedKernelBasepointAdapter4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSpectralCutReferenceAtlas4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
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

universe w

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

private theorem kernelBasisOfOperatorEq_apply_val
    {E Mode : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    {first second : E →L[Real] E}
    (operator_eq : first = second)
    (basis : Module.Basis Mode Real second.ker) (mode : Mode) :
    ((by
        rw [operator_eq]
        exact basis : Module.Basis Mode Real first.ker) mode).1 =
      (basis mode).1 := by
  cases operator_eq
  rfl

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
    {fold : Fold} {Index : Type w}

/-- The exact H14 base basis transported by a represented basepoint frame. -/
def globalHessianPreferredFiveSectorD11NamedKernelFamilyClosure_of_basepointFrame
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
    (frameData : LinearNaturalRepresentationAdmissibleIsomorphismFrameData
      representation
        (atlas.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.frontier.analytic.geometry.coordinates.coordinates)
          refinement pullback) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index := by
  let frontier :=
    atlas.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.frontier
  let coordinates := frontier.analytic.geometry.coordinates.coordinates
  let resolution :=
    globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution period hPeriod
      frontier
  let baseBasis :=
    globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis
      (period := period) (hPeriod := hPeriod)
      (operator := atlas.baseFamily.actualOperator)
      (operator_zero := atlas.baseFamily.actual_zero)
      (baseKernelBasis :=
        atlas.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.basis)
  let gramData : FiveSectorL2AdmissibleFrameKernelGramData
      representation coordinates refinement pullback :=
    { l2Coordinates := fiveSectorL2HilbertCoordinatesOfOrthogonalProduct resolution
      projector_eq := fun sector =>
        fiveSectorLegacyProjector_eq_l2OfOrthogonalProduct coordinates resolution
          (globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution_decomposition
            period hPeriod frontier) sector
      frameData := frameData
      baseKernelBasis := baseBasis }
  let kernels :=
    FiveSectorL2AdmissibleFrameKernelGramData.toFiniteKernelBasisFamilyData
      representation coordinates refinement pullback gramData
  refine
    { familyIndex := atlas
      kernels := kernels
      basis_zero_agreement := ?_ }
  intro mode
  change
    ((baseBasis.map
      (gramData.kernelTransport representation coordinates refinement pullback 0))
        mode).1 =
      (atlas.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.basis
        mode).1
  rw [Module.Basis.map_apply]
  have hTransport :
      gramData.kernelTransport representation coordinates refinement pullback 0 =
        LinearEquiv.refl Real _ := by
    unfold FiveSectorL2AdmissibleFrameKernelGramData.kernelTransport
    exact
      FiniteIntertwiningOperatorTransportData.kernelTransport_self
        (gramData.operatorTransport representation coordinates refinement pullback) 0
  rw [hTransport]
  change (baseBasis mode).1 = _
  dsimp [baseBasis]
  unfold globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis
  exact kernelBasisOfOperatorEq_apply_val atlas.baseFamily.actual_zero
    atlas.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.basis mode

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11BasepointFrameNamedKernelFamilyAdapter4D
end JanusFormal
