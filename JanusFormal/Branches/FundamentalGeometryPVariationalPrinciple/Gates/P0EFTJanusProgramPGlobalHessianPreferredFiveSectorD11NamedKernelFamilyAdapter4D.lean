import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11PreNamedKernelBasepointAdapter4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D

/-!
# D11 construction of the preferred named-kernel family

The pre-named D11 transport starts from the exact H14 basepoint basis stored in
the spectral-cut atlas.  Identity transport at parameter zero supplies the
required basepoint agreement.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11NamedKernelFamilyAdapter4D

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
open P0EFTJanusProgramPLinearNaturalRepresentationAdmissibleIsomorphismFamily4D
open P0EFTJanusProgramPDenseCoreChartBilinearBound4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramBridge4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramGlobalBridge4D
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameKernelGramGlobalBridge4D.FiveSectorL2AdmissibleFrameKernelGramData
open P0EFTJanusProgramPFiveSectorL2AdmissibleFrameTrueKernelBasisGlobalBridge4D
open P0EFTJanusProgramPFiniteIntertwiningOperatorKernelTransport4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorL2AdmissibleIsomorphismFamilyKernelGramFrontend4D
open P0EFTJanusProgramPGlobalCandidateAFiveSectorL2AdmissibleIsomorphismFamilyTrueKernelFrontend4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorCanonicalOperatorFrontier4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11TrueKernelGramFrontend4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11PreNamedKernelBasepointAdapter4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorBismutFreedFamily4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorSpectralCutReferenceAtlas4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D
open P0EFTJanusProgramPGlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
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

/-- A modewise differentiable D11 transport of the exact H14 basis constructs the named
kernel family used by the determinant and zeta layers. -/
def globalHessianPreferredFiveSectorD11NamedKernelFamilyClosure
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
    (transported_vector_differentiable : ∀ mode,
      Differentiable Real
        (fun parameter : Real =>
          isomorphisms.transport representation
            (atlas.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.frontier.analytic.geometry.coordinates.coordinates)
              refinement pullback 0
                parameter
                  (globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis
                    (period := period) (hPeriod := hPeriod)
                    (operator := atlas.baseFamily.actualOperator)
                    (operator_zero := atlas.baseFamily.actual_zero)
                    (baseKernelBasis :=
                      atlas.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.basis)
                    mode).1)) :
    GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period hPeriod
      configuration data analysis einsteinScale hTransverse family chartBound
        Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index := by
  let frontier :=
    atlas.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.frontier
  let d11Input :=
    globalHessianPreferredFiveSectorD11BasepointInput_of_preNamedFrontier
      period hPeriod frontier atlas.baseFamily.actual_zero
        atlas.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.basis
          representation refinement pullback isomorphisms
            transported_vector_differentiable
  let gramData :=
    globalCandidateAFiveSectorIsomorphismFamilyKernelGramData period hPeriod
      configuration data analysis frontier.analytic.geometry.coordinates
        (globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution period
          hPeriod frontier)
        (globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution_decomposition
          period hPeriod frontier)
        representation refinement pullback isomorphisms d11Input.baseKernelBasis
  let kernels :=
    globalHessianPreferredFiveSectorD11FiniteKernelBasisFamilyData period hPeriod
      frontier.analytic.geometry.coordinates
        (globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution period
          hPeriod frontier)
        (globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution_decomposition
          period hPeriod frontier)
        representation refinement pullback isomorphisms d11Input
  refine
    { familyIndex := atlas
      kernels := kernels
      basis_zero_agreement := ?_ }
  intro mode
  change
    ((d11Input.baseKernelBasis.map
      (gramData.kernelTransport representation
        frontier.analytic.geometry.coordinates.coordinates refinement pullback 0))
          mode).1 =
      (atlas.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.basis
        mode).1
  rw [Module.Basis.map_apply]
  have hTransport :
      gramData.kernelTransport representation
          frontier.analytic.geometry.coordinates.coordinates refinement pullback 0 =
        LinearEquiv.refl Real _ := by
    unfold FiveSectorL2AdmissibleFrameKernelGramData.kernelTransport
    exact
      FiniteIntertwiningOperatorTransportData.kernelTransport_self
        (gramData.operatorTransport representation
          frontier.analytic.geometry.coordinates.coordinates refinement pullback) 0
  rw [hTransport]
  change (d11Input.baseKernelBasis mode).1 = _
  dsimp [d11Input,
    globalHessianPreferredFiveSectorD11BasepointInput_of_preNamedFrontier]
  unfold globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis
  exact kernelBasisOfOperatorEq_apply_val atlas.baseFamily.actual_zero
    atlas.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.basis mode

/-- A named-kernel closure together with its differentiability upgrade. -/
structure GlobalHessianPreferredFiveSectorD11NamedKernelFamilyData4D where
  closure : GlobalHessianPreferredFiveSectorNamedKernelFamilyClosure4D period
    hPeriod configuration data analysis einsteinScale hTransverse family
      chartBound Metric Abelian Matter Longitudinal Boundary ZeroMode fold Index
  regularity : GlobalHessianPreferredFiveSectorDifferentiableNamedKernelFamily4D
    period hPeriod closure

/-- The same modewise differentiability premise constructs both the named closure and its
preferred differentiable API without an additional regularity hypothesis. -/
def globalHessianPreferredFiveSectorD11NamedKernelFamilyData
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
    (transported_vector_differentiable : ∀ mode,
      Differentiable Real
        (fun parameter : Real =>
          isomorphisms.transport representation
            (atlas.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.frontier.analytic.geometry.coordinates.coordinates)
              refinement pullback 0 parameter
                (globalHessianPreferredFiveSectorD11PreNamedBaseKernelBasis
                  (period := period) (hPeriod := hPeriod)
                  (operator := atlas.baseFamily.actualOperator)
                  (operator_zero := atlas.baseFamily.actual_zero)
                  (baseKernelBasis :=
                    atlas.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.basis)
                  mode).1)) :
    GlobalHessianPreferredFiveSectorD11NamedKernelFamilyData4D
      (configuration := configuration) (data := data) (analysis := analysis)
      (einsteinScale := einsteinScale) (hTransverse := hTransverse)
      (family := family) (chartBound := chartBound)
      (Metric := Metric) (Abelian := Abelian) (Matter := Matter)
      (Longitudinal := Longitudinal) (Boundary := Boundary)
      (ZeroMode := ZeroMode) (fold := fold) (Index := Index)
      period hPeriod := by
  let closure :=
    globalHessianPreferredFiveSectorD11NamedKernelFamilyClosure period hPeriod
      atlas representation refinement pullback isomorphisms
        transported_vector_differentiable
  let frontier :=
    atlas.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.frontier
  let d11Input :=
    globalHessianPreferredFiveSectorD11BasepointInput_of_preNamedFrontier
      period hPeriod frontier atlas.baseFamily.actual_zero
        atlas.baseFamily.quillen.intrinsicFamily.basepoint.intrinsic.closure.basis
          representation refinement pullback isomorphisms
            transported_vector_differentiable
  let differentiableKernels :=
    globalHessianPreferredFiveSectorD11DifferentiableKernelBasisFamilyData period
      hPeriod frontier.analytic.geometry.coordinates
        (globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution period
          hPeriod frontier)
        (globalHessianPreferredFiveSectorD11PreNamedOrthogonalResolution_decomposition
          period hPeriod frontier)
        representation refinement pullback isomorphisms d11Input
  refine { closure := closure, regularity := { vector_differentiable := ?_ } }
  intro mode
  change Differentiable Real
    (fun parameter : Real => differentiableKernels.kernels.vector parameter mode)
  exact differentiableKernels.vector_differentiable mode

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorD11NamedKernelFamilyAdapter4D
end JanusFormal
