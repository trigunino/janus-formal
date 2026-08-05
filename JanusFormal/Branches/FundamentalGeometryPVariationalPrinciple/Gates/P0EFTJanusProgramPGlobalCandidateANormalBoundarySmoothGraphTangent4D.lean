import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundaryHistoricalGaussPairing4D

/-!
# Smooth graph-tangent bridge for the mobile Candidate-A boundary

This file promotes the smooth-core regularity of the completed latitude and
regular-frame graph-tangent coefficients.  It reuses the installed normal C²
jet, canonical `arctan` collar, and finite smooth throat frame; it introduces
no new boundary field or physical hypothesis.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option synthInstance.maxHeartbeats 600000
set_option maxRecDepth 10000
noncomputable section

open scoped ContDiff Manifold Matrix.Norms.Frobenius Topology
open Bundle

open P0EFTJanusMappingTorusCutThroatBoundaryDoubleCover4D
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixProduct4D
open P0EFTJanusMappingTorusCanonicalPhysicalC2FiniteMatrixInverse4D
open P0EFTJanusMappingTorusCanonicalNormalLiftContinuityReduction4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2Chart4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPRegularFrameMetricInverse4D
open P0EFTJanusProgramPRegularFrameMaxwellCurvatureBridge4D
open P0EFTJanusProgramPRegularFrameMaxwellPairingBridge4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusIntrinsicMetricBVThroatBracket4D
open P0EFTJanusMappingTorusIntrinsicMetricThroatNondegenerate4D
open P0EFTJanusMappingTorusIntrinsicCoverLorentzTensor4D
open P0EFTJanusMappingTorusIntrinsicLorentzMetricDescent4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusProgramPThroatFiniteFrameReconstruction4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarGraph4D
open P0EFTJanusProgramPGlobalNormalDisplacementCollarJointSmooth4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D

variable (period : Real) (hPeriod : period ≠ 0)

local instance smoothGraphTangentCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance smoothGraphTangentCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000) smoothGraphTangentOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000) smoothGraphTangentOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

local instance (priority := 30000) smoothGraphTangentEffectiveQuotientChartedSpace :
    ChartedSpace CoverModel
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D.effectiveQuotientChartedSpace
    period hPeriod

local instance (priority := 30000) smoothGraphTangentEffectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (MappingTorus (reflectedSphereData period hPeriod)) :=
  reflectedSphereQuotient_isManifold period hPeriod

set_option backward.isDefEq.respectTransparency false in
/-- On the smooth core, the stored first latitude jet is the directional
manifold derivative of the canonical `arctan` graph latitude. -/
theorem candidateANormalBoundaryLatitudeSpatialFirst_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod) :
    candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation
        period hPeriod metric index
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      mvfderiv throatCoverModelWithCorners
        (fun point : CutThroatBoundary period hPeriod =>
          Real.arctan (parameter *
            normalDisplacementOrientationScalar period hPeriod displacement
              point)) boundary
        ((finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
            boundary index) := by
  have hLatitude := normalGraphLatitude_mvfderiv_frame period hPeriod
    displacement parameter boundary index
  unfold candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation
  change
    (parameter * normalBoundaryC2JetCoreFirstAt period hPeriod boundary
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement) index) *
      candidateANormalBoundaryRawArctanDerivativeFiberEvaluation
        period hPeriod metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary = _
  rw [candidateANormalBoundaryRawArctanDerivativeFiberEvaluation_apply]
  rw [show candidateANormalBoundaryRawGraphFiberEvaluation period hPeriod
        metric
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      parameter * normalBoundaryC2JetCoreValueAt period hPeriod boundary
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement) by rfl]
  rw [hLatitude]
  ring

set_option backward.isDefEq.respectTransparency false in
/-- Smooth-core boundary regularity of each completed graph-tangent
regular-frame coefficient. -/
theorem candidateANormalBoundaryGraphTangentRegularFrameCoefficient_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real)
    (inner : NormalBoundaryTangentIndex period hPeriod) (row : Fin 4) :
    ContMDiff throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (fun point : CutThroatBoundary period hPeriod =>
        candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric inner row
          (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
            (tensor, displacement), parameter) point) := by
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let latitude : CutThroatBoundary period hPeriod → Real := fun point =>
    Real.arctan (parameter *
      normalDisplacementOrientationScalar period hPeriod displacement point)
  let slope : CutThroatBoundary period hPeriod → Real := fun point =>
    candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation
      period hPeriod metric inner current point
  let horizontal : CutThroatBoundary period hPeriod × Real → Real :=
    normalBoundaryLatitudeHorizontalRegularFrameCoefficient
      period hPeriod metric inner row
  let vertical : CutThroatBoundary period hPeriod × Real → Real :=
    normalBoundaryLatitudeVerticalRegularFrameCoefficient
      period hPeriod metric row
  let horizontalGraph : CutThroatBoundary period hPeriod → Real := fun point =>
    horizontal (point, latitude point)
  let verticalGraph : CutThroatBoundary period hPeriod → Real := fun point =>
    vertical (point, latitude point)
  let graphCoefficient : CutThroatBoundary period hPeriod → Real :=
    horizontalGraph + slope * verticalGraph
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  have hLatitudeSmooth : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ latitude := by
    exact Real.contDiff_arctan.contMDiff.comp
      (contMDiff_const.mul
        (normalDisplacementOrientationScalar_contMDiff
          period hPeriod displacement))
  have hHorizontalGraphSmooth : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ horizontalGraph :=
    (normalBoundaryLatitudeHorizontalRegularFrameCoefficient_contMDiff
      period hPeriod metric inner row).comp
        (contMDiff_id.prodMk hLatitudeSmooth)
  have hVerticalGraphSmooth : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ verticalGraph :=
    (normalBoundaryLatitudeVerticalRegularFrameCoefficient_contMDiff
      period hPeriod metric row).comp (contMDiff_id.prodMk hLatitudeSmooth)
  have hSlopeAt (point : CutThroatBoundary period hPeriod) :
      slope point = mvfderiv throatCoverModelWithCorners latitude point
        (frame.vectorAt point inner) :=
    candidateANormalBoundaryLatitudeSpatialFirst_smooth
      period hPeriod metric tensor displacement parameter point inner
  let latitudeField : SmoothThroatField
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) Real :=
    { toFun := latitude
      contMDiff_toFun := hLatitudeSmooth }
  have hSlopeFunction : slope =
      (normalBoundaryFrameDerivativeComponentField period hPeriod frame
        latitudeField inner).toFun := by
    funext point
    rw [hSlopeAt]
    change mvfderiv throatCoverModelWithCorners latitude point
        (frame.vectorAt point inner) =
      throatFrameDerivative
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        Real frame latitudeField point inner
    rw [throatFrameDerivative_eq_mvfderiv]
    rfl
  have hSlopeSmooth : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ slope := by
    rw [hSlopeFunction]
    exact (normalBoundaryFrameDerivativeComponentField period hPeriod frame
      latitudeField inner).contMDiff_toFun
  have hCoefficient :
      (fun point : CutThroatBoundary period hPeriod =>
        candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric inner row current point) = graphCoefficient := by
    funext point
    unfold graphCoefficient horizontalGraph verticalGraph
    change
      candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric inner row current point =
        horizontal (point, latitude point) +
          slope point * vertical (point, latitude point)
    rw [candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation_apply]
    change horizontal (point, Real.arctan (parameter *
          normalBoundaryC2JetCoreValueAt period hPeriod point
            (smoothNormalDisplacementToBoundaryC2JetCore
              period hPeriod displacement))) +
        (parameter * normalBoundaryC2JetCoreFirstAt period hPeriod point
          (smoothNormalDisplacementToBoundaryC2JetCore
            period hPeriod displacement) inner) *
          ((1 / (1 + (parameter *
            normalBoundaryC2JetCoreValueAt period hPeriod point
              (smoothNormalDisplacementToBoundaryC2JetCore
                period hPeriod displacement)) ^ 2)) *
            vertical (point, Real.arctan (parameter *
              normalBoundaryC2JetCoreValueAt period hPeriod point
                (smoothNormalDisplacementToBoundaryC2JetCore
                  period hPeriod displacement)))) = _
    unfold latitude slope
      candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation
    simp only [BoundedContinuousFunction.mul_apply]
    rw [candidateANormalBoundaryRawArctanDerivativeFiberEvaluation_apply]
    rw [show candidateANormalBoundaryRawGraphFiberEvaluation period hPeriod
          metric current point =
        parameter * normalBoundaryC2JetCoreValueAt period hPeriod point
          (smoothNormalDisplacementToBoundaryC2JetCore
            period hPeriod displacement) by rfl]
    rw [normalBoundaryC2ScaledRawSpatialFirst_apply,
      normalBoundaryC2JetCoreValueAt_smooth]
    have hCurrentNormal : current.1.2 =
        smoothNormalDisplacementToBoundaryC2JetCore period hPeriod
          displacement := rfl
    rw [hCurrentNormal]
    ring
  rw [hCoefficient]
  exact hHorizontalGraphSmooth.add (hSlopeSmooth.mul hVerticalGraphSmooth)

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
