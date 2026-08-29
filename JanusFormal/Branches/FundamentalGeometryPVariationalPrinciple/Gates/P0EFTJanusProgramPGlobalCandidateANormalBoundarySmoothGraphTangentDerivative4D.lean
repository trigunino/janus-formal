import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySmoothLatitudeSecond4D

/-!
# Smooth derivative of the completed graph tangent

This file identifies the completed regular-frame spatial derivative of a graph
coefficient with its manifold directional derivative.  It combines only the
installed smooth collar coefficients and the promoted first/second latitude
jets.
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

local instance smoothGraphTangentDerivativeCandidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedAddCommGroup
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedAddCommGroup
    period hPeriod metric

local instance smoothGraphTangentDerivativeCandidateANormalBoundaryFunctionalCoreNormedSpace
    (metric : RegularGeneralLorentzMetric period hPeriod) :
    NormedSpace Real
      (CandidateANormalBoundaryFunctionalCore period hPeriod metric) :=
  candidateANormalBoundaryFunctionalCoreNormedSpace period hPeriod metric

local instance (priority := 30000) smoothGraphTangentDerivativeOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000) smoothGraphTangentDerivativeOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

/-- Smooth-core evaluation of an installed smooth collar scalar. -/
theorem candidateANormalBoundarySmoothCollarFieldFiberEvaluation_smooth_apply
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (field : CutThroatBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod) :
    candidateANormalBoundarySmoothCollarFieldFiberEvaluation
        period hPeriod metric field hField
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      field (boundary, Real.arctan (parameter *
        normalDisplacementOrientationScalar period hPeriod displacement
          boundary)) := by
  rw [candidateANormalBoundarySmoothCollarFieldFiberEvaluation_apply]
  change field (boundary, Real.arctan (parameter *
      normalBoundaryC2JetCoreValueAt period hPeriod boundary
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement))) = _
  rw [normalBoundaryC2JetCoreValueAt_smooth]

set_option backward.isDefEq.respectTransparency false in
/-- The completed graph-tangent spatial derivative is exactly the manifold
directional derivative of the completed graph-tangent coefficient. -/
theorem candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivative_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (outer inner : NormalBoundaryTangentIndex period hPeriod)
    (row : Fin 4) :
    candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivativeFiberEvaluation
        period hPeriod metric outer inner row
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      mvfderiv throatCoverModelWithCorners
        (fun point : CutThroatBoundary period hPeriod =>
          candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
            period hPeriod metric inner row
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
              metric (tensor, displacement), parameter) point)
        boundary
        ((finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
            boundary outer) := by
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let latitude : CutThroatBoundary period hPeriod → Real := fun point =>
    Real.arctan (parameter *
      normalDisplacementOrientationScalar period hPeriod displacement point)
  let slope (index : NormalBoundaryTangentIndex period hPeriod) :
      CutThroatBoundary period hPeriod → Real := fun point =>
    candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation
      period hPeriod metric index current point
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
    horizontalGraph + slope inner * verticalGraph
  let vector :=
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
        boundary outer
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  have hLatitudeSmooth : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ latitude := by
    exact Real.contDiff_arctan.contMDiff.comp
      (contMDiff_const.mul
        (normalDisplacementOrientationScalar_contMDiff
          period hPeriod displacement))
  have hHorizontalSmooth : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ horizontal :=
    normalBoundaryLatitudeHorizontalRegularFrameCoefficient_contMDiff
      period hPeriod metric inner row
  have hVerticalSmooth : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ vertical :=
    normalBoundaryLatitudeVerticalRegularFrameCoefficient_contMDiff
      period hPeriod metric row
  have hHorizontalGraphSmooth : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ horizontalGraph :=
    hHorizontalSmooth.comp (contMDiff_id.prodMk hLatitudeSmooth)
  have hVerticalGraphSmooth : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ verticalGraph :=
    hVerticalSmooth.comp (contMDiff_id.prodMk hLatitudeSmooth)
  have hSlopeAt (index : NormalBoundaryTangentIndex period hPeriod)
      (point : CutThroatBoundary period hPeriod) :
      slope index point =
        mvfderiv throatCoverModelWithCorners latitude point
          (frame.vectorAt point index) := by
    exact candidateANormalBoundaryLatitudeSpatialFirst_smooth
      period hPeriod metric tensor displacement parameter point index
  let latitudeField : SmoothThroatField
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) Real :=
    { toFun := latitude
      contMDiff_toFun := hLatitudeSmooth }
  have hSlopeFunction (index : NormalBoundaryTangentIndex period hPeriod) :
      slope index =
        (normalBoundaryFrameDerivativeComponentField period hPeriod frame
          latitudeField index).toFun := by
    funext point
    rw [hSlopeAt]
    change mvfderiv throatCoverModelWithCorners latitude point
        (frame.vectorAt point index) =
      throatFrameDerivative
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        Real frame latitudeField point index
    rw [throatFrameDerivative_eq_mvfderiv]
    rfl
  have hSlopeSmooth (index : NormalBoundaryTangentIndex period hPeriod) :
      ContMDiff throatCoverModelWithCorners
        (modelWithCornersSelf Real Real) ∞ (slope index) := by
    rw [hSlopeFunction]
    exact (normalBoundaryFrameDerivativeComponentField period hPeriod frame
      latitudeField index).contMDiff_toFun
  have hHorizontalSource :
      candidateANormalBoundaryHorizontalCoefficientSourceDerivativeFiberEvaluation
          period hPeriod metric outer inner row current boundary =
        normalBoundaryHorizontalFieldDerivative period hPeriod outer horizontal
          (boundary, latitude boundary) := by
    unfold candidateANormalBoundaryHorizontalCoefficientSourceDerivativeFiberEvaluation
    rw [candidateANormalBoundarySmoothCollarFieldFiberEvaluation_smooth_apply]
  have hHorizontalLatitude :
      candidateANormalBoundaryHorizontalCoefficientLatitudeDerivativeFiberEvaluation
          period hPeriod metric inner row current boundary =
        normalBoundaryLatitudeFieldDerivative period hPeriod horizontal
          (boundary, latitude boundary) := by
    unfold candidateANormalBoundaryHorizontalCoefficientLatitudeDerivativeFiberEvaluation
    rw [candidateANormalBoundarySmoothCollarFieldFiberEvaluation_smooth_apply]
  have hVerticalSource :
      candidateANormalBoundaryVerticalCoefficientSourceDerivativeFiberEvaluation
          period hPeriod metric outer row current boundary =
        normalBoundaryHorizontalFieldDerivative period hPeriod outer vertical
          (boundary, latitude boundary) := by
    unfold candidateANormalBoundaryVerticalCoefficientSourceDerivativeFiberEvaluation
    rw [candidateANormalBoundarySmoothCollarFieldFiberEvaluation_smooth_apply]
  have hVerticalLatitude :
      candidateANormalBoundaryVerticalCoefficientLatitudeDerivativeFiberEvaluation
          period hPeriod metric row current boundary =
        normalBoundaryLatitudeFieldDerivative period hPeriod vertical
          (boundary, latitude boundary) := by
    unfold candidateANormalBoundaryVerticalCoefficientLatitudeDerivativeFiberEvaluation
    rw [candidateANormalBoundarySmoothCollarFieldFiberEvaluation_smooth_apply]
  have hHorizontalValue :
      candidateANormalBoundaryHorizontalRegularFrameCoefficientFiberEvaluation
          period hPeriod metric inner row current boundary =
        horizontalGraph boundary := by
    rw [candidateANormalBoundaryHorizontalRegularFrameCoefficientFiberEvaluation_apply]
    change horizontal
        (boundary, Real.arctan (parameter *
          normalBoundaryC2JetCoreValueAt period hPeriod boundary
            (smoothNormalDisplacementToBoundaryC2JetCore
              period hPeriod displacement))) = _
    rw [normalBoundaryC2JetCoreValueAt_smooth]
  have hVerticalValue :
      candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation
          period hPeriod metric row current boundary =
        verticalGraph boundary := by
    rw [candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation_apply]
    change vertical
        (boundary, Real.arctan (parameter *
          normalBoundaryC2JetCoreValueAt period hPeriod boundary
            (smoothNormalDisplacementToBoundaryC2JetCore
              period hPeriod displacement))) = _
    rw [normalBoundaryC2JetCoreValueAt_smooth]
  have hHorizontalChain :=
    candidateANormalBoundarySmoothCollarField_mvfderiv_graph period hPeriod
      horizontal hHorizontalSmooth latitude hLatitudeSmooth boundary outer
  change mfderiv throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) horizontalGraph boundary vector =
    normalBoundaryHorizontalFieldDerivative period hPeriod outer horizontal
        (boundary, latitude boundary) +
      mvfderiv throatCoverModelWithCorners latitude boundary vector •
        normalBoundaryLatitudeFieldDerivative period hPeriod horizontal
          (boundary, latitude boundary) at hHorizontalChain
  rw [← candidateANormalBoundary_mvfderiv_real_eq_mfderiv period hPeriod
    horizontalGraph boundary vector] at hHorizontalChain
  rw [← hSlopeAt outer boundary] at hHorizontalChain
  have hVerticalChain :=
    candidateANormalBoundarySmoothCollarField_mvfderiv_graph period hPeriod
      vertical hVerticalSmooth latitude hLatitudeSmooth boundary outer
  change mfderiv throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) verticalGraph boundary vector =
    normalBoundaryHorizontalFieldDerivative period hPeriod outer vertical
        (boundary, latitude boundary) +
      mvfderiv throatCoverModelWithCorners latitude boundary vector •
        normalBoundaryLatitudeFieldDerivative period hPeriod vertical
          (boundary, latitude boundary) at hVerticalChain
  rw [← candidateANormalBoundary_mvfderiv_real_eq_mfderiv period hPeriod
    verticalGraph boundary vector] at hVerticalChain
  rw [← hSlopeAt outer boundary] at hVerticalChain
  have hSlopeDerivative :
      mvfderiv throatCoverModelWithCorners (slope inner) boundary vector =
        candidateANormalBoundaryLatitudeSpatialSecondFiberEvaluation
          period hPeriod metric outer inner current boundary := by
    exact (candidateANormalBoundaryLatitudeSpatialSecond_smooth
      period hPeriod metric tensor displacement parameter boundary outer
        inner).symm
  have hProduct := congrArg (fun derivative => derivative vector)
    (mvfderiv_mul
      ((hSlopeSmooth inner).mdifferentiableAt (by simp))
      (hVerticalGraphSmooth.mdifferentiableAt (by simp)))
  have hProductApply :
      mvfderiv throatCoverModelWithCorners
          (slope inner * verticalGraph) boundary vector =
        slope inner boundary *
            mvfderiv throatCoverModelWithCorners verticalGraph boundary vector +
          verticalGraph boundary *
            mvfderiv throatCoverModelWithCorners (slope inner) boundary
              vector := by
    simpa only [add_apply, smul_apply, smul_eq_mul] using hProduct
  have hSum := congrArg (fun derivative => derivative vector)
    (mvfderiv_add
      (hHorizontalGraphSmooth.mdifferentiableAt (by simp))
      (((hSlopeSmooth inner).mul hVerticalGraphSmooth).mdifferentiableAt
        (by simp)))
  have hGraphDerivative :
      mvfderiv throatCoverModelWithCorners graphCoefficient boundary vector =
        normalBoundaryHorizontalFieldDerivative period hPeriod outer horizontal
              (boundary, latitude boundary) +
          slope outer boundary *
              normalBoundaryLatitudeFieldDerivative period hPeriod horizontal
                (boundary, latitude boundary) +
          candidateANormalBoundaryLatitudeSpatialSecondFiberEvaluation
              period hPeriod metric outer inner current boundary *
            verticalGraph boundary +
          slope inner boundary *
            (normalBoundaryHorizontalFieldDerivative period hPeriod outer
                vertical (boundary, latitude boundary) +
              slope outer boundary *
                normalBoundaryLatitudeFieldDerivative period hPeriod vertical
                  (boundary, latitude boundary)) := by
    change mvfderiv throatCoverModelWithCorners
        (horizontalGraph + slope inner * verticalGraph) boundary vector = _
    rw [show mvfderiv throatCoverModelWithCorners
          (horizontalGraph + slope inner * verticalGraph) boundary vector =
        mvfderiv throatCoverModelWithCorners horizontalGraph boundary vector +
          mvfderiv throatCoverModelWithCorners
            (slope inner * verticalGraph) boundary vector by
      simpa only [add_apply] using hSum]
    rw [hHorizontalChain, hProductApply, hVerticalChain, hSlopeDerivative]
    ring
  have hCandidateFormula :
      candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivativeFiberEvaluation
          period hPeriod metric outer inner row current boundary =
        normalBoundaryHorizontalFieldDerivative period hPeriod outer horizontal
              (boundary, latitude boundary) +
          slope outer boundary *
              normalBoundaryLatitudeFieldDerivative period hPeriod horizontal
                (boundary, latitude boundary) +
          candidateANormalBoundaryLatitudeSpatialSecondFiberEvaluation
              period hPeriod metric outer inner current boundary *
            verticalGraph boundary +
          slope inner boundary *
            (normalBoundaryHorizontalFieldDerivative period hPeriod outer
                vertical (boundary, latitude boundary) +
              slope outer boundary *
                normalBoundaryLatitudeFieldDerivative period hPeriod vertical
                  (boundary, latitude boundary)) := by
    unfold candidateANormalBoundaryGraphTangentRegularFrameSpatialDerivativeFiberEvaluation
    change
      candidateANormalBoundaryHorizontalCoefficientSourceDerivativeFiberEvaluation
            period hPeriod metric outer inner row current boundary +
        slope outer boundary *
          candidateANormalBoundaryHorizontalCoefficientLatitudeDerivativeFiberEvaluation
            period hPeriod metric inner row current boundary +
        candidateANormalBoundaryLatitudeSpatialSecondFiberEvaluation
            period hPeriod metric outer inner current boundary *
          candidateANormalBoundaryVerticalRegularFrameCoefficientFiberEvaluation
            period hPeriod metric row current boundary +
        slope inner boundary *
          (candidateANormalBoundaryVerticalCoefficientSourceDerivativeFiberEvaluation
              period hPeriod metric outer row current boundary +
            slope outer boundary *
              candidateANormalBoundaryVerticalCoefficientLatitudeDerivativeFiberEvaluation
                period hPeriod metric row current boundary) = _
    rw [hHorizontalSource, hHorizontalLatitude, hVerticalValue,
      hVerticalSource, hVerticalLatitude]
  have hCoefficient :
      (fun point : CutThroatBoundary period hPeriod =>
        candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric inner row current point) = graphCoefficient := by
    funext point
    unfold graphCoefficient
    change
      candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation
          period hPeriod metric inner row current point =
        horizontalGraph point + slope inner point * verticalGraph point
    rw [candidateANormalBoundaryGraphTangentRegularFrameCoefficientFiberEvaluation_apply]
    change horizontalGraph point +
        (parameter * normalBoundaryC2JetCoreFirstAt period hPeriod point
          (smoothNormalDisplacementToBoundaryC2JetCore
            period hPeriod displacement) inner) *
          ((1 / (1 + (parameter *
            normalBoundaryC2JetCoreValueAt period hPeriod point
              (smoothNormalDisplacementToBoundaryC2JetCore
                period hPeriod displacement)) ^ 2)) * verticalGraph point) = _
    unfold slope
    unfold candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation
    change horizontalGraph point +
        (parameter * normalBoundaryC2JetCoreFirstAt period hPeriod point
          (smoothNormalDisplacementToBoundaryC2JetCore
            period hPeriod displacement) inner) *
          ((1 / (1 + (parameter *
            normalBoundaryC2JetCoreValueAt period hPeriod point
              (smoothNormalDisplacementToBoundaryC2JetCore
                period hPeriod displacement)) ^ 2)) * verticalGraph point) =
      horizontalGraph point +
        (normalBoundaryC2ScaledRawSpatialFirst period hPeriod inner
            (smoothNormalDisplacementToBoundaryC2JetCore
              period hPeriod displacement, parameter) point *
          candidateANormalBoundaryRawArctanDerivativeFiberEvaluation
            period hPeriod metric current point) * verticalGraph point
    rw [candidateANormalBoundaryRawArctanDerivativeFiberEvaluation_apply]
    rw [show candidateANormalBoundaryRawGraphFiberEvaluation period hPeriod
          metric current point =
        parameter * normalBoundaryC2JetCoreValueAt period hPeriod point
          (smoothNormalDisplacementToBoundaryC2JetCore
            period hPeriod displacement) by rfl]
    rw [normalBoundaryC2ScaledRawSpatialFirst_apply]
    ring
  rw [hCandidateFormula, ← hGraphDerivative, hCoefficient]

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
