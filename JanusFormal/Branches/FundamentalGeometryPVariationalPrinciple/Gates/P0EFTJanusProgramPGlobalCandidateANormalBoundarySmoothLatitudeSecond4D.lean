import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySmoothActualMetricDerivative4D

/-!
# Smooth second latitude jet for the mobile Candidate-A graph

The stored second latitude jet is identified with the second directional
manifold derivative of the canonical `arctan` graph latitude.  The proof uses
only the existing smooth displacement, finite throat frame, and elementary
chain/product rules.
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

local instance (priority := 30000) smoothLatitudeSecondOrientationBoundaryChartedSpace :
    ChartedSpace ThroatCoverModel (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace
    period hPeriod

local instance (priority := 30000) smoothLatitudeSecondOrientationBoundaryIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (CutThroatBoundary period hPeriod) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold
    period hPeriod

set_option backward.isDefEq.respectTransparency false in
/-- Chain rule for a smooth collar scalar restricted to a smooth graph. -/
theorem candidateANormalBoundarySmoothCollarField_mvfderiv_graph
    (field : CutThroatBoundary period hPeriod × Real → Real)
    (hField : ContMDiff
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) ∞ field)
    (latitude : CutThroatBoundary period hPeriod → Real)
    (hLatitude : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ latitude)
    (boundary : CutThroatBoundary period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod) :
    let vector :=
      (finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
          boundary index
    let slope := mvfderiv throatCoverModelWithCorners latitude boundary vector
    mfderiv throatCoverModelWithCorners (modelWithCornersSelf Real Real)
        (fun point : CutThroatBoundary period hPeriod =>
          field (point, latitude point)) boundary vector =
      normalBoundaryHorizontalFieldDerivative period hPeriod index field
          (boundary, latitude boundary) +
        slope • normalBoundaryLatitudeFieldDerivative period hPeriod field
          (boundary, latitude boundary) := by
  dsimp only
  let vector :=
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
        boundary index
  let slope := mvfderiv throatCoverModelWithCorners latitude boundary vector
  let graphParameter : CutThroatBoundary period hPeriod →
      CutThroatBoundary period hPeriod × Real :=
    fun point => (point, latitude point)
  have hParameter : MDifferentiableAt throatCoverModelWithCorners
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      graphParameter boundary :=
    (contMDiff_id.prodMk hLatitude).mdifferentiableAt (by simp)
  have hFieldAt : MDifferentiableAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) field (graphParameter boundary) :=
    hField.mdifferentiableAt (by simp)
  have hParameterDerivative := congrArg (fun derivative => derivative vector)
    (mfderiv_prodMk
      (f := fun point : CutThroatBoundary period hPeriod => point)
      (g := latitude) mdifferentiableAt_id
      (hLatitude.mdifferentiableAt (by simp)))
  have hParameterApply :
      mfderiv throatCoverModelWithCorners
          (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
          graphParameter boundary vector = (vector, slope) := by
    refine hParameterDerivative.trans ?_
    change
      (mfderiv throatCoverModelWithCorners throatCoverModelWithCorners id
          boundary vector,
        mfderiv throatCoverModelWithCorners (modelWithCornersSelf Real Real)
          latitude boundary vector) = (vector, slope)
    rw [mfderiv_id]
    rfl
  have hCompApply :
      mfderiv throatCoverModelWithCorners (modelWithCornersSelf Real Real)
          (field ∘ graphParameter) boundary vector =
        mfderiv
          (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
          (modelWithCornersSelf Real Real) field (graphParameter boundary)
            (mfderiv throatCoverModelWithCorners
              (throatCoverModelWithCorners.prod
                (modelWithCornersSelf Real Real))
              graphParameter boundary vector) := by
    exact mfderiv_comp_apply boundary hFieldAt hParameter vector
  have hGraph :
      mfderiv throatCoverModelWithCorners (modelWithCornersSelf Real Real)
          (fun point : CutThroatBoundary period hPeriod =>
            field (point, latitude point)) boundary vector =
        mfderiv
          (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
          (modelWithCornersSelf Real Real) field
          (boundary, latitude boundary) (vector, slope) := by
    rw [hParameterApply] at hCompApply
    simpa only [graphParameter, Function.comp_def] using hCompApply
  rw [hGraph]
  have hSplit := mfderiv_prod_eq_add_apply
    (E := ThroatCoverCoordinates) (E' := Real)
    (I := throatCoverModelWithCorners)
    (I' := modelWithCornersSelf Real Real)
    (v := (vector, slope)) hFieldAt
  dsimp only [graphParameter] at hSplit
  have hFieldAtCurrent : MDifferentiableAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
      (modelWithCornersSelf Real Real) field
      (boundary, latitude boundary) := by
    simpa only [graphParameter] using hFieldAt
  have hHorizontal :
      normalBoundaryHorizontalFieldDerivative period hPeriod index field
          (boundary, latitude boundary) =
        mfderiv throatCoverModelWithCorners (modelWithCornersSelf Real Real)
          (fun point : CutThroatBoundary period hPeriod =>
            field (point, latitude boundary)) boundary vector := by
    have hProduct := mfderiv_prod_eq_add_apply
      (E := ThroatCoverCoordinates) (E' := Real)
      (I := throatCoverModelWithCorners)
      (I' := modelWithCornersSelf Real Real)
      (v := (vector, 0)) hFieldAtCurrent
    rw [map_zero, add_zero] at hProduct
    unfold normalBoundaryHorizontalFieldDerivative
      normalBoundaryLatitudeHorizontalTangentLift
    change mfderiv
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        (modelWithCornersSelf Real Real) field
        (boundary, latitude boundary) (vector, 0) = _
    exact hProduct
  have hVertical :
      normalBoundaryLatitudeFieldDerivative period hPeriod field
          (boundary, latitude boundary) =
        mfderiv (modelWithCornersSelf Real Real)
          (modelWithCornersSelf Real Real)
          (fun varied : Real => field (boundary, varied))
          (latitude boundary) 1 := by
    have hProduct := mfderiv_prod_eq_add_apply
      (E := ThroatCoverCoordinates) (E' := Real)
      (I := throatCoverModelWithCorners)
      (I' := modelWithCornersSelf Real Real)
      (v := (0, 1)) hFieldAtCurrent
    rw [map_zero, zero_add] at hProduct
    unfold normalBoundaryLatitudeFieldDerivative
      normalBoundaryLatitudeQuotientVerticalTangentLift
    change mfderiv
        (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real))
        (modelWithCornersSelf Real Real) field
        (boundary, latitude boundary) (0, 1) = _
    exact hProduct
  have hVerticalSlope :
      mfderiv (modelWithCornersSelf Real Real)
          (modelWithCornersSelf Real Real)
          (fun varied : Real => field (boundary, varied))
          (latitude boundary) slope =
        slope • mfderiv (modelWithCornersSelf Real Real)
          (modelWithCornersSelf Real Real)
          (fun varied : Real => field (boundary, varied))
          (latitude boundary) 1 := by
    calc
      mfderiv (modelWithCornersSelf Real Real)
          (modelWithCornersSelf Real Real)
          (fun varied : Real => field (boundary, varied))
          (latitude boundary) slope =
        mfderiv (modelWithCornersSelf Real Real)
          (modelWithCornersSelf Real Real)
          (fun varied : Real => field (boundary, varied))
          (latitude boundary) (slope • (1 : Real)) := by simp
      _ = slope • mfderiv (modelWithCornersSelf Real Real)
          (modelWithCornersSelf Real Real)
          (fun varied : Real => field (boundary, varied))
          (latitude boundary) 1 := by rw [map_smul]
  rw [hSplit, ← hHorizontal, hVerticalSlope, ← hVertical]

set_option backward.isDefEq.respectTransparency false in
/-- Derivative of the reciprocal quadratic appearing in the derivative of
`arctan`. -/
theorem candidateANormalBoundaryReciprocalQuadratic_mvfderiv
    (raw : CutThroatBoundary period hPeriod → Real)
    (hRaw : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ raw)
    (boundary : CutThroatBoundary period hPeriod)
    (vector : TangentSpace throatCoverModelWithCorners boundary) :
    mvfderiv throatCoverModelWithCorners
        (fun point => 1 / (1 + raw point ^ 2)) boundary vector =
      (-2 * raw boundary * (1 / (1 + raw boundary ^ 2)) ^ 2) *
        mvfderiv throatCoverModelWithCorners raw boundary vector := by
  let reciprocalQuadratic : Real → Real := fun value =>
    1 / (1 + value ^ 2)
  have hReciprocalQuadratic (value : Real) : HasDerivAt
      reciprocalQuadratic
      (-2 * value * (1 / (1 + value ^ 2)) ^ 2) value := by
    let denominator : Real → Real := fun varied => 1 + varied ^ 2
    have hDenominator : HasDerivAt denominator
        (2 * value) value := by
      simpa [denominator] using ((hasDerivAt_id value).pow 2).const_add 1
    have hInverse := (hasDerivAt_inv
      (show denominator value ≠ 0 by dsimp only [denominator]; positivity))
        |>.comp value hDenominator
    convert! hInverse using 1
    · funext varied
      change 1 / (1 + varied ^ 2) = (1 + varied ^ 2)⁻¹
      exact one_div _
    · change -2 * value * (1 / (1 + value ^ 2)) ^ 2 =
        -((1 + value ^ 2) ^ 2)⁻¹ * (2 * value)
      field_simp
  have hOuter :=
    (hReciprocalQuadratic (raw boundary)).hasFDerivAt.hasMFDerivAt
  have hComp := hOuter.comp boundary
    (hRaw.mdifferentiableAt (by simp)).hasMFDerivAt
  have hDerivative := congrArg (fun derivative => derivative vector) hComp.mfderiv
  have hDerivative' := congrArg
    (NormedSpace.fromTangentSpace (reciprocalQuadratic (raw boundary)))
    hDerivative
  change mvfderiv throatCoverModelWithCorners
      (reciprocalQuadratic ∘ raw) boundary vector = _
  refine hDerivative'.trans ?_
  change (NormedSpace.fromTangentSpace (reciprocalQuadratic (raw boundary)))
      (ContinuousLinearMap.toSpanSingleton Real
        (-2 * raw boundary * (1 / (1 + raw boundary ^ 2)) ^ 2)
          (mfderiv throatCoverModelWithCorners
            (modelWithCornersSelf Real Real) raw boundary vector)) = _
  rw [ContinuousLinearMap.toSpanSingleton_apply]
  change mvfderiv throatCoverModelWithCorners raw boundary vector *
      (-2 * raw boundary * (1 / (1 + raw boundary ^ 2)) ^ 2) = _
  ring

set_option backward.isDefEq.respectTransparency false in
/-- The stored scaled first raw spatial jet is the directional derivative of
the smooth scaled displacement. -/
theorem candidateANormalBoundaryC2ScaledRawSpatialFirst_smooth
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (index : NormalBoundaryTangentIndex period hPeriod) :
    normalBoundaryC2ScaledRawSpatialFirst period hPeriod index
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement, parameter) boundary =
      mvfderiv throatCoverModelWithCorners
        (fun point : CutThroatBoundary period hPeriod =>
          parameter * normalDisplacementOrientationScalar
            period hPeriod displacement point)
        boundary
        ((finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
            boundary index) := by
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  let field := normalDisplacementOrientationSmoothField
    period hPeriod displacement
  have hScaled := congrFun (congrFun
    (throatFrameDerivative_smul
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      Real frame parameter field) boundary) index
  rw [normalBoundaryC2ScaledRawSpatialFirst_apply,
    normalBoundaryC2JetCoreFirstAt_smooth]
  rw [throatFrameDerivative_eq_mvfderiv] at hScaled
  change parameter * throatFrameDerivative
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      Real frame field boundary index = _
  change mvfderiv throatCoverModelWithCorners
      (fun point : CutThroatBoundary period hPeriod =>
        parameter * normalDisplacementOrientationScalar
          period hPeriod displacement point)
      boundary
      ((finiteSmoothThroatGeneratingFrame
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
          boundary index) =
    parameter * throatFrameDerivative
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      Real frame field boundary index at hScaled
  exact hScaled.symm

set_option backward.isDefEq.respectTransparency false in
/-- The stored scaled second raw spatial jet is the derivative of the first
raw jet along the outer frame vector. -/
theorem candidateANormalBoundaryC2ScaledRawSpatialSecond_smooth
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (outer inner : NormalBoundaryTangentIndex period hPeriod) :
    normalBoundaryC2ScaledRawSpatialSecond period hPeriod outer inner
        (smoothNormalDisplacementToBoundaryC2JetCore
          period hPeriod displacement, parameter) boundary =
      mvfderiv throatCoverModelWithCorners
        (fun point : CutThroatBoundary period hPeriod =>
          normalBoundaryC2ScaledRawSpatialFirst period hPeriod inner
            (smoothNormalDisplacementToBoundaryC2JetCore
              period hPeriod displacement, parameter) point)
        boundary
        ((finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
            boundary outer) := by
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  let field := normalDisplacementOrientationSmoothField
    period hPeriod displacement
  let scaledField : SmoothThroatField
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) Real :=
    parameter • field
  have hFunction :
      (fun point : CutThroatBoundary period hPeriod =>
        normalBoundaryC2ScaledRawSpatialFirst period hPeriod inner
          (smoothNormalDisplacementToBoundaryC2JetCore
            period hPeriod displacement, parameter) point) =
        (normalBoundaryFrameDerivativeComponentField period hPeriod frame
          scaledField inner).toFun := by
    funext point
    rw [candidateANormalBoundaryC2ScaledRawSpatialFirst_smooth]
    change mvfderiv throatCoverModelWithCorners
        (fun current : CutThroatBoundary period hPeriod =>
          parameter * normalDisplacementOrientationScalar
            period hPeriod displacement current)
        point (frame.vectorAt point inner) =
      throatFrameDerivative
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        Real frame scaledField point inner
    rw [throatFrameDerivative_eq_mvfderiv]
    rfl
  rw [hFunction]
  change normalBoundaryC2ScaledRawSpatialSecond period hPeriod outer inner
      (smoothNormalDisplacementToBoundaryC2JetCore
        period hPeriod displacement, parameter) boundary =
    throatFrameDerivative
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      Real frame
      (normalBoundaryFrameDerivativeComponentField period hPeriod frame
        scaledField inner) boundary outer
  change normalBoundaryC2ScaledRawSpatialSecond period hPeriod outer inner
      (smoothNormalDisplacementToBoundaryC2JetCore
        period hPeriod displacement, parameter) boundary =
    normalBoundaryFrameSecondDerivative period hPeriod frame scaledField
      boundary outer inner
  rw [normalBoundaryC2ScaledRawSpatialSecond_apply,
    normalBoundaryC2JetCoreSecondAt_smooth]
  have hScaled := congrFun (congrFun (congrFun
    (normalBoundaryFrameSecondDerivative_smul period hPeriod frame
      parameter field) boundary) outer) inner
  simpa only [scaledField, field, frame, Pi.smul_apply, smul_eq_mul] using
    hScaled.symm

set_option backward.isDefEq.respectTransparency false in
/-- The completed second latitude coefficient is the derivative of the first
latitude coefficient along the outer frame vector. -/
theorem candidateANormalBoundaryLatitudeSpatialSecond_smooth
    (metric : RegularGeneralLorentzMetric period hPeriod)
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod)
    (parameter : Real) (boundary : CutThroatBoundary period hPeriod)
    (outer inner : NormalBoundaryTangentIndex period hPeriod) :
    candidateANormalBoundaryLatitudeSpatialSecondFiberEvaluation
        period hPeriod metric outer inner
        (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
          (tensor, displacement), parameter) boundary =
      mvfderiv throatCoverModelWithCorners
        (fun point : CutThroatBoundary period hPeriod =>
          candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation
            period hPeriod metric inner
            (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod
              metric (tensor, displacement), parameter) point)
        boundary
        ((finiteSmoothThroatGeneratingFrame
          (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
            boundary outer) := by
  let normal := smoothNormalDisplacementToBoundaryC2JetCore
    period hPeriod displacement
  let current :=
    (smoothToCandidateANormalBoundaryFunctionalCore period hPeriod metric
      (tensor, displacement), parameter)
  let raw : CutThroatBoundary period hPeriod → Real := fun point =>
    parameter * normalDisplacementOrientationScalar
      period hPeriod displacement point
  let first (index : NormalBoundaryTangentIndex period hPeriod) :
      CutThroatBoundary period hPeriod → Real := fun point =>
    normalBoundaryC2ScaledRawSpatialFirst period hPeriod index
      (normal, parameter) point
  let reciprocal : CutThroatBoundary period hPeriod → Real := fun point =>
    1 / (1 + raw point ^ 2)
  let vector :=
    (finiteSmoothThroatGeneratingFrame
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt
        boundary outer
  let frame := finiteSmoothThroatGeneratingFrame
    (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
  let scalarField := normalDisplacementOrientationSmoothField
    period hPeriod displacement
  let scaledField : SmoothThroatField
      (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) Real :=
    parameter • scalarField
  have hCurrentNormal : current.1.2 = normal := rfl
  have hCurrentParameter : current.2 = parameter := rfl
  have hRawEvaluation :
      candidateANormalBoundaryRawGraphFiberEvaluation period hPeriod metric
          current boundary = raw boundary := by
    rfl
  have hReciprocalEvaluation :
      candidateANormalBoundaryRawArctanDerivativeFiberEvaluation
          period hPeriod metric current boundary = reciprocal boundary := by
    rw [candidateANormalBoundaryRawArctanDerivativeFiberEvaluation_apply]
    rfl
  have hRawSmooth : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ raw := by
    exact contMDiff_const.mul
      (normalDisplacementOrientationScalar_contMDiff
        period hPeriod displacement)
  have hFirstFunction (index : NormalBoundaryTangentIndex period hPeriod) :
      first index =
        (normalBoundaryFrameDerivativeComponentField period hPeriod frame
          scaledField index).toFun := by
    funext point
    dsimp only [first, normal]
    rw [candidateANormalBoundaryC2ScaledRawSpatialFirst_smooth]
    change mvfderiv throatCoverModelWithCorners raw point
        (frame.vectorAt point index) =
      throatFrameDerivative
        (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
        Real frame scaledField point index
    rw [throatFrameDerivative_eq_mvfderiv]
    rfl
  have hFirstSmooth (index : NormalBoundaryTangentIndex period hPeriod) :
      ContMDiff throatCoverModelWithCorners
        (modelWithCornersSelf Real Real) ∞ (first index) := by
    rw [hFirstFunction]
    exact (normalBoundaryFrameDerivativeComponentField period hPeriod frame
      scaledField index).contMDiff_toFun
  have hReciprocalSmooth : ContMDiff throatCoverModelWithCorners
      (modelWithCornersSelf Real Real) ∞ reciprocal := by
    have hDenominator : ContMDiff throatCoverModelWithCorners
        (modelWithCornersSelf Real Real) ∞
        (fun point => 1 + raw point ^ 2) :=
      contMDiff_const.add (hRawSmooth.pow 2)
    have hInverse := hDenominator.inv₀ (fun point => by positivity)
    simpa only [reciprocal, one_div] using hInverse
  have hCandidateFirst :
      (fun point : CutThroatBoundary period hPeriod =>
        candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation
          period hPeriod metric inner current point) =
        first inner * reciprocal := by
    funext point
    unfold candidateANormalBoundaryLatitudeSpatialFirstFiberEvaluation
    change normalBoundaryC2ScaledRawSpatialFirst period hPeriod inner
          (normal, parameter) point *
        candidateANormalBoundaryRawArctanDerivativeFiberEvaluation
          period hPeriod metric current point =
      first inner point * reciprocal point
    rw [candidateANormalBoundaryRawArctanDerivativeFiberEvaluation_apply]
    rfl
  have hRawDerivative :
      mvfderiv throatCoverModelWithCorners raw boundary vector =
        first outer boundary := by
    exact (candidateANormalBoundaryC2ScaledRawSpatialFirst_smooth period hPeriod
      displacement parameter boundary outer).symm
  have hFirstDerivative :
      mvfderiv throatCoverModelWithCorners (first inner) boundary vector =
        normalBoundaryC2ScaledRawSpatialSecond period hPeriod outer inner
          (normal, parameter) boundary := by
    exact (candidateANormalBoundaryC2ScaledRawSpatialSecond_smooth period hPeriod
      displacement parameter boundary outer inner).symm
  have hReciprocalDerivative :
      mvfderiv throatCoverModelWithCorners reciprocal boundary vector =
        (-2 * raw boundary * reciprocal boundary ^ 2) *
          first outer boundary := by
    have hDerivative := candidateANormalBoundaryReciprocalQuadratic_mvfderiv
      period hPeriod raw hRawSmooth boundary vector
    rw [hRawDerivative] at hDerivative
    simpa only [reciprocal] using hDerivative
  have hProduct := congrArg (fun derivative => derivative vector)
    (mvfderiv_mul
      ((hFirstSmooth inner).mdifferentiableAt (by simp))
      (hReciprocalSmooth.mdifferentiableAt (by simp)))
  have hProductApply :
      mvfderiv throatCoverModelWithCorners
          (first inner * reciprocal) boundary vector =
        first inner boundary *
            mvfderiv throatCoverModelWithCorners reciprocal boundary vector +
          reciprocal boundary *
            mvfderiv throatCoverModelWithCorners (first inner) boundary
              vector := by
    simpa only [add_apply, smul_apply, smul_eq_mul] using hProduct
  have hCandidateSecond :
      candidateANormalBoundaryLatitudeSpatialSecondFiberEvaluation
          period hPeriod metric outer inner current boundary =
        normalBoundaryC2ScaledRawSpatialSecond period hPeriod outer inner
              (normal, parameter) boundary * reciprocal boundary -
          2 * raw boundary * first outer boundary * first inner boundary *
            reciprocal boundary ^ 2 := by
    unfold candidateANormalBoundaryLatitudeSpatialSecondFiberEvaluation
    change
      normalBoundaryC2ScaledRawSpatialSecond period hPeriod outer inner
            (current.1.2, current.2) boundary *
          candidateANormalBoundaryRawArctanDerivativeFiberEvaluation
            period hPeriod metric current boundary -
        2 * (candidateANormalBoundaryRawGraphFiberEvaluation period hPeriod
              metric current boundary *
            normalBoundaryC2ScaledRawSpatialFirst period hPeriod outer
              (current.1.2, current.2) boundary *
            normalBoundaryC2ScaledRawSpatialFirst period hPeriod inner
              (current.1.2, current.2) boundary *
            candidateANormalBoundaryRawArctanDerivativeFiberEvaluation
              period hPeriod metric current boundary ^ 2) = _
    rw [hCurrentNormal, hCurrentParameter, hRawEvaluation,
      hReciprocalEvaluation]
    dsimp only [first]
    ring
  rw [hCandidateSecond, hCandidateFirst, hProductApply,
    hReciprocalDerivative, hFirstDerivative]
  ring

end
end P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
end JanusFormal
