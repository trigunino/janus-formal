import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetric4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalCandidateANormalBoundarySmoothLatitudeSecond4D

/-! First and ordered second throat derivatives of the actual arctangent
latitude. The raw displacement and its latitude are kept distinct. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryLatitudeSpatialJets4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff BoundedContinuousFunction
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient P0EFTJanusMappingTorusSmoothThroatTrace4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetric4D

variable (period : Real) (hPeriod : period ≠ 0)
local notation "Boundary" => OrientationBoundary period hPeriod
local instance : CompactSpace Boundary :=
  fixedThroatQuotientCompactSpace (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
local instance : ChartedSpace ThroatCoverModel Boundary :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω Boundary :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold period hPeriod
local instance : NormedAddCommGroup (NormalBoundaryC2JetCore period hPeriod) :=
  (normalBoundaryC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (NormalBoundaryC2JetCore period hPeriod) :=
  Submodule.normedSpace (normalBoundaryC2JetCoreSubmodule period hPeriod)
local notation "Input" => NormalBoundaryC2JetCore period hPeriod × Real
local notation "Index" => NormalBoundaryTangentIndex period hPeriod
local notation "Field" => BoundedContinuousFunction Boundary Real
local notation "CollarModel" => throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)
local notation "frame" => finiteSmoothThroatGeneratingFrame
  (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

def frameFreeBoundaryLatitudeSpatialFirst (index : Index) (current : Input) : Field :=
  frameFreeBoundaryArctanDerivativeEvaluation period hPeriod current *
    normalBoundaryC2ScaledRawSpatialFirst period hPeriod index current

def frameFreeBoundaryLatitudeSpatialSecond (outer inner : Index) (current : Input) : Field :=
  frameFreeBoundaryArctanDerivativeEvaluation period hPeriod current *
      normalBoundaryC2ScaledRawSpatialSecond period hPeriod outer inner current -
    (2 : Real) • (normalBoundaryC2ScaledRawGraph period hPeriod current *
      normalBoundaryC2ScaledRawSpatialFirst period hPeriod outer current *
      normalBoundaryC2ScaledRawSpatialFirst period hPeriod inner current *
      (frameFreeBoundaryArctanDerivativeEvaluation period hPeriod current) ^ 2)

theorem frameFreeBoundaryLatitudeSpatialFirst_contDiff_two (index : Index) :
    ContDiff Real 2 (frameFreeBoundaryLatitudeSpatialFirst period hPeriod index) :=
  (frameFreeBoundaryArctanDerivativeEvaluation_contDiff_two period hPeriod).mul
    (normalBoundaryC2ScaledRawSpatialFirst_contDiff_two period hPeriod index)

theorem frameFreeBoundaryLatitudeSpatialSecond_contDiff_two (outer inner : Index) :
    ContDiff Real 2 (frameFreeBoundaryLatitudeSpatialSecond period hPeriod outer inner) := by
  have hQ := frameFreeBoundaryArctanDerivativeEvaluation_contDiff_two period hPeriod
  have hFirst := normalBoundaryC2ScaledRawSpatialFirst_contDiff_two period hPeriod
  exact (hQ.mul (normalBoundaryC2ScaledRawSpatialSecond_contDiff_two period hPeriod outer inner)).sub
    (ContDiff.const_smul (2 : Real)
      ((((normalBoundaryC2ScaledRawGraph_contDiff_two period hPeriod).mul (hFirst outer)).mul
        (hFirst inner)).mul (hQ.pow 2)))

theorem frameFreeBoundarySmoothFiberEvaluation_smooth_apply
    (field : Boundary × Real → Real)
    (hField : ContMDiff CollarModel (modelWithCornersSelf Real Real) ∞ field)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real) (boundary : Boundary) :
    normalBoundarySmoothFiberEvaluation period hPeriod field hField
      (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement, parameter) boundary =
      field (boundary, Real.arctan (parameter * normalDisplacementOrientationScalar period hPeriod displacement boundary)) := by
  rw [normalBoundarySmoothFiberEvaluation_apply, normalBoundaryC2JetCoreValueAt_smooth]

theorem frameFreeBoundarySmoothFiberEvaluation_smooth_contMDiff
    (field : Boundary × Real → Real)
    (hField : ContMDiff CollarModel (modelWithCornersSelf Real Real) ∞ field)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real) :
    ContMDiff throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (fun boundary : Boundary => normalBoundarySmoothFiberEvaluation period hPeriod field hField
        (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement, parameter) boundary) := by
  have hFunction : (fun boundary : Boundary => normalBoundarySmoothFiberEvaluation period hPeriod field hField
      (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement, parameter) boundary) =
      fun boundary => field (boundary, Real.arctan
        (parameter * normalDisplacementOrientationScalar period hPeriod displacement boundary)) :=
    funext (frameFreeBoundarySmoothFiberEvaluation_smooth_apply period hPeriod field hField displacement parameter)
  rw [hFunction]
  exact hField.comp (contMDiff_id.prodMk (Real.contDiff_arctan.contMDiff.comp
    (contMDiff_const.mul (normalDisplacementOrientationScalar_contMDiff period hPeriod displacement))))

theorem frameFreeBoundaryRawSpatialFirst_smooth_contMDiff
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real) (index : Index) :
    ContMDiff throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (fun boundary : Boundary => normalBoundaryC2ScaledRawSpatialFirst period hPeriod index
        (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement, parameter) boundary) := by
  let scaled : SmoothThroatField (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod) Real :=
    parameter • normalDisplacementOrientationSmoothField period hPeriod displacement
  have hFunction : (fun boundary : Boundary => normalBoundaryC2ScaledRawSpatialFirst period hPeriod index
      (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement, parameter) boundary) =
      (normalBoundaryFrameDerivativeComponentField period hPeriod frame scaled index).toFun := by
    funext boundary
    rw [candidateANormalBoundaryC2ScaledRawSpatialFirst_smooth]
    change _ = throatFrameDerivative (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
      Real frame scaled boundary index
    rw [throatFrameDerivative_eq_mvfderiv]
    rfl
  rw [hFunction]
  exact (normalBoundaryFrameDerivativeComponentField period hPeriod frame scaled index).contMDiff_toFun

theorem frameFreeBoundaryArctanDerivativeEvaluation_smooth_contMDiff
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real) :
    ContMDiff throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (fun boundary : Boundary => frameFreeBoundaryArctanDerivativeEvaluation period hPeriod
        (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement, parameter) boundary) := by
  unfold frameFreeBoundaryArctanDerivativeEvaluation
  apply frameFreeBoundarySmoothFiberEvaluation_smooth_contMDiff

theorem frameFreeBoundaryLatitudeSpatialFirst_smooth_contMDiff
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real) (index : Index) :
    ContMDiff throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞
      (fun boundary : Boundary => frameFreeBoundaryLatitudeSpatialFirst period hPeriod index
        (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement, parameter) boundary) :=
  (frameFreeBoundaryArctanDerivativeEvaluation_smooth_contMDiff period hPeriod displacement parameter).mul
    (frameFreeBoundaryRawSpatialFirst_smooth_contMDiff period hPeriod displacement parameter index)

theorem frameFreeBoundaryLatitudeSpatialFirst_smooth
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real) (boundary : Boundary) (index : Index) :
    frameFreeBoundaryLatitudeSpatialFirst period hPeriod index
      (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement, parameter) boundary =
      mvfderiv throatCoverModelWithCorners
        (fun point : Boundary => Real.arctan (parameter * normalDisplacementOrientationScalar period hPeriod displacement point))
        boundary ((frame).vectorAt boundary index) := by
  rw [normalGraphLatitude_mvfderiv_frame]
  simp only [frameFreeBoundaryLatitudeSpatialFirst, BoundedContinuousFunction.mul_apply,
    frameFreeBoundaryArctanDerivativeEvaluation_apply, normalBoundaryC2ScaledRawSpatialFirst_apply]

private theorem reciprocalDerivative_smooth
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real) (boundary : Boundary) (outer : Index) :
    let current := (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement, parameter)
    mvfderiv throatCoverModelWithCorners
      (fun point : Boundary => frameFreeBoundaryArctanDerivativeEvaluation period hPeriod current point)
      boundary ((frame).vectorAt boundary outer) =
      (-2 * normalBoundaryC2ScaledRawGraph period hPeriod current boundary *
        (frameFreeBoundaryArctanDerivativeEvaluation period hPeriod current boundary) ^ 2) *
        normalBoundaryC2ScaledRawSpatialFirst period hPeriod outer current boundary := by
  dsimp only
  let raw : Boundary → Real := fun point => parameter * normalDisplacementOrientationScalar period hPeriod displacement point
  have hRaw : ContMDiff throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞ raw :=
    contMDiff_const.mul (normalDisplacementOrientationScalar_contMDiff period hPeriod displacement)
  have hFunction : (fun point : Boundary => frameFreeBoundaryArctanDerivativeEvaluation period hPeriod
      (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement, parameter) point) =
      fun point => 1 / (1 + raw point ^ 2) := by
    funext point
    rw [frameFreeBoundaryArctanDerivativeEvaluation_apply, normalBoundaryC2JetCoreValueAt_smooth]
  rw [hFunction]
  have h := candidateANormalBoundaryReciprocalQuadratic_mvfderiv period hPeriod raw hRaw boundary
    ((frame).vectorAt boundary outer)
  rw [← candidateANormalBoundaryC2ScaledRawSpatialFirst_smooth period hPeriod displacement parameter boundary outer] at h
  simpa only [normalBoundaryC2ScaledRawGraph_apply, normalBoundaryC2JetCoreValueAt_smooth,
    frameFreeBoundaryArctanDerivativeEvaluation_apply, raw] using h

theorem frameFreeBoundaryLatitudeSpatialSecond_smooth
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real) (boundary : Boundary)
    (outer inner : Index) :
    let current := (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement, parameter)
    frameFreeBoundaryLatitudeSpatialSecond period hPeriod outer inner current boundary =
      mvfderiv throatCoverModelWithCorners
        (fun point : Boundary => frameFreeBoundaryLatitudeSpatialFirst period hPeriod inner current point)
        boundary ((frame).vectorAt boundary outer) := by
  dsimp only
  let current := (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement, parameter)
  let reciprocal : Boundary → Real := fun point => frameFreeBoundaryArctanDerivativeEvaluation period hPeriod current point
  let first : Boundary → Real := fun point => normalBoundaryC2ScaledRawSpatialFirst period hPeriod inner current point
  let vector := (frame).vectorAt boundary outer
  have hProduct := congrArg (fun derivative => derivative vector)
    (mvfderiv_mul
      ((frameFreeBoundaryArctanDerivativeEvaluation_smooth_contMDiff period hPeriod displacement parameter).mdifferentiableAt (by simp))
      ((frameFreeBoundaryRawSpatialFirst_smooth_contMDiff period hPeriod displacement parameter inner).mdifferentiableAt (by simp)))
  have hProductApply : mvfderiv throatCoverModelWithCorners (reciprocal * first) boundary vector =
      reciprocal boundary * mvfderiv throatCoverModelWithCorners first boundary vector +
        first boundary * mvfderiv throatCoverModelWithCorners reciprocal boundary vector := by
    simpa only [add_apply, smul_apply, smul_eq_mul] using hProduct
  change _ = mvfderiv throatCoverModelWithCorners (reciprocal * first) boundary vector
  rw [hProductApply]
  have hFirst := candidateANormalBoundaryC2ScaledRawSpatialSecond_smooth period hPeriod displacement parameter boundary outer inner
  have hReciprocal := reciprocalDerivative_smooth period hPeriod displacement parameter boundary outer
  dsimp only at hReciprocal
  change mvfderiv throatCoverModelWithCorners reciprocal boundary vector = _ at hReciprocal
  change _ = mvfderiv throatCoverModelWithCorners first boundary vector at hFirst
  rw [← hFirst, hReciprocal]
  simp only [frameFreeBoundaryLatitudeSpatialSecond, BoundedContinuousFunction.sub_apply,
    BoundedContinuousFunction.mul_apply, BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.pow_apply, smul_eq_mul, reciprocal, first]
  ring

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryLatitudeSpatialJets4D
