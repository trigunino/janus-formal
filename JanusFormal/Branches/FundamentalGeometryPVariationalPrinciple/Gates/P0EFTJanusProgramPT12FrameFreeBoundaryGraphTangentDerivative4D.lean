import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryLatitudeSpatialJets4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetricSmooth4D

/-! Ordered throat derivatives of the actual graph-tangent coefficients.
The source generators vary with the boundary point. This is not an assertion
that these coefficients are a fixed-coordinate acceleration. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryGraphTangentDerivative4D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff BoundedContinuousFunction
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPT12FrameFreeBoundaryC3Core4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryTangentCoefficients4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetric4D
open P0EFTJanusProgramPT12FrameFreeBoundaryLatitudeSpatialJets4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Q := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (Q period hPeriod) := reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (Q period hPeriod) := reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (Q period hPeriod) := reflectedSphereQuotientCompactSpace period hPeriod
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
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance
local notation "NormalInput" => NormalBoundaryC2JetCore period hPeriod × Real
local notation "TangentIndex" => NormalBoundaryTangentIndex period hPeriod
local notation "Field" => BoundedContinuousFunction Boundary Real
local notation "CollarModel" => throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)
local notation "throatFrame" => finiteSmoothThroatGeneratingFrame
  (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)

def frameFreeBoundaryCollarSpatialDerivativeEvaluation (outer : TangentIndex)
    (field : Boundary × Real → Real)
    (hField : ContMDiff CollarModel (modelWithCornersSelf Real Real) ∞ field)
    (current : NormalInput) : Field :=
  normalBoundarySmoothFiberEvaluation period hPeriod
      (normalBoundaryHorizontalFieldDerivative period hPeriod outer field)
      (normalBoundaryHorizontalFieldDerivative_contMDiff period hPeriod outer field hField) current +
    frameFreeBoundaryLatitudeSpatialFirst period hPeriod outer current *
      normalBoundarySmoothFiberEvaluation period hPeriod
        (normalBoundaryLatitudeFieldDerivative period hPeriod field)
        (normalBoundaryLatitudeFieldDerivative_contMDiff period hPeriod field hField) current

theorem frameFreeBoundaryCollarSpatialDerivativeEvaluation_contDiff_two (outer : TangentIndex)
    (field : Boundary × Real → Real)
    (hField : ContMDiff CollarModel (modelWithCornersSelf Real Real) ∞ field) :
    ContDiff Real 2 (frameFreeBoundaryCollarSpatialDerivativeEvaluation period hPeriod outer field hField) :=
  (normalBoundarySmoothFiberEvaluation_contDiff_two period hPeriod _ _).add
    ((frameFreeBoundaryLatitudeSpatialFirst_contDiff_two period hPeriod outer).mul
      (normalBoundarySmoothFiberEvaluation_contDiff_two period hPeriod _ _))

theorem frameFreeBoundaryCollarSpatialDerivativeEvaluation_smooth (outer : TangentIndex)
    (field : Boundary × Real → Real)
    (hField : ContMDiff CollarModel (modelWithCornersSelf Real Real) ∞ field)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real) (boundary : Boundary) :
    let current := (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement, parameter)
    frameFreeBoundaryCollarSpatialDerivativeEvaluation period hPeriod outer field hField current boundary =
      mvfderiv throatCoverModelWithCorners
        (fun point : Boundary => normalBoundarySmoothFiberEvaluation period hPeriod field hField current point)
        boundary ((throatFrame).vectorAt boundary outer) := by
  dsimp only
  let latitude : Boundary → Real := fun point =>
    Real.arctan (parameter * normalDisplacementOrientationScalar period hPeriod displacement point)
  have hLatitude : ContMDiff throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞ latitude :=
    Real.contDiff_arctan.contMDiff.comp
      (contMDiff_const.mul (normalDisplacementOrientationScalar_contMDiff period hPeriod displacement))
  have hFunction : (fun point : Boundary => normalBoundarySmoothFiberEvaluation period hPeriod field hField
      (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement, parameter) point) =
      fun point => field (point, latitude point) :=
    funext (frameFreeBoundarySmoothFiberEvaluation_smooth_apply period hPeriod field hField displacement parameter)
  rw [hFunction]
  have hChain := candidateANormalBoundarySmoothCollarField_mvfderiv_graph
    period hPeriod field hField latitude hLatitude boundary outer
  dsimp only at hChain
  rw [← candidateANormalBoundary_mvfderiv_real_eq_mfderiv period hPeriod
    (fun point : Boundary => field (point, latitude point)) boundary ((throatFrame).vectorAt boundary outer)] at hChain
  rw [← frameFreeBoundaryLatitudeSpatialFirst_smooth period hPeriod displacement parameter boundary outer] at hChain
  simpa only [frameFreeBoundaryCollarSpatialDerivativeEvaluation, BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.mul_apply, frameFreeBoundarySmoothFiberEvaluation_smooth_apply,
    smul_eq_mul, latitude] using hChain.symm

private theorem scalar_add_mul_derivative (a b c : Boundary → Real)
    (ha : ContMDiff throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞ a)
    (hb : ContMDiff throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞ b)
    (hc : ContMDiff throatCoverModelWithCorners (modelWithCornersSelf Real Real) ∞ c)
    (point : Boundary) (vector : TangentSpace throatCoverModelWithCorners point) :
    mvfderiv throatCoverModelWithCorners (a + b * c) point vector =
      mvfderiv throatCoverModelWithCorners a point vector +
        mvfderiv throatCoverModelWithCorners b point vector * c point +
        b point * mvfderiv throatCoverModelWithCorners c point vector := by
  rw [mvfderiv_add (ha.mdifferentiableAt (by simp)) ((hb.mul hc).mdifferentiableAt (by simp)),
    mvfderiv_mul (hb.mdifferentiableAt (by simp)) (hc.mdifferentiableAt (by simp))]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

variable (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "Index" => BoundaryMetricJetIndex period hPeriod
local notation "Input" => FrameFreeBoundaryJointCore period hPeriod frame metric × Real

def frameFreeBoundaryGraphTangentDerivativeEvaluation (outer inner : TangentIndex) (row : Index)
    (current : Input) : Field :=
  let normal := frameFreeBoundaryNormalInput period hPeriod metric current
  frameFreeBoundaryCollarSpatialDerivativeEvaluation period hPeriod outer
      (frameFreeBoundaryHorizontalCoefficient period hPeriod frame metric inner row)
      (frameFreeBoundaryHorizontalCoefficient_contMDiff period hPeriod frame metric inner row) normal +
    frameFreeBoundaryLatitudeSpatialSecond period hPeriod outer inner normal *
      frameFreeBoundaryVerticalCoefficientEvaluation period hPeriod frame metric row normal +
    frameFreeBoundaryLatitudeSpatialFirst period hPeriod inner normal *
      frameFreeBoundaryCollarSpatialDerivativeEvaluation period hPeriod outer
        (frameFreeBoundaryVerticalCoefficient period hPeriod frame metric row)
        (frameFreeBoundaryVerticalCoefficient_contMDiff period hPeriod frame metric row) normal

theorem frameFreeBoundaryGraphTangentDerivativeEvaluation_contDiff_two
    (outer inner : TangentIndex) (row : Index) :
    ContDiff Real 2 (frameFreeBoundaryGraphTangentDerivativeEvaluation period hPeriod metric outer inner row) := by
  have hInput := frameFreeBoundaryNormalInput_contDiff_two period hPeriod metric
  exact (((frameFreeBoundaryCollarSpatialDerivativeEvaluation_contDiff_two period hPeriod outer
      _ (frameFreeBoundaryHorizontalCoefficient_contMDiff period hPeriod frame metric inner row)).comp hInput).add
    (((frameFreeBoundaryLatitudeSpatialSecond_contDiff_two period hPeriod outer inner).comp hInput).mul
      ((frameFreeBoundaryVerticalCoefficientEvaluation_contDiff_two period hPeriod frame metric row).comp hInput))).add
    (((frameFreeBoundaryLatitudeSpatialFirst_contDiff_two period hPeriod inner).comp hInput).mul
      ((frameFreeBoundaryCollarSpatialDerivativeEvaluation_contDiff_two period hPeriod outer
        _ (frameFreeBoundaryVerticalCoefficient_contMDiff period hPeriod frame metric row)).comp hInput))

/-- Exact derivative of the coefficients that reconstruct the genuine graph tangent.
The metric completion may be arbitrary: graph tangents depend on its normal component. -/
theorem frameFreeBoundaryGraphTangentDerivativeEvaluation_smooth
    (variation : FrameFreeBoundaryC3Core period hPeriod frame metric)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real) (boundary : Boundary)
    (outer inner : TangentIndex) (row : Index) :
    let current := ((variation, smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement), parameter)
    frameFreeBoundaryGraphTangentDerivativeEvaluation period hPeriod metric outer inner row current boundary =
      mvfderiv throatCoverModelWithCorners
        (fun point : Boundary => frameFreeBoundaryGraphTangentEvaluation period hPeriod metric inner row current point)
        boundary ((throatFrame).vectorAt boundary outer) := by
  dsimp only
  let normal := (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement, parameter)
  let horizontal := frameFreeBoundaryHorizontalCoefficient period hPeriod frame metric inner row
  let vertical := frameFreeBoundaryVerticalCoefficient period hPeriod frame metric row
  have hHorizontal := frameFreeBoundaryHorizontalCoefficient_contMDiff period hPeriod frame metric inner row
  have hVertical := frameFreeBoundaryVerticalCoefficient_contMDiff period hPeriod frame metric row
  let a : Boundary → Real := fun point => normalBoundarySmoothFiberEvaluation period hPeriod horizontal hHorizontal normal point
  let b : Boundary → Real := fun point => frameFreeBoundaryLatitudeSpatialFirst period hPeriod inner normal point
  let c : Boundary → Real := fun point => normalBoundarySmoothFiberEvaluation period hPeriod vertical hVertical normal point
  have ha := frameFreeBoundarySmoothFiberEvaluation_smooth_contMDiff period hPeriod horizontal hHorizontal displacement parameter
  have hb := frameFreeBoundaryLatitudeSpatialFirst_smooth_contMDiff period hPeriod displacement parameter inner
  have hc := frameFreeBoundarySmoothFiberEvaluation_smooth_contMDiff period hPeriod vertical hVertical displacement parameter
  have hDerivative := scalar_add_mul_derivative period hPeriod a b c ha hb hc boundary ((throatFrame).vectorAt boundary outer)
  have hA := frameFreeBoundaryCollarSpatialDerivativeEvaluation_smooth period hPeriod outer
    horizontal hHorizontal displacement parameter boundary
  have hB := frameFreeBoundaryLatitudeSpatialSecond_smooth period hPeriod displacement parameter boundary outer inner
  have hC := frameFreeBoundaryCollarSpatialDerivativeEvaluation_smooth period hPeriod outer
    vertical hVertical displacement parameter boundary
  dsimp only at hA hB hC
  change _ = mvfderiv throatCoverModelWithCorners a boundary ((throatFrame).vectorAt boundary outer) at hA
  change _ = mvfderiv throatCoverModelWithCorners b boundary ((throatFrame).vectorAt boundary outer) at hB
  change _ = mvfderiv throatCoverModelWithCorners c boundary ((throatFrame).vectorAt boundary outer) at hC
  rw [← hA, ← hB, ← hC] at hDerivative
  change _ = mvfderiv throatCoverModelWithCorners (a + b * c) boundary ((throatFrame).vectorAt boundary outer)
  simpa only [frameFreeBoundaryGraphTangentDerivativeEvaluation, frameFreeBoundaryNormalInput,
    BoundedContinuousFunction.add_apply, BoundedContinuousFunction.mul_apply,
    frameFreeBoundaryVerticalCoefficientEvaluation, a, b, c, horizontal, vertical, normal] using hDerivative.symm

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryGraphTangentDerivative4D
