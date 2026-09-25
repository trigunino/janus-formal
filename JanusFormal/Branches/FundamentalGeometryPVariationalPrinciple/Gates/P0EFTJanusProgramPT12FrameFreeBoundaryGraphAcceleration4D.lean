import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryGraphTangentDerivative4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryConnectionSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryProjectedNormal4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12MovingFrameAccelerationCalculus4D

/-! Genuine finite-frame graph acceleration. Its smooth reconstruction uses
the local Levi-Civita derivative of the moving ambient generators. It is not
identified with the fixed-source-coordinate Hessian. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryGraphAcceleration4D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff BigOperators BoundedContinuousFunction
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusH1GraphTrace4D P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusFiniteFrameKoszulCoefficients4D P0EFTJanusFiniteFrameCovariantTensorDivergence4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetric4D
open P0EFTJanusProgramPT12FrameFreeBoundaryGraphTangentDerivative4D
open P0EFTJanusProgramPT12FrameFreeBoundaryAmbientInverse4D
open P0EFTJanusProgramPT12FrameFreeBoundaryConnectionEvaluation4D
open P0EFTJanusProgramPT12FrameFreeBoundaryConnectionSmooth4D
open P0EFTJanusProgramPT12FrameFreeBoundaryProjectedNormal4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedDomain4D
open P0EFTJanusProgramPT12MovingFrameAccelerationCalculus4D

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

variable (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "Index" => BoundaryMetricJetIndex period hPeriod
local notation "TangentIndex" => NormalBoundaryTangentIndex period hPeriod
local notation "Input" => FrameFreeBoundaryJointCore period hPeriod frame metric × Real
local notation "Field" => BoundedContinuousFunction Boundary Real

def frameFreeBoundaryGraphAccelerationEvaluation (outer inner : TangentIndex) (upper : Index)
    (current : Input) : Field :=
  frameFreeBoundaryGraphTangentDerivativeEvaluation period hPeriod metric outer inner upper current +
    ∑ first : Index, ∑ second : Index,
      frameFreeBoundaryConnectionEvaluation period hPeriod metric upper first second current *
        frameFreeBoundaryGraphTangentEvaluation period hPeriod metric outer first current *
        frameFreeBoundaryGraphTangentEvaluation period hPeriod metric inner second current

theorem frameFreeBoundaryGraphAccelerationEvaluation_contDiffOn_two
    (outer inner : TangentIndex) (upper : Index) :
    ContDiffOn Real 2 (frameFreeBoundaryGraphAccelerationEvaluation period hPeriod metric outer inner upper)
      (frameFreeBoundaryAmbientDomain period hPeriod metric) := by
  apply (frameFreeBoundaryGraphTangentDerivativeEvaluation_contDiff_two
    period hPeriod metric outer inner upper).contDiffOn.add
  apply ContDiffOn.sum
  intro first _
  apply ContDiffOn.sum
  intro second _
  exact ((frameFreeBoundaryConnectionEvaluation_contDiffOn_two period hPeriod metric upper first second).mul
    (frameFreeBoundaryGraphTangentEvaluation_contDiff_two period hPeriod metric outer first).contDiffOn).mul
    (frameFreeBoundaryGraphTangentEvaluation_contDiff_two period hPeriod metric inner second).contDiffOn

variable (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
  (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
  (hVaried : variedMetric.tensor = metric.tensor + tensor)
  (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)

include hVaried in
theorem frameFreeBoundaryGraphAccelerationEvaluation_smooth
    (hCurrent : (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) ∈
      frameFreeBoundaryAmbientDomain period hPeriod metric)
    (outer inner : TangentIndex) (upper : Index) (boundary : Boundary) :
    let current := (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter)
    frameFreeBoundaryGraphAccelerationEvaluation period hPeriod metric outer inner upper current boundary =
      mvfderiv throatCoverModelWithCorners
        (fun point => frameFreeBoundaryGraphTangentEvaluation period hPeriod metric inner upper current point)
        boundary ((finiteSmoothThroatGeneratingFrame (doubledPeriod period)
          (doubledPeriod_ne_zero period hPeriod)).vectorAt boundary outer) +
      ∑ first : Index, ∑ second : Index,
        finiteFrameKoszulChristoffelCoefficient period hPeriod frame metric variedMetric upper first second
          (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) *
        frameFreeBoundaryGraphTangentEvaluation period hPeriod metric outer first current boundary *
        frameFreeBoundaryGraphTangentEvaluation period hPeriod metric inner second current boundary := by
  dsimp only
  have hDerivative := frameFreeBoundaryGraphTangentDerivativeEvaluation_smooth period hPeriod metric
    (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement)).1
    displacement parameter boundary outer inner upper
  have hConnection := frameFreeBoundaryConnectionEvaluation_smooth period hPeriod metric tensor
    variedMetric hVaried displacement parameter hCurrent
  simp only [frameFreeBoundaryGraphAccelerationEvaluation, BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.mul_apply, hConnection]
  simpa only [smoothToFrameFreeBoundaryJointCore, LinearMap.prodMap_apply] using
    congrArg (fun value : Real => value + ∑ first : Index, ∑ second : Index,
      finiteFrameKoszulChristoffelCoefficient period hPeriod frame metric variedMetric upper first second
        (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) *
      frameFreeBoundaryGraphTangentEvaluation period hPeriod metric outer first
        (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) boundary *
      frameFreeBoundaryGraphTangentEvaluation period hPeriod metric inner second
        (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) boundary)
      hDerivative

include hVaried in
/-- Exact reconstruction in any genuine ambient holonomic chart. The source
generator remains variable in the coefficient derivative. -/
theorem frameFreeBoundaryGraphAccelerationEvaluation_smooth_reconstructs_local
    (hCurrent : (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) ∈
      frameFreeBoundaryAmbientDomain period hPeriod metric)
    (outer inner : TangentIndex) (boundary : Boundary)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Fin 4 → Real)
    (hAt : patch.coordinateMap coordinate = normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) :
    let current := (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter)
    (∑ upper : Index,
      frameFreeBoundaryGraphAccelerationEvaluation period hPeriod metric outer inner upper current boundary •
        finiteFramePulledVector period hPeriod frame patch upper coordinate) =
      (∑ upper : Index, mvfderiv throatCoverModelWithCorners
        (fun point => frameFreeBoundaryGraphTangentEvaluation period hPeriod metric inner upper current point)
        boundary ((finiteSmoothThroatGeneratingFrame (doubledPeriod period)
          (doubledPeriod_ne_zero period hPeriod)).vectorAt boundary outer) •
        finiteFramePulledVector period hPeriod frame patch upper coordinate) +
      ∑ first : Index, ∑ second : Index,
        (frameFreeBoundaryGraphTangentEvaluation period hPeriod metric outer first current boundary *
          frameFreeBoundaryGraphTangentEvaluation period hPeriod metric inner second current boundary) •
        finiteFrameLocalCovariantDerivativeVector period hPeriod frame variedMetric patch coordinate first second := by
  dsimp only
  have hLocal (upper first second : Index) :
      finiteFrameKoszulChristoffelCoefficient period hPeriod frame metric variedMetric upper first second
        (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) =
      finiteFrameTensorChristoffelCoefficient period hPeriod frame metric variedMetric patch coordinate upper first second := by
    rw [← hAt]
    exact finiteFrameKoszulChristoffelCoefficient_eq_local period hPeriod frame metric variedMetric patch coordinate upper first second
  simp_rw [frameFreeBoundaryGraphAccelerationEvaluation_smooth period hPeriod metric tensor
    variedMetric hVaried displacement parameter hCurrent, hLocal]
  rw [movingFrameAcceleration_rearrange]
  simp_rw [← finiteFrameLocalCovariantDerivativeVector_reconstructs period hPeriod frame metric variedMetric patch coordinate]

include hVaried in
/-- The true projected normal removes the source-generator correction. -/
theorem frameFreeBoundaryGraphAcceleration_normal_tangent_correction
    (hCurrent : (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) ∈
      frameFreeBoundaryInducedDomain period hPeriod metric)
    (boundary : Boundary) (sourceCorrection : TangentSpace throatCoverModelWithCorners boundary)
    (acceleration : TangentSpace coverModelWithCorners
      (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter))) :
    -variedMetric.tensor.tensor (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter))
      (frameFreeBoundaryProjectedNormalVector period hPeriod metric tensor displacement parameter boundary)
      (acceleration + mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fun point : Boundary => normalGraphOrientationDouble period hPeriod displacement (point, parameter))
        boundary sourceCorrection) =
    -variedMetric.tensor.tensor (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter))
      (frameFreeBoundaryProjectedNormalVector period hPeriod metric tensor displacement parameter boundary)
      acceleration := by
  rw [map_add, frameFreeBoundaryProjectedNormalVector_smooth_orthogonal period hPeriod metric
    tensor displacement parameter variedMetric hVaried hCurrent boundary sourceCorrection, add_zero]

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryGraphAcceleration4D
