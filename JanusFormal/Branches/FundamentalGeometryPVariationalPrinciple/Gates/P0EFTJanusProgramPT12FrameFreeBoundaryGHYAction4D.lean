import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryMeanCurvatureSmooth4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryInducedVolume4D

/-! Joint C² extension of the unchanged mobile two-sheet GHY action near the
intrinsic base. Integration uses the existing fixed first-sheet measure; the
factor two is the historical oriented second-sheet identity. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryGHYAction4D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff Topology BoundedContinuousFunction
open MeasureTheory
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusCanonicalPhysicalH1TraceBound4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusCutBoundaryFirstSheetCurrentBridge4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedDomain4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedVolume4D
open P0EFTJanusProgramPT12FrameFreeBoundarySecondForm4D
open P0EFTJanusProgramPT12FrameFreeBoundaryMeanCurvatureSmooth4D

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
local instance : ChartedSpace ThroatCoverModel (MappingTorus (fixedEquatorData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω (MappingTorus (fixedEquatorData period hPeriod)) :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.effectiveThroatIsManifold period hPeriod
local instance : NormedAddCommGroup (NormalBoundaryC2JetCore period hPeriod) :=
  (normalBoundaryC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (NormalBoundaryC2JetCore period hPeriod) :=
  Submodule.normedSpace (normalBoundaryC2JetCoreSubmodule period hPeriod)
local instance : NormedAddCommGroup (CanonicalPhysicalScalarC2JetCore period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup
local instance : NormedSpace Real (CanonicalPhysicalScalarC2JetCore period hPeriod) := inferInstance
local instance : MeasurableSpace Boundary := borel _
local instance : BorelSpace Boundary where measurable_eq := rfl
local notation "baseMetric" => P0EFTJanusProgramPGlobalCandidateAGeometry4D.GlobalCandidateAGeometry.plusMetric
  (intrinsicBulkGeometry period hPeriod)
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "Input" => FrameFreeBoundaryJointCore period hPeriod frame baseMetric × Real
local notation "Field" => BoundedContinuousFunction Boundary Real

def frameFreeBoundaryGHYDomain : Set Input :=
  frameFreeBoundarySecondFormDomain period hPeriod ∩ frameFreeBoundaryInducedVolumeDomain period hPeriod

theorem frameFreeBoundaryGHYDomain_isOpen : IsOpen (frameFreeBoundaryGHYDomain period hPeriod) :=
  (frameFreeBoundarySecondFormDomain_isOpen period hPeriod).inter
    (frameFreeBoundaryInducedVolumeDomain_isOpen period hPeriod)

theorem zero_mem_frameFreeBoundaryGHYDomain : (0 : Input) ∈ frameFreeBoundaryGHYDomain period hPeriod :=
  ⟨zero_joint_mem_frameFreeBoundarySecondFormDomain period hPeriod 0,
    zero_mem_frameFreeBoundaryInducedVolumeDomain period hPeriod⟩

/-- Increasing first-sheet orientation, with the original Einstein coupling. -/
def frameFreeBoundaryGHYIntegrand (einsteinScale : Real) (current : Input) : Field :=
  einsteinScale • (frameFreeBoundaryInducedVolume period hPeriod current *
    frameFreeBoundaryMeanCurvatureEvaluation period hPeriod current)

theorem frameFreeBoundaryGHYIntegrand_contDiffOn_two (einsteinScale : Real) :
    ContDiffOn Real 2 (frameFreeBoundaryGHYIntegrand period hPeriod einsteinScale)
      (frameFreeBoundaryGHYDomain period hPeriod) := by
  exact ContDiffOn.const_smul einsteinScale
    (((frameFreeBoundaryInducedVolume_contDiffOn_two period hPeriod).mono (fun _ h => h.2)).mul
      ((frameFreeBoundaryMeanCurvatureEvaluation_contDiffOn_two period hPeriod).mono (fun _ h => h.1)))

def frameFreeBoundaryFirstSheetGHYAction (einsteinScale : Real) (current : Input) : Real :=
  candidateANormalBoundaryFirstSheetIntegralCLM period hPeriod
    (frameFreeBoundaryGHYIntegrand period hPeriod einsteinScale current)

theorem frameFreeBoundaryFirstSheetGHYAction_eq_integral (einsteinScale : Real) (current : Input) :
    frameFreeBoundaryFirstSheetGHYAction period hPeriod einsteinScale current =
      ∫ base, frameFreeBoundaryGHYIntegrand period hPeriod einsteinScale current
        (canonicalLatitudeCutBoundaryFirstLift period hPeriod base) ∂canonicalLatitudeBaseMeasure period := by
  rw [frameFreeBoundaryFirstSheetGHYAction, candidateANormalBoundaryFirstSheetIntegralCLM_apply]
  unfold candidateANormalBoundaryFirstSheetMeasure
  rw [integral_map
    (continuous_canonicalLatitudeCutBoundaryFirstLift period hPeriod |>.measurable.aemeasurable)
    (frameFreeBoundaryGHYIntegrand period hPeriod einsteinScale current).continuous.aestronglyMeasurable]

theorem frameFreeBoundaryFirstSheetGHYAction_contDiffOn_two (einsteinScale : Real) :
    ContDiffOn Real 2 (frameFreeBoundaryFirstSheetGHYAction period hPeriod einsteinScale)
      (frameFreeBoundaryGHYDomain period hPeriod) :=
  (candidateANormalBoundaryFirstSheetIntegralCLM period hPeriod).contDiff.contDiffOn.comp
    (frameFreeBoundaryGHYIntegrand_contDiffOn_two period hPeriod einsteinScale)
    (fun _ _ => Set.mem_univ _)

/-- The unchanged two oriented sheets, using their proved equal contributions. -/
def frameFreeBoundaryTwoSheetGHYAction (einsteinScale : Real) (current : Input) : Real :=
  2 * frameFreeBoundaryFirstSheetGHYAction period hPeriod einsteinScale current

theorem frameFreeBoundaryTwoSheetGHYAction_contDiffOn_two (einsteinScale : Real) :
    ContDiffOn Real 2 (frameFreeBoundaryTwoSheetGHYAction period hPeriod einsteinScale)
      (frameFreeBoundaryGHYDomain period hPeriod) :=
  contDiffOn_const.mul (frameFreeBoundaryFirstSheetGHYAction_contDiffOn_two period hPeriod einsteinScale)

theorem frameFreeBoundaryGHYIntegrand_smooth
    (einsteinScale : Real) (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor =
      (P0EFTJanusProgramPGlobalCandidateAGeometry4D.GlobalCandidateAGeometry.plusMetric
        (intrinsicBulkGeometry period hPeriod)).tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)
    (hCurrent : (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter) ∈
      frameFreeBoundaryGHYDomain period hPeriod) (boundary : Boundary) :
    let hNonNull := normalGraphNonNullAt_of_frameFreeBoundaryInducedDomain period hPeriod baseMetric tensor
      variedMetric hVaried displacement parameter hCurrent.1.1.1
    frameFreeBoundaryGHYIntegrand period hPeriod einsteinScale
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter) boundary =
    normalGraphCanonicalInducedGaussGHYIntegrand period hPeriod einsteinScale variedMetric
      displacement parameter hNonNull boundary .increasing := by
  dsimp only
  let point := normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)
  have hMean := frameFreeBoundaryMeanCurvatureEvaluation_smooth_eq_gauss period hPeriod tensor variedMetric hVaried
    displacement parameter hCurrent.1 boundary (normalGraphCanonicalSelectedHolonomicPatchAt period hPeriod point)
      (normalGraphCanonicalSelectedHolonomicCoordinateAt period hPeriod point)
      (normalGraphCanonicalSelectedHolonomicPatchAt_map period hPeriod point)
  simp only [frameFreeBoundaryGHYIntegrand, BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.mul_apply, smul_eq_mul,
    frameFreeBoundaryInducedVolume_smooth period hPeriod tensor variedMetric hVaried displacement parameter hCurrent.2,
    hMean, normalGraphCanonicalInducedGaussGHYIntegrand,
    P0EFTJanusGaussianNormalEmbeddedHypersurface.NormalOrientation.sign]
  ring

theorem frameFreeBoundaryFirstSheetGHYAction_smooth
    (einsteinScale : Real) (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor =
      (P0EFTJanusProgramPGlobalCandidateAGeometry4D.GlobalCandidateAGeometry.plusMetric
        (intrinsicBulkGeometry period hPeriod)).tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)
    (hCurrent : (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter) ∈
      frameFreeBoundaryGHYDomain period hPeriod) :
    let hNonNull := normalGraphNonNullAt_of_frameFreeBoundaryInducedDomain period hPeriod baseMetric tensor
      variedMetric hVaried displacement parameter hCurrent.1.1.1
    frameFreeBoundaryFirstSheetGHYAction period hPeriod einsteinScale
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter) =
    normalGraphCanonicalFirstSheetGaussGHYAction period hPeriod einsteinScale variedMetric displacement parameter hNonNull := by
  dsimp only
  rw [frameFreeBoundaryFirstSheetGHYAction_eq_integral, normalGraphCanonicalFirstSheetGaussGHYAction]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun base => frameFreeBoundaryGHYIntegrand_smooth period hPeriod
    einsteinScale tensor variedMetric hVaried displacement parameter hCurrent
      (canonicalLatitudeCutBoundaryFirstLift period hPeriod base)

/-- Exact agreement with the native action, including its orientation and
two-sheet factor. The Einstein coupling remains arbitrary. -/
theorem frameFreeBoundaryTwoSheetGHYAction_smooth
    (einsteinScale : Real) (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor =
      (P0EFTJanusProgramPGlobalCandidateAGeometry4D.GlobalCandidateAGeometry.plusMetric
        (intrinsicBulkGeometry period hPeriod)).tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)
    (hCurrent : (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter) ∈
      frameFreeBoundaryGHYDomain period hPeriod) :
    let hNonNull := normalGraphNonNullAt_of_frameFreeBoundaryInducedDomain period hPeriod baseMetric tensor
      variedMetric hVaried displacement parameter hCurrent.1.1.1
    frameFreeBoundaryTwoSheetGHYAction period hPeriod einsteinScale
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter) =
    normalGraphCanonicalTwoSheetGaussGHYAction period hPeriod einsteinScale variedMetric displacement parameter hNonNull := by
  dsimp only
  rw [frameFreeBoundaryTwoSheetGHYAction, normalGraphCanonicalTwoSheetGaussGHYAction_eq_two_mul_first]
  exact congrArg (fun value : Real => 2 * value)
    (frameFreeBoundaryFirstSheetGHYAction_smooth period hPeriod einsteinScale tensor variedMetric hVaried
      displacement parameter hCurrent)

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryGHYAction4D
