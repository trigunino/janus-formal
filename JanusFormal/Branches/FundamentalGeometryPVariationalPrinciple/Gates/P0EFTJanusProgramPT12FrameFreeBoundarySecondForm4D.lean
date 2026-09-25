import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryUnitNormal4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryHistoricalAcceleration4D

/-! C² second-form coefficients from the true positive unit normal and graph
acceleration. The symmetric form agrees with the unchanged historical Gauss
form. Its finite trace uses the faithful induced inverse lift. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundarySecondForm4D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff Topology BigOperators BoundedContinuousFunction
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusFiniteFrameCovariantTensorDivergence4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetric4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetricSmooth4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedDomain4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedInverse4D
open P0EFTJanusProgramPT12FrameFreeBoundaryAmbientInverse4D
open P0EFTJanusProgramPT12FrameFreeBoundaryUnitNormal4D
open P0EFTJanusProgramPT12FrameFreeBoundaryGraphAcceleration4D
open P0EFTJanusProgramPT12FrameFreeBoundaryHistoricalAcceleration4D

private theorem finiteBilinearPairing {I E : Type*} [Fintype I]
    [AddCommGroup E] [Module Real E] [TopologicalSpace E]
    (pairing : E →L[Real] E →L[Real] Real) (vectors : I → E) (first second : I → Real) :
    (∑ i : I, ∑ j : I, first i * pairing (vectors i) (vectors j) * second j) =
      pairing (∑ i : I, first i • vectors i) (∑ j : I, second j • vectors j) := by
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

private theorem dependentPairing_heq {X : Type*} (E : X → Type*)
    (pairing : ∀ x, E x → E x → Real) {x y : X} (h : x = y)
    {u v : E x} {u' v' : E y} (hu : HEq u u') (hv : HEq v v') :
    pairing x u v = pairing y u' v' := by
  cases h
  cases hu
  cases hv
  rfl

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
local notation "baseMetric" => P0EFTJanusProgramPGlobalCandidateAGeometry4D.GlobalCandidateAGeometry.plusMetric
  (intrinsicBulkGeometry period hPeriod)
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "throatFrame" => finiteSmoothThroatGeneratingFrame
  (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
local notation "Index" => BoundaryMetricJetIndex period hPeriod
local notation "TangentIndex" => NormalBoundaryTangentIndex period hPeriod
local notation "Input" => FrameFreeBoundaryJointCore period hPeriod frame baseMetric × Real
local notation "Field" => BoundedContinuousFunction Boundary Real
local notation "MatrixField" => CandidateANormalBoundaryInducedMetricMatrixField period hPeriod
@[reducible] local instance : NormedAddCommGroup MatrixField := Pi.normedAddCommGroup
@[reducible] local instance : NormedSpace Real MatrixField := Pi.normedSpace

def frameFreeBoundarySecondFormDomain : Set Input :=
  frameFreeBoundaryUnitNormalDomain period hPeriod ∩ frameFreeBoundaryAmbientDomain period hPeriod baseMetric

theorem frameFreeBoundarySecondFormDomain_isOpen : IsOpen (frameFreeBoundarySecondFormDomain period hPeriod) :=
  (frameFreeBoundaryUnitNormalDomain_isOpen period hPeriod).inter
    (frameFreeBoundaryAmbientDomain_isOpen period hPeriod baseMetric)

theorem zero_joint_mem_frameFreeBoundarySecondFormDomain (parameter : Real) :
    ((0, parameter) : Input) ∈ frameFreeBoundarySecondFormDomain period hPeriod :=
  ⟨zero_joint_mem_frameFreeBoundaryUnitNormalDomain period hPeriod parameter,
    zero_mem_frameFreeBoundaryAmbientDomain period hPeriod baseMetric parameter⟩

def frameFreeBoundaryRawSecondFormEvaluation (outer inner : TangentIndex) (current : Input) : Field :=
  -(∑ first : Index, ∑ second : Index,
    frameFreeBoundaryUnitNormalEvaluation period hPeriod first current *
      frameFreeBoundaryActualMetricEvaluation period hPeriod baseMetric first second current *
      frameFreeBoundaryGraphAccelerationEvaluation period hPeriod baseMetric outer inner second current)

theorem frameFreeBoundaryRawSecondFormEvaluation_contDiffOn_two (outer inner : TangentIndex) :
    ContDiffOn Real 2 (frameFreeBoundaryRawSecondFormEvaluation period hPeriod outer inner)
      (frameFreeBoundarySecondFormDomain period hPeriod) := by
  unfold frameFreeBoundaryRawSecondFormEvaluation
  apply ContDiffOn.neg
  exact ContDiffOn.sum fun first _ => ContDiffOn.sum fun second _ =>
    (((frameFreeBoundaryUnitNormalEvaluation_contDiffOn_two period hPeriod first).mono Set.inter_subset_left).mul
      (frameFreeBoundaryActualMetricEvaluation_contDiff_two period hPeriod baseMetric first second).contDiffOn).mul
      ((frameFreeBoundaryGraphAccelerationEvaluation_contDiffOn_two period hPeriod baseMetric outer inner second).mono
        Set.inter_subset_right)

def frameFreeBoundarySecondFormEvaluation (outer inner : TangentIndex) (current : Input) : Field :=
  (1 / 2 : Real) • (frameFreeBoundaryRawSecondFormEvaluation period hPeriod outer inner current +
    frameFreeBoundaryRawSecondFormEvaluation period hPeriod inner outer current)

theorem frameFreeBoundarySecondFormEvaluation_contDiffOn_two (outer inner : TangentIndex) :
    ContDiffOn Real 2 (frameFreeBoundarySecondFormEvaluation period hPeriod outer inner)
      (frameFreeBoundarySecondFormDomain period hPeriod) :=
  ContDiffOn.const_smul (1 / 2 : Real)
    ((frameFreeBoundaryRawSecondFormEvaluation_contDiffOn_two period hPeriod outer inner).add
      (frameFreeBoundaryRawSecondFormEvaluation_contDiffOn_two period hPeriod inner outer))

theorem frameFreeBoundarySecondFormEvaluation_symmetric (outer inner : TangentIndex) (current : Input) :
    frameFreeBoundarySecondFormEvaluation period hPeriod outer inner current =
      frameFreeBoundarySecondFormEvaluation period hPeriod inner outer current := by
  unfold frameFreeBoundarySecondFormEvaluation
  rw [add_comm]

/-- Chart transport only: this lemma is independent of the completed metric
core and of the nonlinear acceleration coefficients. -/
private theorem canonicalUnitNormal_finiteFramePairing
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : Boundary) (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : Fin 4 → Real)
    (hAt : patch.coordinateMap coordinate = normalGraphOrientationDouble period hPeriod displacement (boundary, parameter))
    (coefficients : Index → Real) :
    localMetricCoordinateForm period hPeriod metric patch coordinate
      (normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod metric
        displacement parameter hNonNull boundary patch coordinate hAt)
      (∑ row : Index, coefficients row • finiteFramePulledVector period hPeriod frame patch row coordinate) =
    metric.tensor.tensor (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter))
      (normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement parameter hNonNull boundary)
      (∑ row : Index, coefficients row • (frame).vectorAt
        (normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) row) := by
  let derivative : (Fin 4 → Real) →L[Real] CoverCoordinates :=
    mfderiv (modelWithCornersSelf Real (Fin 4 → Real)) coverModelWithCorners patch.coordinateMap coordinate
  have hNormal := (normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt_reconstructs period hPeriod
    metric displacement parameter hNonNull boundary patch coordinate hAt).heq.trans
      (eqRec_heq hAt.symm (normalGraphCanonicalMetricUnitNormal period hPeriod metric displacement parameter hNonNull boundary))
  have hPush (row : Index) : derivative (finiteFramePulledVector period hPeriod frame patch row coordinate) =
      (frame).vectorAt (patch.coordinateMap coordinate) row :=
    coordinateMap_mfderiv_finiteFramePulledVector period hPeriod frame patch coordinate row
  have hMap : derivative (∑ row : Index, coefficients row • finiteFramePulledVector period hPeriod frame patch row coordinate) =
      ∑ row : Index, coefficients row • (frame).vectorAt (patch.coordinateMap coordinate) row := by
    rw [map_sum]
    simp_rw [map_smul, hPush]
  have hTransport (x y : Q period hPeriod) (hxy : x = y) :
      HEq (∑ row : Index, coefficients row • (frame).vectorAt x row)
        (∑ row : Index, coefficients row • (frame).vectorAt y row) := by cases hxy; rfl
  rw [localMetricCoordinateForm_apply]
  exact dependentPairing_heq (fun p : Q period hPeriod => TangentSpace coverModelWithCorners p)
    (fun p first second => metric.tensor.tensor p first second) hAt hNormal
    (hMap.heq.trans (hTransport _ _ hAt))

variable (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
  (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
  (hVaried : variedMetric.tensor = (P0EFTJanusProgramPGlobalCandidateAGeometry4D.GlobalCandidateAGeometry.plusMetric (intrinsicBulkGeometry period hPeriod)).tensor + tensor)
  (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)

include hVaried in
theorem frameFreeBoundaryRawSecondFormEvaluation_smooth (boundary : Boundary) (outer inner : TangentIndex) :
    let current := (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter)
    let point := normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)
    frameFreeBoundaryRawSecondFormEvaluation period hPeriod outer inner current boundary =
      -variedMetric.tensor.tensor point (frameFreeBoundaryUnitNormalVector period hPeriod tensor displacement parameter boundary)
        (∑ row : Index, frameFreeBoundaryGraphAccelerationEvaluation period hPeriod baseMetric outer inner row current boundary •
          (finiteSmoothTangentFrame period hPeriod).vectorAt point row) := by
  dsimp only
  unfold frameFreeBoundaryRawSecondFormEvaluation frameFreeBoundaryUnitNormalVector
  simp only [BoundedContinuousFunction.neg_apply, BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.mul_apply]
  simp_rw [frameFreeBoundaryActualMetricEvaluation_smooth period hPeriod baseMetric tensor displacement parameter boundary,
    ← hVaried]
  exact congrArg Neg.neg (finiteBilinearPairing _ _ _ _)

include hVaried in
theorem frameFreeBoundaryRawSecondFormEvaluation_smooth_eq_gauss
    (hCurrent : (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter) ∈
      frameFreeBoundarySecondFormDomain period hPeriod)
    (boundary : Boundary) (outer inner : TangentIndex)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Fin 4 → Real)
    (hAt : patch.coordinateMap coordinate = normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) :
    let current := (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter)
    let hNonNull := normalGraphNonNullAt_of_frameFreeBoundaryInducedDomain period hPeriod baseMetric tensor
      variedMetric hVaried displacement parameter hCurrent.1.1
    frameFreeBoundaryRawSecondFormEvaluation period hPeriod outer inner current boundary =
      normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt period hPeriod variedMetric displacement
        parameter hNonNull boundary patch coordinate hAt
        (normalBoundaryOrientationTangentEquiv period hPeriod boundary ((throatFrame).vectorAt boundary outer))
        (normalBoundaryOrientationTangentEquiv period hPeriod boundary ((throatFrame).vectorAt boundary inner)) := by
  dsimp only
  let current := (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter)
  let coefficients := fun row : Index =>
    frameFreeBoundaryGraphAccelerationEvaluation period hPeriod baseMetric outer inner row current boundary
  let hNonNull := normalGraphNonNullAt_of_frameFreeBoundaryInducedDomain period hPeriod baseMetric tensor
    variedMetric hVaried displacement parameter hCurrent.1.1
  let point := normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)
  let acceleration : TangentSpace coverModelWithCorners point :=
    ∑ row : Index, coefficients row • (frame).vectorAt point row
  have hRaw := frameFreeBoundaryRawSecondFormEvaluation_smooth period hPeriod tensor variedMetric hVaried
    displacement parameter boundary outer inner
  have hNormal := frameFreeBoundaryUnitNormalVector_smooth period hPeriod tensor variedMetric hVaried
    displacement parameter hCurrent.1 boundary
  have hNormalPair := congrArg
    (fun normal : TangentSpace coverModelWithCorners point =>
      -variedMetric.tensor.tensor point normal acceleration) hNormal
  have hCoordinate := canonicalUnitNormal_finiteFramePairing period hPeriod variedMetric displacement
    parameter hNonNull boundary patch coordinate hAt coefficients
  have hLocal := congrArg Neg.neg hCoordinate.symm
  have hAcceleration := frameFreeBoundaryGraphAcceleration_normal_eq_gauss period hPeriod baseMetric
    tensor variedMetric hVaried displacement parameter hCurrent.2 hNonNull boundary outer inner patch coordinate hAt
  exact ((hRaw.trans hNormalPair).trans hLocal).trans hAcceleration

include hVaried in
theorem frameFreeBoundaryRawSecondFormEvaluation_smooth_eq_weingarten
    (hCurrent : (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter) ∈
      frameFreeBoundarySecondFormDomain period hPeriod)
    (boundary : Boundary) (outer inner : TangentIndex)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Fin 4 → Real)
    (hAt : patch.coordinateMap coordinate = normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) :
    let hNonNull := normalGraphNonNullAt_of_frameFreeBoundaryInducedDomain period hPeriod baseMetric tensor
      variedMetric hVaried displacement parameter hCurrent.1.1
    let base := (orientationDoubleToThroat period hPeriod boundary, parameter)
    let normal := normalGraphCanonicalHolonomicMetricUnitNormalCoordinatesAt period hPeriod variedMetric
      displacement parameter hNonNull boundary patch coordinate hAt
    frameFreeBoundaryRawSecondFormEvaluation period hPeriod outer inner
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter) boundary =
      normalGraphHolonomicRawExtrinsicCurvatureCoordinates period hPeriod variedMetric displacement base patch coordinate normal
        (normalBoundaryOrientationTangentEquiv period hPeriod boundary ((throatFrame).vectorAt boundary outer))
        (normalBoundaryOrientationTangentEquiv period hPeriod boundary ((throatFrame).vectorAt boundary inner)) base := by
  dsimp only
  exact (frameFreeBoundaryRawSecondFormEvaluation_smooth_eq_gauss period hPeriod tensor variedMetric hVaried
    displacement parameter hCurrent boundary outer inner patch coordinate hAt).trans
      (normalGraphCanonicalHolonomicGaussRawExtrinsicCurvatureCoordinatesAt_eq_weingarten period hPeriod variedMetric
        displacement parameter _ boundary patch coordinate hAt _ _).symm

include hVaried in
theorem frameFreeBoundarySecondFormEvaluation_smooth_eq_gauss
    (hCurrent : (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter) ∈
      frameFreeBoundarySecondFormDomain period hPeriod)
    (boundary : Boundary) (outer inner : TangentIndex)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Fin 4 → Real)
    (hAt : patch.coordinateMap coordinate = normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) :
    let hNonNull := normalGraphNonNullAt_of_frameFreeBoundaryInducedDomain period hPeriod baseMetric tensor
      variedMetric hVaried displacement parameter hCurrent.1.1
    frameFreeBoundarySecondFormEvaluation period hPeriod outer inner
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter) boundary =
      normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt period hPeriod variedMetric displacement
        parameter hNonNull boundary patch coordinate hAt
        (normalBoundaryOrientationTangentEquiv period hPeriod boundary ((throatFrame).vectorAt boundary outer))
        (normalBoundaryOrientationTangentEquiv period hPeriod boundary ((throatFrame).vectorAt boundary inner)) := by
  dsimp only
  have hRaw (first second : TangentIndex) := frameFreeBoundaryRawSecondFormEvaluation_smooth_eq_gauss
    period hPeriod tensor variedMetric hVaried displacement parameter hCurrent boundary first second patch coordinate hAt
  simp only [frameFreeBoundarySecondFormEvaluation, BoundedContinuousFunction.smul_apply,
    BoundedContinuousFunction.add_apply, smul_eq_mul, normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt,
    hRaw]

/-- Raise with the fixed reference dual, then use the faithful induced inverse
lift. No inverse of the redundant Gram matrix is taken. -/
def frameFreeBoundarySecondFormRelativeMatrix (current : Input) : MatrixField := fun row column =>
  ∑ middle : TangentIndex, normalBoundaryReferenceDualCoefficientMatrix period hPeriod row middle *
    frameFreeBoundarySecondFormEvaluation period hPeriod middle column current

theorem frameFreeBoundarySecondFormRelativeMatrix_contDiffOn_two :
    ContDiffOn Real 2 (frameFreeBoundarySecondFormRelativeMatrix period hPeriod)
      (frameFreeBoundarySecondFormDomain period hPeriod) := by
  rw [contDiffOn_pi]
  intro row
  rw [contDiffOn_pi]
  intro column
  unfold frameFreeBoundarySecondFormRelativeMatrix
  exact ContDiffOn.sum fun middle _ => contDiffOn_const.mul
    (frameFreeBoundarySecondFormEvaluation_contDiffOn_two period hPeriod middle column)

def frameFreeBoundaryMeanCurvatureEvaluation (current : Input) : Field :=
  Matrix.trace (frameFreeBoundaryInducedLiftInverse period hPeriod baseMetric current *
    frameFreeBoundarySecondFormRelativeMatrix period hPeriod current)

theorem frameFreeBoundaryMeanCurvatureEvaluation_contDiffOn_two :
    ContDiffOn Real 2 (frameFreeBoundaryMeanCurvatureEvaluation period hPeriod)
      (frameFreeBoundarySecondFormDomain period hPeriod) := by
  have hInverse := (frameFreeBoundaryInducedLiftInverse_contDiffOn_two period hPeriod baseMetric).mono
    (show frameFreeBoundarySecondFormDomain period hPeriod ⊆ frameFreeBoundaryInducedDomain period hPeriod baseMetric
      from fun _ h => h.1.1)
  have hSecond := frameFreeBoundarySecondFormRelativeMatrix_contDiffOn_two period hPeriod
  unfold frameFreeBoundaryMeanCurvatureEvaluation Matrix.trace
  exact ContDiffOn.sum fun row _ => by
    simp only [Matrix.diag_apply, Matrix.mul_apply]
    exact ContDiffOn.sum fun column _ =>
      (contDiffOn_pi.mp (contDiffOn_pi.mp hInverse row) column).mul
        (contDiffOn_pi.mp (contDiffOn_pi.mp hSecond column) row)

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundarySecondForm4D
