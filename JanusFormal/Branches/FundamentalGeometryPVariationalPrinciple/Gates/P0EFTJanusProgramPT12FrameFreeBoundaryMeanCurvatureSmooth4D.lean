import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FiniteCovectorTrace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundarySecondForm4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryTangentialProjection4D

/-! The faithful finite trace is the historical three-dimensional mean
curvature. The redundant generators are retained throughout: only their
synthesis, and the already proved genuine induced sharp, enter the trace. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryMeanCurvatureSmooth4D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff Topology BigOperators BoundedContinuousFunction
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusMappingTorusCanonicalHolonomicAtlasTransitionJets4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusProgramPThroatFiniteFrameReconstruction4D
open P0EFTJanusProgramPT12IntrinsicBulkGeometry4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedDomain4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedInverse4D
open P0EFTJanusProgramPT12FrameFreeBoundaryTangentialProjection4D
open P0EFTJanusProgramPT12FrameFreeBoundarySecondForm4D
open P0EFTJanusProgramPT12FiniteCovectorTrace4D

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
local notation "TangentIndex" => NormalBoundaryTangentIndex period hPeriod

/-- At its own center the tangent trivialization is the identity on the
model used to define that tangent fiber. -/
private theorem throatTangentTrivialization_self
    (point : MappingTorus (fixedEquatorData period hPeriod)) :
    (trivializationAt ThroatCoverCoordinates
      (ThroatTangentFiber period hPeriod) point).continuousLinearMapAt Real point =
        ContinuousLinearMap.id Real ThroatCoverCoordinates := by
  erw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core
    (mem_chart_source ThroatCoverModel point)]
  apply ContinuousLinearMap.ext
  intro vector
  exact tangentCoordChange_self (I := throatCoverModelWithCorners)
    (mem_extChartAt_source (I := throatCoverModelWithCorners) point)

/-- The historical coordinate inverse at the anchor is the genuine inverse
musical map, with the centered tangent/cotangent adapters made explicit. -/
theorem frameFreeBoundaryHistoricalInverseCoordinates_base_apply
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (point : MappingTorus (fixedEquatorData period hPeriod))
    (covector : ThroatCoverCoordinates →L[Real] Real) :
    normalGraphInducedMetricInverseCoordinates period hPeriod metric displacement
      (point, parameter) (point, parameter) covector =
    normalGraphInducedMetricInverse period hPeriod metric displacement parameter hNonNull point covector := by
  have hTangent := mem_baseSet_trivializationAt ThroatCoverCoordinates
    (ThroatTangentFiber period hPeriod) point
  have hCotangent := mem_baseSet_trivializationAt (ThroatCoverCoordinates →L[Real] Real)
    (ThroatCotangentFiber period hPeriod) point
  have hCotangentSelf :
      (trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) point).symmL Real point covector = covector := by
    erw [Bundle.Trivialization.symmL_apply]
    change (Bundle.Pretrivialization.continuousLinearMap (RingHom.id Real)
      (trivializationAt ThroatCoverCoordinates (ThroatTangentFiber period hPeriod) point)
      (trivializationAt Real (fun _ : MappingTorus (fixedEquatorData period hPeriod) => Real) point)).symm
        point covector = covector
    erw [Bundle.Pretrivialization.continuousLinearMap_symm_apply'
      (RingHom.id Real) _ _ ⟨hTangent, by simp⟩]
    simp [throatTangentTrivialization_self period hPeriod point]
    apply ContinuousLinearMap.ext
    intro vector
    rfl
  erw [normalGraphInducedMetricInverseCoordinates_eq_inCoordinates period hPeriod
    metric displacement (point, parameter) (point, parameter) hNonNull hTangent hCotangent]
  change (trivializationAt ThroatCoverCoordinates (ThroatTangentFiber period hPeriod) point).continuousLinearMapAt Real point
    (normalGraphInducedMetricInverse period hPeriod metric displacement parameter hNonNull point
      ((trivializationAt (ThroatCoverCoordinates →L[Real] Real)
        (ThroatCotangentFiber period hPeriod) point).symmL Real point covector)) = _
  erw [hCotangentSelf, throatTangentTrivialization_self]
  rfl

/-- The finite coefficient solver synthesizes to the genuine inverse
musical map on the physical throat. No curvature or chart enters here. -/
private theorem inducedSharp_synthesis
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor =
      (P0EFTJanusProgramPGlobalCandidateAGeometry4D.GlobalCandidateAGeometry.plusMetric
        (intrinsicBulkGeometry period hPeriod)).tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)
    (hCurrent : (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter) ∈
      frameFreeBoundaryInducedDomain period hPeriod baseMetric)
    (hNonNull : NormalGraphNonNullAt period hPeriod variedMetric displacement parameter)
    (boundary : Boundary) (covector : ThroatCoverCoordinates →L[Real] Real) :
    let current := (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter)
    let tangent := normalBoundaryOrientationTangentEquiv period hPeriod boundary
    let vectors : TangentIndex → ThroatCoverCoordinates := fun i => tangent ((throatFrame).vectorAt boundary i)
    let inverse : Matrix TangentIndex TangentIndex Real := Matrix.of fun i j =>
      frameFreeBoundaryInducedLiftInverse period hPeriod baseMetric current i j boundary
    let dual : Matrix TangentIndex TangentIndex Real := Matrix.of fun i j =>
      normalBoundaryReferenceDualCoefficientMatrix period hPeriod i j boundary
    finiteCovectorTraceSynthesis vectors ((inverse * dual).mulVec (fun i => covector (vectors i))) =
      normalGraphInducedMetricInverse period hPeriod variedMetric displacement parameter hNonNull
        (orientationDoubleToThroat period hPeriod boundary) covector := by
  dsimp only
  let current := (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter)
  let point := orientationDoubleToThroat period hPeriod boundary
  let tangent := normalBoundaryOrientationTangentEquiv period hPeriod boundary
  let pulled := covector.comp tangent.toContinuousLinearMap
  let raised := frameFreeBoundaryInducedInverseMusicalAt period hPeriod baseMetric current boundary pulled
  have hRaised := frameFreeBoundaryInducedInverseMusicalAt_smooth period hPeriod baseMetric tensor
    variedMetric hVaried displacement parameter hCurrent boundary pulled
  have hPushed : normalGraphInducedMetricValue period hPeriod variedMetric displacement parameter point
      (tangent raised) = covector := by
    refine ContinuousLinearMap.ext fun (vector : ThroatTangentFiber period hPeriod point) => ?_
    have h := congrArg (fun value => value (tangent.symm vector)) hRaised
    change normalGraphInducedMetricValue period hPeriod variedMetric displacement parameter point
      (tangent raised) (tangent (tangent.symm vector)) = covector (tangent (tangent.symm vector)) at h
    have hRetraction := tangent.apply_symm_apply vector
    have hLeft := congrArg (fun value : ThroatTangentFiber period hPeriod point =>
      normalGraphInducedMetricValue period hPeriod variedMetric displacement parameter point (tangent raised) value)
      hRetraction
    have hRight := congrArg (fun value : ThroatTangentFiber period hPeriod point => covector value) hRetraction
    exact hLeft.symm.trans (h.trans hRight)
  have hRecovered := normalGraphInducedMetricInverse_metric period hPeriod variedMetric displacement
    parameter hNonNull point (tangent raised)
  have hInverse := congrArg
    (fun value : ThroatCotangentFiber period hPeriod point =>
      normalGraphInducedMetricInverse period hPeriod variedMetric displacement parameter hNonNull point value) hPushed
  have hSynthesis :
      finiteCovectorTraceSynthesis (E := ThroatCoverCoordinates)
        (fun i : TangentIndex => tangent ((throatFrame).vectorAt boundary i))
        (((Matrix.of fun i j => frameFreeBoundaryInducedLiftInverse period hPeriod baseMetric current i j boundary) *
          Matrix.of (fun i j => normalBoundaryReferenceDualCoefficientMatrix period hPeriod i j boundary)).mulVec
          (fun i => covector (tangent ((throatFrame).vectorAt boundary i)))) = tangent raised := by
    simp only [finiteCovectorTraceSynthesis, raised, frameFreeBoundaryInducedInverseMusicalAt,
      intrinsicThroatFiniteFrameSynthesisAt_apply, map_sum, map_smul,
      pulled, ContinuousLinearMap.comp_apply, Matrix.mulVec_mulVec]
    rfl
  exact hSynthesis.trans (hRecovered.symm.trans hInverse)

/-- Symmetrization and reversal of the two historical slots, isolated from
all completed-core expressions. -/
private theorem historicalSecondForm_eq_gauss_reversed
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)
    (hNonNull : NormalGraphNonNullAt period hPeriod metric displacement parameter)
    (boundary : Boundary) (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Fin 4 → Real)
    (hAt : patch.coordinateMap coordinate = normalGraphOrientationDouble period hPeriod displacement (boundary, parameter))
    (first second : ThroatCoverCoordinates) :
    normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap period hPeriod metric displacement
      boundary parameter patch coordinate (orientationDoubleToThroat period hPeriod boundary, parameter) first second =
    normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt period hPeriod metric displacement
      parameter hNonNull boundary patch coordinate hAt second first := by
  have hFirst := normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates_base_eq_gauss
    period hPeriod metric displacement parameter hNonNull boundary patch coordinate hAt first second
  have hSecond := normalGraphCanonicalHolonomicLocalSectionRawExtrinsicCurvatureCoordinates_base_eq_gauss
    period hPeriod metric displacement parameter hNonNull boundary patch coordinate hAt second first
  have hSum := congrArg₂ (fun x y : Real => (1 / 2 : Real) * (x + y)) hFirst hSecond
  have hFormula := normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap_apply
    period hPeriod metric displacement boundary parameter patch coordinate
      (orientationDoubleToThroat period hPeriod boundary, parameter) first second
  have hSymmetric := normalGraphCanonicalHolonomicGaussExtrinsicCurvatureCoordinatesAt_symmetric
    period hPeriod metric displacement parameter hNonNull boundary patch coordinate hAt first second
  exact (hFormula.trans hSum).trans hSymmetric

private theorem meanCurvatureEvaluation_trace_at
    (current : FrameFreeBoundaryJointCore period hPeriod frame baseMetric × Real) (boundary : Boundary) :
    frameFreeBoundaryMeanCurvatureEvaluation period hPeriod current boundary =
      Matrix.trace
        (((Matrix.of fun i j => frameFreeBoundaryInducedLiftInverse period hPeriod baseMetric current i j boundary) *
          Matrix.of (fun i j => normalBoundaryReferenceDualCoefficientMatrix period hPeriod i j boundary)) *
          Matrix.of (fun i j => frameFreeBoundarySecondFormEvaluation period hPeriod i j current boundary)) := by
  rw [Matrix.mul_assoc]
  simp [frameFreeBoundaryMeanCurvatureEvaluation, frameFreeBoundarySecondFormRelativeMatrix,
    Matrix.trace, Matrix.mul_apply]

/-- The finite trace equals the same historical local-section contraction.
No independence or coordinate-basis assumption is made on the generators. -/
theorem frameFreeBoundaryMeanCurvatureEvaluation_smooth_eq_localSection
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor =
      (P0EFTJanusProgramPGlobalCandidateAGeometry4D.GlobalCandidateAGeometry.plusMetric
        (intrinsicBulkGeometry period hPeriod)).tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)
    (hCurrent : (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter) ∈
      frameFreeBoundarySecondFormDomain period hPeriod)
    (boundary : Boundary) (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Fin 4 → Real)
    (hAt : patch.coordinateMap coordinate = normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) :
    frameFreeBoundaryMeanCurvatureEvaluation period hPeriod
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter) boundary =
    normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily period hPeriod variedMetric displacement
      boundary parameter patch coordinate (orientationDoubleToThroat period hPeriod boundary, parameter) := by
  let current := (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter)
  let point := orientationDoubleToThroat period hPeriod boundary
  let hNonNull := normalGraphNonNullAt_of_frameFreeBoundaryInducedDomain period hPeriod baseMetric tensor
    variedMetric hVaried displacement parameter hCurrent.1.1
  let tangent := normalBoundaryOrientationTangentEquiv period hPeriod boundary
  let vectors : TangentIndex → ThroatCoverCoordinates := fun i => tangent ((throatFrame).vectorAt boundary i)
  let inverse : Matrix TangentIndex TangentIndex Real := Matrix.of fun i j =>
    frameFreeBoundaryInducedLiftInverse period hPeriod baseMetric current i j boundary
  let dual : Matrix TangentIndex TangentIndex Real := Matrix.of fun i j =>
    normalBoundaryReferenceDualCoefficientMatrix period hPeriod i j boundary
  let sharp := (normalGraphInducedMetricInverse period hPeriod variedMetric displacement parameter hNonNull point).toContinuousLinearMap
  let form := normalGraphCanonicalHolonomicLocalSectionExtrinsicCurvatureLinearMap period hPeriod
    variedMetric displacement boundary parameter patch coordinate (point, parameter)
  have hSharp (covector : ThroatCoverCoordinates →L[Real] Real) :
      finiteCovectorTraceSynthesis vectors ((inverse * dual).mulVec (fun i => covector (vectors i))) =
        sharp covector :=
    inducedSharp_synthesis period hPeriod tensor variedMetric hVaried displacement parameter
      hCurrent.1.1 hNonNull boundary covector
  have hCoefficients (row column : TangentIndex) :
      frameFreeBoundarySecondFormEvaluation period hPeriod row column current boundary =
        form (vectors column) (vectors row) := by
    have hSmooth := frameFreeBoundarySecondFormEvaluation_smooth_eq_gauss period hPeriod tensor variedMetric hVaried
      displacement parameter hCurrent boundary row column patch coordinate hAt
    have hHistorical := historicalSecondForm_eq_gauss_reversed period hPeriod variedMetric displacement
      parameter hNonNull boundary patch coordinate hAt (vectors column) (vectors row)
    exact hSmooth.trans hHistorical.symm
  have hMatrix : Matrix.of (fun row column => frameFreeBoundarySecondFormEvaluation period hPeriod row column current boundary) =
      Matrix.of (fun row column => form (vectors column) (vectors row)) := by
    ext row column
    exact hCoefficients row column
  have hEvaluation := meanCurvatureEvaluation_trace_at period hPeriod current boundary
  have hWeighted := congrArg (fun matrix : Matrix TangentIndex TangentIndex Real =>
    Matrix.trace ((inverse * dual) * matrix)) hMatrix
  have hFiniteTrace := finiteCovectorTrace_eq_sharp_trace vectors (inverse * dual) sharp hSharp form
  have hCoordinate : sharp.toLinearMap.comp form.toLinearMap =
      (normalGraphInducedMetricInverseCoordinates period hPeriod variedMetric displacement
        (point, parameter) (point, parameter)).toLinearMap.comp form.toLinearMap := by
    refine LinearMap.ext fun (vector : ThroatCoverCoordinates) => ?_
    exact (frameFreeBoundaryHistoricalInverseCoordinates_base_apply period hPeriod variedMetric
      displacement parameter hNonNull point (form vector)).symm
  have hTrace := congrArg (LinearMap.trace Real ThroatCoverCoordinates) hCoordinate
  have hHistorical := normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily_eq_trace period hPeriod
    variedMetric displacement boundary parameter patch coordinate (point, parameter)
  exact (((hEvaluation.trans hWeighted).trans hFiniteTrace).trans hTrace).trans hHistorical.symm

/-- Smooth agreement with the unchanged chart-free historical Gauss mean
curvature, whose definition uses the genuine induced inverse and a 3×3 trace. -/
theorem frameFreeBoundaryMeanCurvatureEvaluation_smooth_eq_gauss
    (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (variedMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hVaried : variedMetric.tensor =
      (P0EFTJanusProgramPGlobalCandidateAGeometry4D.GlobalCandidateAGeometry.plusMetric
        (intrinsicBulkGeometry period hPeriod)).tensor + tensor)
    (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)
    (hCurrent : (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter) ∈
      frameFreeBoundarySecondFormDomain period hPeriod)
    (boundary : Boundary) (patch : SmoothHolonomicFrameChart4 period hPeriod) (coordinate : Fin 4 → Real)
    (hAt : patch.coordinateMap coordinate = normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)) :
    let hNonNull := normalGraphNonNullAt_of_frameFreeBoundaryInducedDomain period hPeriod baseMetric tensor
      variedMetric hVaried displacement parameter hCurrent.1.1
    frameFreeBoundaryMeanCurvatureEvaluation period hPeriod
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame baseMetric (tensor, displacement), parameter) boundary =
      normalGraphCanonicalGaussMeanCurvature period hPeriod variedMetric displacement parameter hNonNull boundary := by
  dsimp only
  exact (frameFreeBoundaryMeanCurvatureEvaluation_smooth_eq_localSection period hPeriod tensor variedMetric hVaried
    displacement parameter hCurrent boundary patch coordinate hAt).trans
      (normalGraphCanonicalHolonomicLocalSectionMeanCurvatureFamily_base_eq_gauss period hPeriod variedMetric displacement
        parameter _ boundary patch coordinate hAt)

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryMeanCurvatureSmooth4D
