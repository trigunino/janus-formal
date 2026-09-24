import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetric4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameBRSTPairing4D

/-! The completed contraction agrees with the actual pullback of `g + h` by the
pre-existing smooth normal graph. All frame reconstructions allow redundancy. -/
namespace JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetricSmooth4D
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Manifold ContDiff BigOperators BoundedContinuousFunction
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusOrientationDoubleCover
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusFiniteSmoothTangentGenerators4D
open P0EFTJanusMappingTorusDifferentialLLWeakEquation4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricBVFirstLevel4D
open P0EFTJanusD8NormalBundleD9DisplacementBridge4D
open P0EFTJanusProgramPGeneralMetricPositiveDualizer4D
open P0EFTJanusProgramPGeneralMetricC2RelativeEndomorphism4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryC3MetricCore4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D
open P0EFTJanusProgramPGlobalCandidateANormalBoundaryFiberSubstitution4D
open P0EFTJanusFiniteFrameBRSTPairing4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointCore4D
open P0EFTJanusProgramPT12FrameFreeBoundaryJointC2Evaluation4D
open P0EFTJanusProgramPT12FrameFreeBoundaryTangentCoefficients4D
open P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetric4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local notation "Boundary" => OrientationBoundary period hPeriod
local instance : CompactSpace Boundary :=
  fixedThroatQuotientCompactSpace (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)
local instance : ChartedSpace ThroatCoverModel Boundary :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryChartedSpace period hPeriod
local instance : IsManifold throatCoverModelWithCorners ω Boundary :=
  P0EFTJanusProgramPGlobalCandidateANormalBoundarySameActionClosure4D.orientationBoundaryIsManifold period hPeriod
local notation "TangentIndex" => NormalBoundaryTangentIndex period hPeriod

theorem frameFreeBoundaryCollarTangent_reconstructs
    (frame : SmoothD8Frame period hPeriod) (metric : SmoothGeneralLorentzMetric period hPeriod)
    (boundary : Boundary) (latitude slope : Real) (index : TangentIndex) :
    (∑ row : Fin frame.count,
      (frameFreeBoundaryHorizontalCoefficient period hPeriod frame metric index row (boundary, latitude) +
        slope * frameFreeBoundaryVerticalCoefficient period hPeriod frame metric row (boundary, latitude)) •
      frame.vectorAt (normalBoundaryLatitudeFiberPoint period hPeriod boundary latitude) row) =
      mfderiv (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) coverModelWithCorners
        (fun current : Boundary × Real => normalBoundaryLatitudeFiberPoint period hPeriod current.1 current.2)
        (boundary, latitude) ((finiteSmoothThroatGeneratingFrame (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt boundary index, slope) := by
  let point := normalBoundaryLatitudeFiberPoint period hPeriod boundary latitude
  let collar := fun current : Boundary × Real =>
    normalBoundaryLatitudeFiberPoint period hPeriod current.1 current.2
  have hHorizontal := frameFreeBoundaryLiftCoefficient_reconstructs period hPeriod frame metric
    (normalBoundaryLatitudeHorizontalFiberLift period hPeriod index) (boundary, latitude)
  change (normalBoundaryLatitudeHorizontalFiberLift period hPeriod index (boundary, latitude)).2 =
    ∑ row : Fin frame.count,
      frameFreeBoundaryHorizontalCoefficient period hPeriod frame metric index row (boundary, latitude) •
        frame.vectorAt point row at hHorizontal
  have hVertical := frameFreeBoundaryLiftCoefficient_reconstructs period hPeriod frame metric
    (fun current => normalBoundaryLatitudeFiberLift period hPeriod current.1 current.2) (boundary, latitude)
  rw [normalBoundaryLatitudeFiberLift_base] at hVertical
  change (normalBoundaryLatitudeFiberLift period hPeriod boundary latitude).2 =
    ∑ row : Fin frame.count,
      frameFreeBoundaryVerticalCoefficient period hPeriod frame metric row (boundary, latitude) •
        frame.vectorAt point row at hVertical
  have hHorizontalDerivative := normalBoundaryLatitudeHorizontalFiberLift_eq_mfderiv_horizontal
    period hPeriod index boundary latitude
  have hVerticalDerivative := normalBoundaryLatitudeFiberLift_eq_mfderiv_vertical
    period hPeriod boundary latitude
  have hVerticalSlope :
      mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
        (fun varied : Real => collar (boundary, varied)) latitude slope =
      slope • (normalBoundaryLatitudeFiberLift period hPeriod boundary latitude).2 := by
    calc
      _ = mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
          (fun varied : Real => collar (boundary, varied)) latitude (slope • (1 : Real)) := by simp
      _ = slope • mfderiv (modelWithCornersSelf Real Real) coverModelWithCorners
          (fun varied : Real => collar (boundary, varied)) latitude 1 := by rw [map_smul]
      _ = _ := by rw [← hVerticalDerivative]
  have hCollar : MDifferentiableAt
      (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) coverModelWithCorners
      collar (boundary, latitude) :=
    (normalBoundaryLatitudeFiberPoint_joint_contMDiff period hPeriod).mdifferentiableAt (by simp)
  have hSplit := mfderiv_prod_eq_add_apply (E := ThroatCoverCoordinates) (E' := Real)
    (I := throatCoverModelWithCorners) (I' := modelWithCornersSelf Real Real)
    (v := ((finiteSmoothThroatGeneratingFrame (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt boundary index, slope)) hCollar
  calc
    _ = (∑ row : Fin frame.count,
        frameFreeBoundaryHorizontalCoefficient period hPeriod frame metric index row (boundary, latitude) •
          frame.vectorAt point row) +
      slope • (∑ row : Fin frame.count,
        frameFreeBoundaryVerticalCoefficient period hPeriod frame metric row (boundary, latitude) •
          frame.vectorAt point row) := by
      simp only [point, add_smul, Finset.sum_add_distrib, Finset.smul_sum, smul_smul]
    _ = _ := by
      rw [← hHorizontal, ← hVertical, hHorizontalDerivative, ← hVerticalSlope]
      exact hSplit.symm

variable (metric : SmoothGeneralLorentzMetric period hPeriod)
local notation "frame" => finiteSmoothTangentFrame period hPeriod
local notation "Index" => BoundaryMetricJetIndex period hPeriod
variable (tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
  (displacement : SmoothNormalDisplacement period hPeriod) (parameter : Real)

theorem frameFreeBoundaryGraphTangentEvaluation_smooth_reconstructs (boundary : Boundary) (index : TangentIndex) :
    let variation := smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement)
    let point := normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)
    (∑ row : Index,
      frameFreeBoundaryGraphTangentEvaluation period hPeriod metric index row (variation, parameter) boundary •
        (finiteSmoothTangentFrame period hPeriod).vectorAt point row) =
      mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fun current : Boundary => normalGraphOrientationDouble period hPeriod displacement (current, parameter))
        boundary ((finiteSmoothThroatGeneratingFrame (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt boundary index) := by
  dsimp only
  let variation := smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement)
  let normal := smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement
  let latitude := Real.arctan (parameter *
    normalDisplacementOrientationScalar period hPeriod displacement boundary)
  let slope := (1 / (1 + (parameter * normalBoundaryC2JetCoreValueAt period hPeriod boundary normal) ^ 2)) *
    (parameter * normalBoundaryC2JetCoreFirstAt period hPeriod boundary normal index)
  let point := normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)
  have hPoint : normalBoundaryLatitudeFiberPoint period hPeriod boundary latitude = point := by
    change normalBoundaryLatitudeFiberPoint period hPeriod boundary
      (Real.arctan (parameter * normalDisplacementOrientationScalar period hPeriod displacement boundary)) = _
    rw [← normalBoundaryC2JetCoreValueAt_smooth period hPeriod displacement boundary]
    rw [← normalBoundaryRawFiberPoint_eq_latitude, normalBoundaryRawFiberPoint_graph,
      normalBoundaryC2Graph_smooth]
  have hCoefficient (row : Index) :
      frameFreeBoundaryGraphTangentEvaluation period hPeriod metric index row (variation, parameter) boundary =
      frameFreeBoundaryHorizontalCoefficient period hPeriod frame metric index row (boundary, latitude) +
        slope * frameFreeBoundaryVerticalCoefficient period hPeriod frame metric row (boundary, latitude) := by
    rw [frameFreeBoundaryGraphTangentEvaluation_apply]
    change frameFreeBoundaryHorizontalCoefficient period hPeriod frame metric index row
        (boundary, Real.arctan (parameter * normalBoundaryC2JetCoreValueAt period hPeriod boundary normal)) +
      slope * frameFreeBoundaryVerticalCoefficient period hPeriod frame metric row
        (boundary, Real.arctan (parameter * normalBoundaryC2JetCoreValueAt period hPeriod boundary normal)) = _
    dsimp only [latitude]
    rw [normalBoundaryC2JetCoreValueAt_smooth]
  have hCollar := frameFreeBoundaryCollarTangent_reconstructs
    period hPeriod frame metric boundary latitude slope index
  have hHistorical :
      mfderiv throatCoverModelWithCorners coverModelWithCorners
        (fun current : Boundary => normalGraphOrientationDouble period hPeriod displacement (current, parameter))
        boundary ((finiteSmoothThroatGeneratingFrame (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt boundary index) =
      mfderiv (throatCoverModelWithCorners.prod (modelWithCornersSelf Real Real)) coverModelWithCorners
        (fun current : Boundary × Real => normalBoundaryLatitudeFiberPoint period hPeriod current.1 current.2)
        (boundary, latitude) ((finiteSmoothThroatGeneratingFrame (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt boundary index, slope) := by
    have hExplicit := normalGraphOrientationDouble_mfderiv_frame_eq_collar
      period hPeriod displacement parameter boundary index
    dsimp only at hExplicit
    exact hExplicit
  rw [hPoint] at hCollar
  calc
    _ = ∑ row : Index,
        (frameFreeBoundaryHorizontalCoefficient period hPeriod frame metric index row (boundary, latitude) +
          slope * frameFreeBoundaryVerticalCoefficient period hPeriod frame metric row (boundary, latitude)) •
          (finiteSmoothTangentFrame period hPeriod).vectorAt point row := by
      apply Finset.sum_congr rfl
      intro row _
      rw [hCoefficient]
    _ = _ := hCollar.trans hHistorical.symm

theorem frameFreeBoundaryActualMetricEvaluation_smooth (boundary : Boundary) (row column : Index) :
    let point := normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)
    frameFreeBoundaryActualMetricEvaluation period hPeriod metric row column
      (smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement), parameter) boundary =
      (metric.tensor + tensor).tensor point ((finiteSmoothTangentFrame period hPeriod).vectorAt point row) ((finiteSmoothTangentFrame period hPeriod).vectorAt point column) := by
  dsimp only
  let point := normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)
  let variation := smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement)
  have hBase (i j : Index) :
      frameFreeBoundaryBaseMetricEvaluation period hPeriod metric i j (variation, parameter) boundary =
      generalMetricFrameCoefficient period hPeriod frame metric.tensor i j point := by
    rw [frameFreeBoundaryBaseMetricEvaluation_apply]
    change generalMetricFrameCoefficient period hPeriod frame metric.tensor i j
      (normalBoundaryC2Graph period hPeriod
        (smoothNormalDisplacementToBoundaryC2JetCore period hPeriod displacement) parameter boundary) = _
    rw [normalBoundaryC2Graph_smooth]
  have hRelative (i j : Index) :
      frameFreeBoundaryJointValueEvaluation period hPeriod metric i j (variation, parameter) boundary =
      smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor i j point := by
    rw [frameFreeBoundaryJointValueEvaluation_eq_atGraph, frameFreeBoundaryRelativeEntryAtGraph_smooth]
  have hPair := finiteFrameCovector_pairing period hPeriod frame metric point
    (metric.tensor.tensor point ((finiteSmoothTangentFrame period hPeriod).vectorAt point row))
    (inverseMetricSharp period hPeriod metric point (tensor.tensor point ((finiteSmoothTangentFrame period hPeriod).vectorAt point column)))
  have hFlat := congrArg (fun covector => covector ((finiteSmoothTangentFrame period hPeriod).vectorAt point row))
    (metric_flat_inverseMetricSharp period hPeriod metric point
      (tensor.tensor point ((finiteSmoothTangentFrame period hPeriod).vectorAt point column)))
  change (metric.musical point).toContinuousLinearMap
    (inverseMetricSharp period hPeriod metric point (tensor.tensor point ((finiteSmoothTangentFrame period hPeriod).vectorAt point column)))
      ((finiteSmoothTangentFrame period hPeriod).vectorAt point row) = _ at hFlat
  rw [metric.musical_eq_tensor point, metric.tensor.symmetric, tensor.symmetric point] at hFlat
  have hTensor :
      (∑ middle : Index, generalMetricFrameCoefficient period hPeriod frame metric.tensor row middle point *
        smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor middle column point) =
      tensor.tensor point ((finiteSmoothTangentFrame period hPeriod).vectorAt point row) ((finiteSmoothTangentFrame period hPeriod).vectorAt point column) := by
    simpa only [generalMetricFrameCoefficient_apply,
      smoothGeneralMetricRelativeEndomorphismMatrix_entry_apply, finiteFrameEndomorphismMatrixAt_apply,
      raisedGeneralMetricTensorAt, ContinuousLinearMap.comp_apply, inverseMetricSharp] using hPair.symm.trans hFlat
  simp only [frameFreeBoundaryActualMetricEvaluation, BoundedContinuousFunction.add_apply,
    BoundedContinuousFunction.sum_apply, BoundedContinuousFunction.mul_apply]
  change frameFreeBoundaryBaseMetricEvaluation period hPeriod metric row column (variation, parameter) boundary +
    (∑ middle : Index,
      frameFreeBoundaryBaseMetricEvaluation period hPeriod metric row middle (variation, parameter) boundary *
        frameFreeBoundaryJointValueEvaluation period hPeriod metric middle column (variation, parameter) boundary) = _
  calc
    _ = generalMetricFrameCoefficient period hPeriod frame metric.tensor row column point +
        (∑ middle : Index, generalMetricFrameCoefficient period hPeriod frame metric.tensor row middle point *
          smoothGeneralMetricRelativeEndomorphismMatrix period hPeriod frame metric tensor middle column point) := by
      apply congrArg₂ (fun first second : Real => first + second) (hBase row column)
      apply Finset.sum_congr rfl
      intro middle _
      exact congrArg₂ (fun first second : Real => first * second) (hBase row middle) (hRelative middle column)
    _ = _ := by
      rw [hTensor, generalMetricFrameCoefficient_apply]
      rfl

/-- Unconditional smooth agreement with the genuine induced symmetric tensor. -/
theorem frameFreeBoundaryInducedMetricEvaluation_smooth (boundary : Boundary) (first second : TangentIndex) :
    let variation := smoothToFrameFreeBoundaryJointCore period hPeriod frame metric (tensor, displacement)
    let point := normalGraphOrientationDouble period hPeriod displacement (boundary, parameter)
    let graph := fun current : Boundary =>
      normalGraphOrientationDouble period hPeriod displacement (current, parameter)
    frameFreeBoundaryInducedMetricEvaluation period hPeriod metric (variation, parameter) first second boundary =
      (metric.tensor + tensor).tensor point
        (mfderiv throatCoverModelWithCorners coverModelWithCorners graph boundary ((finiteSmoothThroatGeneratingFrame (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt boundary first))
        (mfderiv throatCoverModelWithCorners coverModelWithCorners graph boundary ((finiteSmoothThroatGeneratingFrame (doubledPeriod period) (doubledPeriod_ne_zero period hPeriod)).vectorAt boundary second)) := by
  dsimp only
  have hMetric (row column : Index) := frameFreeBoundaryActualMetricEvaluation_smooth
    period hPeriod metric tensor displacement parameter boundary row column
  have hFirst := frameFreeBoundaryGraphTangentEvaluation_smooth_reconstructs
    period hPeriod metric tensor displacement parameter boundary first
  have hSecond := frameFreeBoundaryGraphTangentEvaluation_smooth_reconstructs
    period hPeriod metric tensor displacement parameter boundary second
  dsimp only at hMetric hFirst hSecond
  rw [frameFreeBoundaryInducedMetricEvaluation_apply]
  simp_rw [hMetric]
  rw [← hFirst]
  simp only [map_sum, map_smul, _root_.sum_apply, _root_.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro row _
  rw [← hSecond]
  simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro column _
  ring

end
end JanusFormal.P0EFTJanusProgramPT12FrameFreeBoundaryInducedMetricSmooth4D
