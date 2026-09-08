import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameRegularC2PhysicalStationarityResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalTenFlowGeneratorDivergence4D

/-! # Intrinsic De Donder residual of the finite physical center -/

namespace JanusFormal
namespace P0EFTJanusFiniteFrameRegularC2PhysicalDiffeomorphismDeDonderResidual4D

set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option synthInstance.maxHeartbeats 1200000
set_option maxRecDepth 8000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff BigOperators Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D
open P0EFTJanusMappingTorusGlobalGeneralMetricSymmetricTensorDivergence4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusMappingTorusCanonicalTenFlowGeneratorDivergence4D
open P0EFTJanusEffectiveD8SmoothCovectorFieldFunctor4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2IdentityRootLift4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMetricResidualTestSeparation4D
open P0EFTJanusFiniteFrameRegularC2RootDerivativeSylvesterBridge4D
open P0EFTJanusFiniteFrameBRSTPairing4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFrameC2CanonicalVolume4D
open P0EFTJanusFiniteFrameC2DeDonder4D
open P0EFTJanusFiniteFrameDiffeomorphismBRSTSmoothFeatures4D
open P0EFTJanusFiniteFrameC2DiffeomorphismBRSTCenterEuler4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalEulerStationaritySplit4D
open P0EFTJanusFiniteFramePairedC2PhysicalEulerThreeBlockSplit4D
open P0EFTJanusFiniteFramePairedC2PhysicalDiffeomorphismCenterEuler4D
open P0EFTJanusFiniteFrameRegularC2PhysicalMetricResidualBridge4D
open P0EFTJanusFiniteFrameRegularC2PhysicalStationarityResidual4D
open P0EFTJanusPairedInteractionSmoothMetricResidual4D
open P0EFTJanusReciprocalBimetricPotential

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

private abbrev C2Scalar :=
  CanonicalPhysicalScalarC2JetCore period hPeriod

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance : IsManifold coverModelWithCorners ω
    (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

private abbrev SmoothTangentSection :=
  ContMDiffSection coverModelWithCorners CoverCoordinates ∞
    (fun point : EffectiveQuotient period hPeriod =>
      TangentSpace coverModelWithCorners point)

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance : IsFiniteMeasure
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

/-- Evaluation of a smooth covector on one member of an arbitrary finite
generating frame is a genuine smooth scalar. -/
def finiteFrameSmoothCovectorCoefficient
    (frame : SmoothD8Frame period hPeriod)
    (covector : EffectiveD8SmoothCovectorField
      (generalMetricDivergenceBackground period hPeriod))
    (index : Fin frame.count) : SmoothQuotientField period hPeriod Real where
  toFun := fun point => covector point (frame.vectorAt point index)
  contMDiff_toFun := by
    have hApplied := covector.contMDiff.clm_bundle_apply
      (frame.contMDiff_vector index)
    intro point
    have hAppliedAt := hApplied point
    rw [Bundle.contMDiffAt_section] at hAppliedAt
    simpa using hAppliedAt

/-- Positive metric volume and the finite generating property make the
integrated covector-vector pairing separating. -/
theorem finiteFrameSmoothCovector_weightedPairing_zero_iff
    (frame : SmoothD8Frame period hPeriod)
    (reference metric : SmoothGeneralLorentzMetric period hPeriod)
    (covector : EffectiveD8SmoothCovectorField
      (generalMetricDivergenceBackground period hPeriod)) :
    (∀ vector : SmoothTangentSection period hPeriod,
      (∫ point, globalMetricVolumeRatio period hPeriod metric point *
        covector point (vector point)
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) = 0) ↔
      covector = 0 := by
  constructor
  · intro hPairing
    have hCoefficient (index : Fin frame.count) :
        finiteFrameSmoothCovectorCoefficient period hPeriod frame covector index = 0 := by
      let weighted : SmoothQuotientField period hPeriod Real :=
        { toFun := fun point => globalMetricVolumeRatio period hPeriod metric point *
              covector point (frame.vectorAt point index)
          contMDiff_toFun :=
            (globalSmoothMetricVolumeRatio period hPeriod metric).contMDiff_toFun.mul
              (finiteFrameSmoothCovectorCoefficient period hPeriod frame covector index
                ).contMDiff_toFun }
      have hWeak : ∀ test : SmoothQuotientField period hPeriod Real,
          (∫ point, test point * weighted point
            ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) = 0 := by
        intro test
        let vector : SmoothTangentSection period hPeriod :=
          { toFun := fun point => test point • frame.vectorAt point index
            contMDiff_toFun :=
              (test.contMDiff_toFun.of_le (by simp)).smul_section
                (frame.contMDiff_vector index) }
        have h := hPairing vector
        change (∫ point, test point *
          (globalMetricVolumeRatio period hPeriod metric point *
            covector point (frame.vectorAt point index))
          ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod) = 0
        convert h using 1
        apply integral_congr_ae
        filter_upwards [] with point
        change test point *
            (globalMetricVolumeRatio period hPeriod metric point *
              covector point (frame.vectorAt point index)) =
          globalMetricVolumeRatio period hPeriod metric point *
            covector point (test point • frame.vectorAt point index)
        simp only [map_smul, smul_eq_mul]
        ring
      have hWeighted := canonicalSmoothScalar_eq_zero_of_weak_pairings period hPeriod
        weighted hWeak
      apply SmoothQuotientField.ext period hPeriod Real
      intro point
      have hPoint := congrArg
        (fun field : SmoothQuotientField period hPeriod Real => field point) hWeighted
      change globalMetricVolumeRatio period hPeriod metric point *
          covector point (frame.vectorAt point index) = 0 at hPoint
      exact (mul_eq_zero.mp hPoint).resolve_left
        (ne_of_gt (globalMetricVolumeRatio_pos period hPeriod metric point))
    apply ContMDiffSection.ext
    intro point
    apply ContinuousLinearMap.ext
    intro vector
    rw [finiteFrameCovector_pairing period hPeriod frame reference point (covector point) vector]
    apply Finset.sum_eq_zero
    intro index _
    have hPoint := congrArg
      (fun field : SmoothQuotientField period hPeriod Real => field point)
      (hCoefficient index)
    change covector point (frame.vectorAt point index) = 0 at hPoint
    rw [hPoint]
    simp
  · rintro rfl vector
    simp

/-- On a smooth metric and tensor lift, the finite auxiliary-field action is
the intrinsic De Donder covector paired with the same smooth vector. -/
theorem finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction_smooth_vector
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (variation tensor : SmoothSymmetricCovariantTwoTensor period hPeriod)
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (hMetric : metric.tensor = baseMetric.tensor + variation)
    (hVolume : smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric)
    (vector : SmoothTangentSection period hPeriod) :
    finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction period hPeriod frame baseMetric
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric variation)
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame baseMetric tensor)
        (finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod frame baseMetric vector) =
      ∫ point, globalMetricVolumeRatio period hPeriod metric point *
        globalGeneralMetricDeDonderLinearMap period hPeriod metric tensor point (vector point)
        ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod := by
  unfold finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction
    finiteFrameC2DiffeomorphismBRSTNakanishiLautrupDensity
  rw [finiteFrameBRSTCanonicalIntegralCLM_apply,
    finiteFrameCanonicalVolumeC0_smooth period hPeriod frame baseMetric variation metric hMetric
      hVolume,
    finiteFrameDiffeomorphismC2ToContinuous_smooth period hPeriod frame baseMetric vector]
  apply integral_congr_ae
  filter_upwards [] with point
  simp only [ContinuousMap.mul_apply, ContinuousMap.sum_apply]
  simp_rw [finiteFrameC2DeDonderCoefficient_smooth period hPeriod frame baseMetric variation
    tensor metric hMetric hVolume.1 point]
  change globalMetricVolumeRatio period hPeriod metric point *
      (∑ index : Fin frame.count,
        globalGeneralMetricDeDonderLinearMap period hPeriod metric tensor point
            (frame.vectorAt point index) *
          generalMetricFiniteFrameCoefficient period hPeriod frame baseMetric vector index point) =
    globalMetricVolumeRatio period hPeriod metric point *
      globalGeneralMetricDeDonderLinearMap period hPeriod metric tensor point (vector point)
  rw [← finiteFrameSmoothCovector_pairing period hPeriod frame baseMetric vector point
    (globalGeneralMetricDeDonderLinearMap period hPeriod metric tensor point)]

/-- Vanishing of every transported finite auxiliary pairing is equivalent to
the intrinsic global De Donder equation for the smooth relative tensor. -/
theorem finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction_transition_zero_iff_globalDeDonder
    (frame : SmoothD8Frame period hPeriod)
    (plusMetric minusMetric : SmoothGeneralLorentzMetric period hPeriod)
    (hShift : smoothToGeneralMetricRelativeC2Core period hPeriod frame plusMetric
        (minusMetric.tensor - plusMetric.tensor) ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame plusMetric) :
    (∀ field : FiniteFrameDiffeomorphismC2Core period hPeriod frame,
      finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction period hPeriod frame plusMetric
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusMetric
          (minusMetric.tensor - plusMetric.tensor))
        (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusMetric
          (minusMetric.tensor - plusMetric.tensor))
        (finiteFrameDiffeomorphismC2Transition period hPeriod frame frame plusMetric field) = 0) ↔
      globalGeneralMetricDeDonderLinearMap period hPeriod minusMetric
        (minusMetric.tensor - plusMetric.tensor) = 0 := by
  have hMetric : minusMetric.tensor =
      plusMetric.tensor + (minusMetric.tensor - plusMetric.tensor) := by
    abel
  constructor
  · intro hPairing
    apply (finiteFrameSmoothCovector_weightedPairing_zero_iff period hPeriod frame plusMetric
      minusMetric (globalGeneralMetricDeDonderLinearMap period hPeriod minusMetric
        (minusMetric.tensor - plusMetric.tensor))).mp
    intro vector
    have hAction := hPairing
      (finiteFrameSmoothDiffeomorphismC2Coefficients period hPeriod frame plusMetric vector)
    rw [finiteFrameDiffeomorphismC2Transition_smooth_vector period hPeriod frame frame
      plusMetric plusMetric vector,
      finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction_smooth_vector period hPeriod
        frame plusMetric (minusMetric.tensor - plusMetric.tensor)
        (minusMetric.tensor - plusMetric.tensor) minusMetric hMetric hShift vector] at hAction
    exact hAction
  · intro hDeDonder field
    have hCoefficient (point : EffectiveQuotient period hPeriod) (index : Fin frame.count) :
        finiteFrameC2DeDonderCoefficient period hPeriod frame plusMetric index
          (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusMetric
              (minusMetric.tensor - plusMetric.tensor),
            smoothToGeneralMetricRelativeC2Core period hPeriod frame plusMetric
              (minusMetric.tensor - plusMetric.tensor)) point = 0 := by
      rw [finiteFrameC2DeDonderCoefficient_smooth period hPeriod frame plusMetric
        (minusMetric.tensor - plusMetric.tensor) (minusMetric.tensor - plusMetric.tensor)
        minusMetric hMetric hShift.1 point index, hDeDonder]
      rfl
    unfold finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction
      finiteFrameC2DiffeomorphismBRSTNakanishiLautrupDensity
    rw [finiteFrameBRSTCanonicalIntegralCLM_apply]
    apply integral_eq_zero_of_ae
    filter_upwards [] with point
    simp only [ContinuousMap.mul_apply, ContinuousMap.sum_apply]
    have hSum : (∑ index : Fin frame.count,
        finiteFrameC2DeDonderCoefficient period hPeriod frame plusMetric index
            (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusMetric
                (minusMetric.tensor - plusMetric.tensor),
              smoothToGeneralMetricRelativeC2Core period hPeriod frame plusMetric
                (minusMetric.tensor - plusMetric.tensor)) point *
          finiteFrameDiffeomorphismC2ToContinuous period hPeriod frame
            (finiteFrameDiffeomorphismC2Transition period hPeriod frame frame plusMetric field)
            index point) = 0 := by
      apply Finset.sum_eq_zero
      intro index _
      rw [hCoefficient point index]
      simp
    rw [hSum]
    simp

/-- The physical diffeomorphism field equation at the regular center is the
intrinsic global De Donder equation of the relative minus tensor. -/
theorem finiteFramePairedC2PhysicalDiffeomorphismFieldsEuler_zero_iff_globalDeDonder
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hChart : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase)
    (frame : SmoothD8Frame period hPeriod)
    (hShift : smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
        (minusBase.metric.tensor - plusBase.metric.tensor) ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame plusBase.metric)
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    let hFiniteRegular :=
      regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod
        plusBase (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    finiteFramePairedC2PhysicalDiffeomorphismFieldsEuler period hPeriod geometry frame
        hFiniteRegular couplings interactionScale coefficients 0 = 0 ↔
      globalGeneralMetricDeDonderLinearMap period hPeriod minusBase.metric
        (minusBase.metric.tensor - plusBase.metric.tensor) = 0 := by
  dsimp only
  let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
    (minusBase.metric.tensor - plusBase.metric.tensor) hChart
  let hFiniteRegular :=
    regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart
  have hGeometryMinusTensor : geometry.minusMetric.tensor = minusBase.metric.tensor := by
    dsimp only [geometry]
    rw [regularGeneralMetricC2LorentzChartGeometry_minusMetric,
      regularGeneralMetricC2LorentzChartMetric_tensor]
    abel
  have hCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame =
      smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
        (minusBase.metric.tensor - plusBase.metric.tensor) := by
    unfold finiteFramePairedC2MinusCenter
    change smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
      (geometry.minusMetric.tensor - plusBase.metric.tensor) = _
    rw [hGeometryMinusTensor]
  have hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric := by
    rw [hCenter]
    change smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
      (minusBase.metric.tensor - plusBase.metric.tensor) ∈
        generalMetricRelativeC2VolumeDomain period hPeriod frame plusBase.metric
    exact hShift
  rw [finiteFramePairedC2PhysicalDiffeomorphismFieldsEuler_zero_iff_deDonderPairing
    period hPeriod geometry frame hFiniteRegular hMinusCenter couplings interactionScale
      coefficients, hCenter]
  exact finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction_transition_zero_iff_globalDeDonder
    period hPeriod frame plusBase.metric minusBase.metric hShift

/-- Full finite physical stationarity at the regular center is exactly the
metric residual equation and the intrinsic global De Donder equation. -/
theorem finiteFramePairedC2PhysicalEuler_zero_iff_residual_and_globalDeDonder
    (plusBase minusBase : RegularGeneralLorentzMetric period hPeriod)
    (hPlusCanonicalVolume : plusBase.volume =
      globalSmoothMetricVolumeRatio period hPeriod plusBase.metric)
    (hMinusCanonicalVolume : minusBase.volume =
      globalSmoothMetricVolumeRatio period hPeriod minusBase.metric)
    (hChart : regularGeneralMetricSmoothC2Variation period hPeriod plusBase
        (minusBase.metric.tensor - plusBase.metric.tensor) ∈
      regularGeneralMetricC2LorentzChartDomain period hPeriod plusBase)
    (frame : SmoothD8Frame period hPeriod)
    (hShift : smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
        (minusBase.metric.tensor - plusBase.metric.tensor) ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame plusBase.metric)
    (hZero : (0 : RegularGeneralMetricC2PairedRelativeCore period hPeriod plusBase minusBase) ∈
      regularGeneralMetricC2PairedLorentzMatrixDomain period hPeriod plusBase minusBase)
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    let hFiniteRegular :=
      regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod
        plusBase (minusBase.metric.tensor - plusBase.metric.tensor) hChart
    let hRoot := pairedInteractionCenter_rootAdmissible period hPeriod plusBase minusBase hZero
    finiteFramePairedC2PhysicalEuler period hPeriod geometry frame hFiniteRegular couplings
        interactionScale coefficients 0 = 0 ↔
      regularFramePairedMobileEinsteinHilbertInteractionResidual period hPeriod
          plusBase minusBase hRoot couplings interactionScale coefficients = 0 ∧
        globalGeneralMetricDeDonderLinearMap period hPeriod minusBase.metric
          (minusBase.metric.tensor - plusBase.metric.tensor) = 0 := by
  dsimp only
  let geometry := regularGeneralMetricC2LorentzChartGeometry period hPeriod plusBase
    (minusBase.metric.tensor - plusBase.metric.tensor) hChart
  let hFiniteRegular :=
    regularGeneralMetricC2LorentzChartGeometry_intrinsicSylvester_bijective period hPeriod plusBase
      (minusBase.metric.tensor - plusBase.metric.tensor) hChart
  have hGeometryMinusTensor : geometry.minusMetric.tensor = minusBase.metric.tensor := by
    dsimp only [geometry]
    rw [regularGeneralMetricC2LorentzChartGeometry_minusMetric,
      regularGeneralMetricC2LorentzChartMetric_tensor]
    abel
  have hCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame =
      smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
        (minusBase.metric.tensor - plusBase.metric.tensor) := by
    unfold finiteFramePairedC2MinusCenter
    change smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
      (geometry.minusMetric.tensor - plusBase.metric.tensor) = _
    rw [hGeometryMinusTensor]
  have hStationarity :=
    finiteFramePairedC2PhysicalEuler_zero_iff_residual_and_deDonderPairing period hPeriod
      plusBase minusBase hPlusCanonicalVolume hMinusCanonicalVolume hChart frame hShift hZero
        couplings interactionScale coefficients
  dsimp only at hStationarity
  have hGauge :
      (∀ field : FiniteFrameDiffeomorphismC2Core period hPeriod frame,
        finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction period hPeriod frame
          geometry.plusMetric
          (finiteFramePairedC2MinusCenter period hPeriod geometry frame)
          (finiteFramePairedC2MinusCenter period hPeriod geometry frame)
          (finiteFrameDiffeomorphismC2Transition period hPeriod frame frame
            geometry.plusMetric field) = 0) ↔
        globalGeneralMetricDeDonderLinearMap period hPeriod minusBase.metric
          (minusBase.metric.tensor - plusBase.metric.tensor) = 0 := by
    rw [hCenter]
    change
      (∀ field : FiniteFrameDiffeomorphismC2Core period hPeriod frame,
        finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction period hPeriod frame
          plusBase.metric
          (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
            (minusBase.metric.tensor - plusBase.metric.tensor))
          (smoothToGeneralMetricRelativeC2Core period hPeriod frame plusBase.metric
            (minusBase.metric.tensor - plusBase.metric.tensor))
          (finiteFrameDiffeomorphismC2Transition period hPeriod frame frame plusBase.metric
            field) = 0) ↔ _
    exact
      finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction_transition_zero_iff_globalDeDonder
        period hPeriod frame plusBase.metric minusBase.metric hShift
  rw [hStationarity, hGauge]

end
end P0EFTJanusFiniteFrameRegularC2PhysicalDiffeomorphismDeDonderResidual4D
end JanusFormal
