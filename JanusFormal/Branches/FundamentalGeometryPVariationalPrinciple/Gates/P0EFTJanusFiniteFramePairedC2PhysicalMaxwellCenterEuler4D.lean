import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalMaxwellAction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameRegularC2PhysicalDiffeomorphismDeDonderResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalEulerChainRule4D

/-! # Maxwell augmentation at the finite physical center -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalMaxwellCenterEuler4D

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
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusMappingTorusGlobalGeneralMetricDeDonder4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusProgramPRegularGeneralMetricAffineNondegenerateBridge4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartDomain4D
open P0EFTJanusProgramPRegularGeneralMetricC2LorentzChartGeometry4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalRelativeMetricCoreProjection4D
open P0EFTJanusProgramPRegularGeneralMetricC2PairedMinimalPhysicalAdmissibleDomainOpen4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D
open P0EFTJanusFiniteFrameC2MaxwellPairing4D
open P0EFTJanusFiniteFrameC2MobileMaxwellAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalEulerChainRule4D
open P0EFTJanusFiniteFramePairedC2PhysicalMaxwellAction4D
open P0EFTJanusFiniteFrameRegularC2RootDerivativeSylvesterBridge4D
open P0EFTJanusFiniteFrameRegularC2PhysicalMetricResidualBridge4D
open P0EFTJanusFiniteFrameRegularC2PhysicalDiffeomorphismDeDonderResidual4D
open P0EFTJanusPairedInteractionSmoothMetricResidual4D
open P0EFTJanusReciprocalBimetricPotential

attribute [local instance 2000]
  NormedAddCommGroup.toAddCommGroup NormedSpace.toModule
  PseudoMetricSpace.toUniformSpace UniformSpace.toTopologicalSpace

private theorem hasFDerivAt_eq_zero_of_fst_zero_snd_even
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    [NormedAddCommGroup G] [NormedSpace Real G]
    (action : E × G → Real) (metric : E) (derivative : E × G →L[Real] Real)
    (hDerivative : HasFDerivAt action derivative (metric, 0))
    (hZero : ∀ value : E, action (value, 0) = 0)
    (hEven : ∀ (value : E) (gauge : G), action (value, -gauge) = action (value, gauge)) :
    derivative = 0 := by
  let metricDerivative := derivative.comp (ContinuousLinearMap.inl Real E G)
  have hMetric : HasFDerivAt (fun value : E => action (value, 0)) metricDerivative metric := by
    simpa only [Function.comp_def, metricDerivative] using
      hDerivative.comp metric (hasFDerivAt_prodMk_left (𝕜 := Real) metric (0 : G))
  have hMetricFunction : (fun value : E => action (value, 0)) = (fun _ => (0 : Real)) := by
    funext value
    exact hZero value
  rw [hMetricFunction] at hMetric
  have hMetricDerivative : metricDerivative = 0 :=
    hMetric.unique (hasFDerivAt_const (x := metric) (c := (0 : Real)))
  let gaugeDerivative := derivative.comp (ContinuousLinearMap.inr Real E G)
  have hGauge : HasFDerivAt (fun gauge : G => action (metric, gauge)) gaugeDerivative 0 := by
    simpa only [Function.comp_def, gaugeDerivative] using
      hDerivative.comp (0 : G) (hasFDerivAt_prodMk_right metric (0 : G))
  have hNegMap : HasFDerivAt (fun gauge : G => -gauge)
      (-(ContinuousLinearMap.id Real G)) 0 :=
    (hasFDerivAt_id (0 : G)).neg
  have hGaugeNegZero : HasFDerivAt (fun gauge : G => action (metric, gauge))
      gaugeDerivative (-(0 : G)) := by
    simpa using hGauge
  have hGaugeNeg := hGaugeNegZero.comp (0 : G) hNegMap
  simp only [Function.comp_def] at hGaugeNeg
  have hGaugeFunction :
      (fun gauge : G => action (metric, -gauge)) =
        (fun gauge : G => action (metric, gauge)) := by
    funext gauge
    exact hEven metric gauge
  rw [hGaugeFunction] at hGaugeNeg
  have hGaugeUnique := hGaugeNeg.unique hGauge
  have hGaugeDerivative : gaugeDerivative = 0 := by
    apply ContinuousLinearMap.ext
    intro direction
    have hValue := congrArg (fun map : G →L[Real] Real => map direction) hGaugeUnique
    change gaugeDerivative (-direction) = gaugeDerivative direction at hValue
    rw [map_neg] at hValue
    change gaugeDerivative direction = 0
    linarith
  apply ContinuousLinearMap.ext
  rintro ⟨metricDirection, gaugeDirection⟩
  change derivative (metricDirection, gaugeDirection) = 0
  rw [show (metricDirection, gaugeDirection) =
      (metricDirection, (0 : G)) + ((0 : E), gaugeDirection) by ext <;> simp,
    map_add]
  change metricDerivative metricDirection + gaugeDerivative gaugeDirection = 0
  rw [hMetricDerivative, hGaugeDerivative]
  simp

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

local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _

local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

local instance : NormedAddCommGroup (C2Scalar period hPeriod) :=
  (canonicalPhysicalScalarC2JetCoreSubmodule period hPeriod).normedAddCommGroup

local instance : NormedSpace Real (C2Scalar period hPeriod) := inferInstance

local instance : CompleteSpace (C2Scalar period hPeriod) :=
  canonicalPhysicalScalarC2JetCoreCompleteSpace period hPeriod

variable (frame : SmoothD8Frame period hPeriod)
  (baseMetric : SmoothGeneralLorentzMetric period hPeriod)

local notation "MetricCore" =>
  GeneralMetricRelativeC2Core period hPeriod frame baseMetric

local notation "GaugeCore" => FiniteFrameAbelianGaugeC2Core period hPeriod frame

@[simp] theorem finiteFrameC2MobileMaxwellAction_zero
    (variation : MetricCore) :
    finiteFrameC2MobileMaxwellAction period hPeriod frame baseMetric (variation, 0) = 0 := by
  simp [finiteFrameC2MobileMaxwellAction, finiteFrameC2MobileMaxwellDensity]

theorem finiteFrameC2MobileMaxwellAction_neg
    (variation : MetricCore) (potential : GaugeCore) :
    finiteFrameC2MobileMaxwellAction period hPeriod frame baseMetric
        (variation, -potential) =
      finiteFrameC2MobileMaxwellAction period hPeriod frame baseMetric
        (variation, potential) := by
  simp only [finiteFrameC2MobileMaxwellAction, finiteFrameC2MobileMaxwellDensity,
    finiteFrameMaxwellPairingC0_neg]

/-- The joint metric-potential Maxwell derivative vanishes at zero potential. -/
theorem finiteFrameC2MobileMaxwellEuler_zero_potential
    (variation : MetricCore)
    (hVariation : variation ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame baseMetric) :
    finiteFrameC2MobileMaxwellEuler period hPeriod frame baseMetric (variation, 0) = 0 := by
  apply hasFDerivAt_eq_zero_of_fst_zero_snd_even
    (finiteFrameC2MobileMaxwellAction period hPeriod frame baseMetric) variation
  · exact finiteFrameC2MobileMaxwellAction_hasFDerivAt period hPeriod frame baseMetric
      (variation, 0) ⟨hVariation, Set.mem_univ _⟩
  · exact finiteFrameC2MobileMaxwellAction_zero period hPeriod frame baseMetric
  · exact finiteFrameC2MobileMaxwellAction_neg period hPeriod frame baseMetric

variable (plusFrame minusFrame : SmoothD8Frame period hPeriod)
  (plusBase minusBase : SmoothGeneralLorentzMetric period hPeriod)

local notation "PairInput" =>
  FiniteFramePairedC2MaxwellCore period hPeriod plusFrame minusFrame plusBase minusBase

local notation "PlusInput" =>
  GeneralMetricRelativeC2Core period hPeriod plusFrame plusBase ×
    FiniteFrameAbelianGaugeC2Core period hPeriod plusFrame

local notation "MinusInput" =>
  GeneralMetricRelativeC2Core period hPeriod minusFrame minusBase ×
    FiniteFrameAbelianGaugeC2Core period hPeriod minusFrame

/-- Both weighted Maxwell sectors have zero Euler functional at zero potential. -/
theorem finiteFramePairedC2MobileMaxwellEuler_zero_potentials
    (plusScale minusScale : Real)
    (plusVariation : GeneralMetricRelativeC2Core period hPeriod plusFrame plusBase)
    (minusVariation : GeneralMetricRelativeC2Core period hPeriod minusFrame minusBase)
    (hPlus : plusVariation ∈
      generalMetricRelativeC2VolumeDomain period hPeriod plusFrame plusBase)
    (hMinus : minusVariation ∈
      generalMetricRelativeC2VolumeDomain period hPeriod minusFrame minusBase) :
    finiteFramePairedC2MobileMaxwellEuler period hPeriod plusFrame minusFrame
        plusBase minusBase plusScale minusScale
        ((plusVariation, 0), (minusVariation, 0)) = 0 := by
  let center : PairInput := ((plusVariation, 0), (minusVariation, 0))
  have hPlusDerivative : HasFDerivAt
      (finiteFrameC2MobileMaxwellAction period hPeriod plusFrame plusBase) 0
      (plusVariation, 0) :=
    (finiteFrameC2MobileMaxwellAction_hasFDerivAt period hPeriod plusFrame plusBase
      (plusVariation, 0) ⟨hPlus, Set.mem_univ _⟩).congr_fderiv
        (finiteFrameC2MobileMaxwellEuler_zero_potential period hPeriod plusFrame plusBase
          plusVariation hPlus)
  have hMinusDerivative : HasFDerivAt
      (finiteFrameC2MobileMaxwellAction period hPeriod minusFrame minusBase) 0
      (minusVariation, 0) :=
    (finiteFrameC2MobileMaxwellAction_hasFDerivAt period hPeriod minusFrame minusBase
      (minusVariation, 0) ⟨hMinus, Set.mem_univ _⟩).congr_fderiv
        (finiteFrameC2MobileMaxwellEuler_zero_potential period hPeriod minusFrame minusBase
          minusVariation hMinus)
  have hFst : HasFDerivAt (fun input : PairInput => input.1)
      (ContinuousLinearMap.fst Real PlusInput MinusInput) center := by
    fun_prop
  have hSnd : HasFDerivAt (fun input : PairInput => input.2)
      (ContinuousLinearMap.snd Real PlusInput MinusInput) center := by
    fun_prop
  have hPlusOnPair : HasFDerivAt
      (fun input : PairInput => plusScale *
        finiteFrameC2MobileMaxwellAction period hPeriod plusFrame plusBase input.1)
      (0 : PairInput →L[Real] Real) center := by
    simpa [center] using
      (hPlusDerivative.comp center hFst).const_mul plusScale
  have hMinusOnPair : HasFDerivAt
      (fun input : PairInput => minusScale *
        finiteFrameC2MobileMaxwellAction period hPeriod minusFrame minusBase input.2)
      (0 : PairInput →L[Real] Real) center := by
    simpa [center] using
      (hMinusDerivative.comp center hSnd).const_mul minusScale
  have hActionZero : HasFDerivAt
      (finiteFramePairedC2MobileMaxwellAction period hPeriod plusFrame minusFrame
        plusBase minusBase plusScale minusScale) (0 : PairInput →L[Real] Real) center := by
    have hSum : HasFDerivAt
        ((fun input : PairInput => plusScale *
          finiteFrameC2MobileMaxwellAction period hPeriod plusFrame plusBase input.1) +
        (fun input : PairInput => minusScale *
          finiteFrameC2MobileMaxwellAction period hPeriod minusFrame minusBase input.2))
        (0 : PairInput →L[Real] Real) center :=
      (hPlusOnPair.add hMinusOnPair).congr_fderiv (by simp)
    apply hSum.congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun input => by
      rfl
  have hAction := finiteFramePairedC2MobileMaxwellAction_hasFDerivAt period hPeriod
    plusFrame minusFrame plusBase minusBase plusScale minusScale center
      ⟨⟨hPlus, Set.mem_univ _⟩, ⟨hMinus, Set.mem_univ _⟩⟩
  exact hAction.unique hActionZero

variable (geometry : GlobalCandidateAGeometry period hPeriod)
  (hRegular : ∀ point, Function.Bijective
    (intrinsicCandidateASylvesterAt period hPeriod geometry point))

local notation "PhysicalInput" =>
  FiniteFramePairedC2PhysicalCore period hPeriod geometry frame

local notation "PhysicalMaxwellInput" =>
  FiniteFramePairedC2MaxwellCore period hPeriod frame frame
    geometry.plusMetric geometry.plusMetric

/-- Adding Maxwell leaves the physical center Euler functional unchanged at zero potentials. -/
theorem finiteFramePairedC2PhysicalMaxwellEuler_zero_eq
    (hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric)
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    finiteFramePairedC2PhysicalMaxwellEuler period hPeriod geometry frame hRegular
        couplings interactionScale coefficients 0 =
      finiteFramePairedC2PhysicalEuler period hPeriod geometry frame hRegular
        couplings interactionScale coefficients 0 := by
  have hCenter := zero_mem_finiteFramePairedC2PhysicalDomain period hPeriod geometry frame
    hRegular hMinusCenter
  have hOld := finiteFramePairedC2PhysicalAction_hasFDerivAt period hPeriod geometry frame
    hRegular couplings interactionScale coefficients (0 : PhysicalInput) hCenter
  have hNew := finiteFramePairedC2PhysicalMaxwellAction_hasFDerivAt period hPeriod geometry frame
    hRegular couplings interactionScale coefficients (0 : PhysicalInput) hCenter
  let projection := fun input : PhysicalInput =>
    finiteFramePairedC2PhysicalMaxwellProjection period hPeriod geometry frame
      (finiteFramePairedC2PhysicalRecenter period hPeriod geometry frame input)
  have hProjection : DifferentiableAt Real projection 0 :=
    (finiteFramePairedC2PhysicalMaxwellProjection period hPeriod geometry frame).differentiableAt.comp
      (0 : PhysicalInput)
        (finiteFramePairedC2PhysicalRecenter_hasFDerivAt period hPeriod geometry frame 0).differentiableAt
  let maxwellCenter : PhysicalMaxwellInput :=
    (((0 : GeneralMetricRelativeC2Core period hPeriod frame geometry.plusMetric), 0),
      (finiteFramePairedC2MinusCenter period hPeriod geometry frame, 0))
  have hProjectionZero : projection 0 = maxwellCenter := by
    simp [projection, maxwellCenter]
  have hMaxwellCenter : maxwellCenter ∈
      finiteFramePairedC2MobileMaxwellDomain period hPeriod frame frame
        geometry.plusMetric geometry.plusMetric := by
    exact ⟨⟨zero_mem_generalMetricRelativeC2VolumeDomain period hPeriod frame
      geometry.plusMetric, Set.mem_univ _⟩, ⟨hMinusCenter, Set.mem_univ _⟩⟩
  have hOuterRaw :=
    finiteFramePairedC2MobileMaxwellAction_hasFDerivAt period hPeriod frame frame
      geometry.plusMetric geometry.plusMetric couplings.plusMaxwellScale
      couplings.minusMaxwellScale maxwellCenter hMaxwellCenter
  have hOuterEuler :
      finiteFramePairedC2MobileMaxwellEuler period hPeriod frame frame
        geometry.plusMetric geometry.plusMetric couplings.plusMaxwellScale
        couplings.minusMaxwellScale maxwellCenter = 0 := by
    simpa only [maxwellCenter] using
      finiteFramePairedC2MobileMaxwellEuler_zero_potentials period hPeriod frame frame
        geometry.plusMetric geometry.plusMetric couplings.plusMaxwellScale
        couplings.minusMaxwellScale 0
        (finiteFramePairedC2MinusCenter period hPeriod geometry frame)
        (zero_mem_generalMetricRelativeC2VolumeDomain period hPeriod frame
          geometry.plusMetric) hMinusCenter
  have hOuter : HasFDerivAt
      (finiteFramePairedC2MobileMaxwellAction period hPeriod frame frame
        geometry.plusMetric geometry.plusMetric couplings.plusMaxwellScale
        couplings.minusMaxwellScale) (0 : PhysicalMaxwellInput →L[Real] Real)
      (projection 0) := by
    rw [hProjectionZero]
    exact hOuterRaw.congr_fderiv hOuterEuler
  have hMaxwell : HasFDerivAt
      (fun input : PhysicalInput =>
        finiteFramePairedC2MobileMaxwellAction period hPeriod frame frame
          geometry.plusMetric geometry.plusMetric couplings.plusMaxwellScale
          couplings.minusMaxwellScale (projection input))
      (0 : PhysicalInput →L[Real] Real) 0 := by
    simpa only [Function.comp_def, ContinuousLinearMap.zero_comp] using
      hOuter.comp (0 : PhysicalInput) hProjection.hasFDerivAt
  have hSum : HasFDerivAt
      ((finiteFramePairedC2PhysicalAction period hPeriod geometry frame hRegular
        couplings interactionScale coefficients) +
      (fun input : PhysicalInput =>
        finiteFramePairedC2MobileMaxwellAction period hPeriod frame frame
          geometry.plusMetric geometry.plusMetric couplings.plusMaxwellScale
          couplings.minusMaxwellScale (projection input)))
      (finiteFramePairedC2PhysicalEuler period hPeriod geometry frame hRegular
        couplings interactionScale coefficients 0) 0 :=
    (hOld.add hMaxwell).congr_fderiv (by simp)
  apply hNew.unique
  apply hSum.congr_of_eventuallyEq
  exact Filter.Eventually.of_forall fun input => by
    rfl

/-- The residual characterization from the finite physical center survives the
Maxwell augmentation at the zero-potential background. -/
theorem finiteFramePairedC2PhysicalMaxwellEuler_zero_iff_residual_and_globalDeDonder
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
    finiteFramePairedC2PhysicalMaxwellEuler period hPeriod geometry frame hFiniteRegular
        couplings interactionScale coefficients 0 = 0 ↔
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
  have hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric := by
    rw [hCenter]
    exact hShift
  rw [finiteFramePairedC2PhysicalMaxwellEuler_zero_eq period hPeriod frame geometry
    hFiniteRegular hMinusCenter couplings interactionScale coefficients]
  exact finiteFramePairedC2PhysicalEuler_zero_iff_residual_and_globalDeDonder period hPeriod
    plusBase minusBase hPlusCanonicalVolume hMinusCanonicalVolume hChart frame hShift hZero
      couplings interactionScale coefficients

end
end P0EFTJanusFiniteFramePairedC2PhysicalMaxwellCenterEuler4D
end JanusFormal
