import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameC2DiffeomorphismBRSTCenterEuler4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedDiffeomorphismBRSTEulerSectors4D

/-! # Paired and physical diffeomorphism Euler map at the center -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalDiffeomorphismCenterEuler4D

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 1200000
set_option maxRecDepth 8000

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusGeneralLorentzTensor4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D
open P0EFTJanusProgramPGlobalCandidateAGeometry4D
open P0EFTJanusProgramPGlobalCovariantAction4D
open P0EFTJanusProgramPGeneralMetricC2OpenDomain4D
open P0EFTJanusProgramPGeneralMetricC2VolumeDensity4D
open P0EFTJanusProgramPCandidateADiagonalDiffeomorphismKineticAdjointBridge4D
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusFiniteFrameDiffeomorphismC2Core4D
open P0EFTJanusFiniteFrameC2MetricTensorTrace4D
open P0EFTJanusFiniteFrameC2DeDonder4D
open P0EFTJanusFiniteFrameC2DiffeomorphismBRSTAction4D
open P0EFTJanusFiniteFramePairedDiffeomorphismBRSTAction4D
open P0EFTJanusFiniteFramePairedDiffeomorphismBRSTEulerSectors4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalEulerStationaritySplit4D
open P0EFTJanusFiniteFramePairedC2PhysicalEulerThreeBlockSplit4D
open P0EFTJanusFiniteFrameC2DiffeomorphismBRSTCenterEuler4D
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

/-- The finite De Donder coefficient vanishes on the zero tensor. -/
theorem finiteFrameC2DeDonderCoefficient_zero_tensor
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (metric : GeneralMetricRelativeC2Core period hPeriod frame baseMetric)
    (index : Fin frame.count) :
    finiteFrameC2DeDonderCoefficient period hPeriod frame baseMetric index (metric, 0) = 0 := by
  simp [finiteFrameC2DeDonderCoefficient,
    finiteFrameMetricTensorTraceGradientC0,
    finiteFrameMetricTensorTraceC2]

/-- Hence the auxiliary-field pairing vanishes on the zero tensor. -/
theorem finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction_zero_tensor
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (metric : GeneralMetricRelativeC2Core period hPeriod frame baseMetric)
    (field : FiniteFrameDiffeomorphismC2Core period hPeriod frame) :
    finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction period hPeriod frame baseMetric
        metric 0 field = 0 := by
  simp [finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction,
    finiteFrameC2DiffeomorphismBRSTNakanishiLautrupDensity,
    finiteFrameC2DeDonderCoefficient_zero_tensor]

@[simp] theorem finiteFrameDiffeomorphismNonminimalC2Transition_fst
    (source target : SmoothD8Frame period hPeriod)
    (targetReference : SmoothGeneralLorentzMetric period hPeriod)
    (fields : FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod source) :
    (finiteFrameDiffeomorphismNonminimalC2Transition period hPeriod source target
      targetReference fields).1 =
      finiteFrameDiffeomorphismC2Transition period hPeriod source target targetReference
        fields.1 := by
  rfl

/-- At zero nonminimal fields, the paired Euler map is the weighted sum of
the two transported auxiliary-field De Donder pairings. -/
theorem finiteFramePairedDiffeomorphismBRSTEuler_zero_nonminimal_apply
    (source plusFrame minusFrame : SmoothD8Frame period hPeriod)
    (plusMetric minusMetric : SmoothGeneralLorentzMetric period hPeriod)
    (plusBase : GeneralMetricRelativeC2Core period hPeriod plusFrame plusMetric)
    (minusBase : GeneralMetricRelativeC2Core period hPeriod minusFrame minusMetric)
    (hPlus : plusBase ∈
      generalMetricRelativeC2VolumeDomain period hPeriod plusFrame plusMetric)
    (hMinus : minusBase ∈
      generalMetricRelativeC2VolumeDomain period hPeriod minusFrame minusMetric)
    (couplings : GlobalCandidateAActionCouplings)
    (fields : FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod source) :
    finiteFramePairedDiffeomorphismBRSTEuler period hPeriod source plusFrame minusFrame
        plusMetric minusMetric couplings ((plusBase, minusBase), 0) (0, fields) =
      candidateAPlusEinsteinKineticWeight couplings *
          finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction period hPeriod plusFrame
            plusMetric plusBase plusBase
            (finiteFrameDiffeomorphismNonminimalC2Transition period hPeriod source plusFrame
              plusMetric fields).1 +
        candidateAMinusEinsteinKineticWeight couplings *
          finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction period hPeriod minusFrame
            minusMetric minusBase minusBase
            (finiteFrameDiffeomorphismNonminimalC2Transition period hPeriod source minusFrame
              minusMetric fields).1 := by
  rw [finiteFramePairedDiffeomorphismBRSTEuler_eq_sector_eulers period hPeriod source
    plusFrame minusFrame plusMetric minusMetric couplings ((plusBase, minusBase), 0)
      ⟨⟨hPlus, hMinus⟩, Set.mem_univ _⟩]
  simp only [add_apply, smul_eq_mul, smul_apply,
    ContinuousLinearMap.comp_apply, finiteFramePairedDiffeomorphismBRSTPlusInput_apply,
    finiteFramePairedDiffeomorphismBRSTMinusInput_apply,
    finiteFrameSharedMetricDiffeomorphismBRSTInput_apply, map_zero]
  change
    candidateAPlusEinsteinKineticWeight couplings *
          finiteFrameC2DiffeomorphismBRSTEuler period hPeriod plusFrame plusMetric
            (plusBase, (plusBase, 0))
            (0, (0, finiteFrameDiffeomorphismNonminimalC2Transition period hPeriod source
              plusFrame plusMetric fields)) +
        candidateAMinusEinsteinKineticWeight couplings *
          finiteFrameC2DiffeomorphismBRSTEuler period hPeriod minusFrame minusMetric
            (minusBase, (minusBase, 0))
            (0, (0, finiteFrameDiffeomorphismNonminimalC2Transition period hPeriod source
              minusFrame minusMetric fields)) = _
  rw [finiteFrameC2DiffeomorphismBRSTEuler_zero_nonminimal_apply period hPeriod plusFrame
      plusMetric plusBase plusBase hPlus
      (finiteFrameDiffeomorphismNonminimalC2Transition period hPeriod source plusFrame
        plusMetric fields),
    finiteFrameC2DiffeomorphismBRSTEuler_zero_nonminimal_apply period hPeriod minusFrame
      minusMetric minusBase minusBase hMinus
      (finiteFrameDiffeomorphismNonminimalC2Transition period hPeriod source minusFrame
        minusMetric fields)]

/-- At the physical center, only the minus-sector De Donder pairing survives. -/
theorem finiteFramePairedC2PhysicalDiffeomorphismFieldsEuler_zero_apply
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point))
    (hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric)
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients)
    (fields : FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame) :
    finiteFramePairedC2PhysicalDiffeomorphismFieldsEuler period hPeriod geometry frame
        hRegular couplings interactionScale coefficients 0 fields =
      candidateAMinusEinsteinKineticWeight couplings *
        finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction period hPeriod frame
          geometry.plusMetric
          (finiteFramePairedC2MinusCenter period hPeriod geometry frame)
          (finiteFramePairedC2MinusCenter period hPeriod geometry frame)
          (finiteFrameDiffeomorphismC2Transition period hPeriod frame frame
            geometry.plusMetric fields.1) := by
  rw [finiteFramePairedC2PhysicalDiffeomorphismFieldsEuler_apply period hPeriod geometry
    frame hRegular couplings interactionScale coefficients 0
      (zero_mem_finiteFramePairedC2PhysicalDomain period hPeriod geometry frame hRegular
        hMinusCenter) fields]
  simp only [finiteFramePairedC2PhysicalRecenter_zero,
    finiteFramePairedC2FullBRSTGaugeDiffeomorphismProjection_apply]
  change
    finiteFramePairedDiffeomorphismBRSTEuler period hPeriod frame frame frame
        geometry.plusMetric geometry.plusMetric couplings
        ((0, finiteFramePairedC2MinusCenter period hPeriod geometry frame), 0)
        (0, fields) = _
  rw [finiteFramePairedDiffeomorphismBRSTEuler_zero_nonminimal_apply period hPeriod
    frame frame frame geometry.plusMetric geometry.plusMetric 0
    (finiteFramePairedC2MinusCenter period hPeriod geometry frame)
    (zero_mem_generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric)
    hMinusCenter couplings fields,
    finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction_zero_tensor period hPeriod frame
      geometry.plusMetric 0]
  simp

/-- The remaining physical field equation is exactly annihilation of the
transported finite De Donder pairing on every auxiliary-field coefficient. -/
theorem finiteFramePairedC2PhysicalDiffeomorphismFieldsEuler_zero_iff_deDonderPairing
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point))
    (hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric)
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    finiteFramePairedC2PhysicalDiffeomorphismFieldsEuler period hPeriod geometry frame
        hRegular couplings interactionScale coefficients 0 = 0 ↔
      ∀ field : FiniteFrameDiffeomorphismC2Core period hPeriod frame,
        finiteFrameC2DiffeomorphismBRSTNakanishiLautrupAction period hPeriod frame
          geometry.plusMetric
          (finiteFramePairedC2MinusCenter period hPeriod geometry frame)
          (finiteFramePairedC2MinusCenter period hPeriod geometry frame)
          (finiteFrameDiffeomorphismC2Transition period hPeriod frame frame
            geometry.plusMetric field) = 0 := by
  constructor
  · intro hEuler field
    have hApply := DFunLike.congr_fun hEuler
      ((field, 0) : FiniteFrameDiffeomorphismNonminimalC2Core period hPeriod frame)
    rw [finiteFramePairedC2PhysicalDiffeomorphismFieldsEuler_zero_apply period hPeriod
      geometry frame hRegular hMinusCenter couplings interactionScale coefficients] at hApply
    exact (mul_eq_zero.mp hApply).resolve_left
      (candidateAMinusEinsteinKineticWeight_ne_zero couplings)
  · intro hPairing
    apply ContinuousLinearMap.ext
    intro fields
    rw [finiteFramePairedC2PhysicalDiffeomorphismFieldsEuler_zero_apply period hPeriod
      geometry frame hRegular hMinusCenter couplings interactionScale coefficients,
      hPairing fields.1]
    simp

end
end P0EFTJanusFiniteFramePairedC2PhysicalDiffeomorphismCenterEuler4D
end JanusFormal
