import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFrameRegularC2PhysicalMetricStationarityResidual4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusFiniteFramePairedC2PhysicalEulerThreeBlockSplit4D

/-! # Reduction of the finite physical field equations at the center -/

namespace JanusFormal
namespace P0EFTJanusFiniteFramePairedC2PhysicalFieldsCenterReduction4D

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
open P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameSylvesterRegularity4D
open P0EFTJanusFiniteFrameC2AbelianOperators4D
open P0EFTJanusFiniteFrameC2AbelianBRSTAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTGaugeAction4D
open P0EFTJanusFiniteFramePairedC2FullBRSTEulerDecomposition4D
open P0EFTJanusFiniteFramePairedC2AbelianBRSTEulerSectors4D
open P0EFTJanusFiniteFramePairedC2PhysicalAction4D
open P0EFTJanusFiniteFramePairedC2PhysicalEulerStationaritySplit4D
open P0EFTJanusFiniteFramePairedC2PhysicalEulerThreeBlockSplit4D
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

/-- The finite Lorenz expression is odd in the Abelian potential. -/
theorem finiteFrameC2AbelianLorenzComponentExpression_neg
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (metric : GeneralMetricRelativeC2Core period hPeriod frame baseMetric)
    (potential : FiniteFrameAbelianGaugeC2Core period hPeriod frame)
    (component : Fin 2) :
    finiteFrameC2AbelianLorenzComponentExpression period hPeriod frame baseMetric metric
        (-potential) component =
      -finiteFrameC2AbelianLorenzComponentExpression period hPeriod frame baseMetric metric
        potential component := by
  simp [finiteFrameC2AbelianLorenzComponentExpression,
    finiteFrameC2AbelianLorenzExpression]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro first _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro second _
  ring

/-- The finite Abelian Faddeev--Popov expression is odd in the ghost. -/
theorem finiteFrameC2AbelianFPComponentExpression_neg
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (metric : GeneralMetricRelativeC2Core period hPeriod frame baseMetric)
    (ghost : FiniteFrameAbelianGhostC2Core period hPeriod)
    (component : Fin 2) :
    finiteFrameC2AbelianFPComponentExpression period hPeriod frame baseMetric metric
        (-ghost) component =
      -finiteFrameC2AbelianFPComponentExpression period hPeriod frame baseMetric metric
        ghost component := by
  simp [finiteFrameC2AbelianFPComponentExpression,
    finiteFrameC2AbelianFPExpression]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro first _
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro second _
  ring

/-- At fixed metric, simultaneous sign reversal of every Abelian field leaves
the finite BRST action unchanged. -/
theorem finiteFrameC2AbelianBRSTAction_neg_fields
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (metric : GeneralMetricRelativeC2Core period hPeriod frame baseMetric)
    (fields : FiniteFrameAbelianGaugeC2Core period hPeriod frame ×
      FiniteFrameAbelianNonminimalC2Core period hPeriod) :
    finiteFrameC2AbelianBRSTAction period hPeriod frame baseMetric (metric, -fields) =
      finiteFrameC2AbelianBRSTAction period hPeriod frame baseMetric (metric, fields) := by
  simp [finiteFrameC2AbelianBRSTAction, finiteFrameC2AbelianBRSTDensity,
    finiteFrameC2AbelianLorenzComponentExpression_neg,
    finiteFrameC2AbelianFPComponentExpression_neg]

/-- The actual Abelian Euler map has zero field restriction when all Abelian
fields vanish, for every admissible metric. -/
theorem finiteFrameC2AbelianBRSTEuler_zero_fields_apply_fields
    (frame : SmoothD8Frame period hPeriod)
    (baseMetric : SmoothGeneralLorentzMetric period hPeriod)
    (metric : GeneralMetricRelativeC2Core period hPeriod frame baseMetric)
    (hMetric : metric ∈ generalMetricRelativeC2OpenDomain period hPeriod frame baseMetric)
    (fields : FiniteFrameAbelianGaugeC2Core period hPeriod frame ×
      FiniteFrameAbelianNonminimalC2Core period hPeriod) :
    finiteFrameC2AbelianBRSTEuler period hPeriod frame baseMetric (metric, 0)
        (0, fields) = 0 := by
  let Metric := GeneralMetricRelativeC2Core period hPeriod frame baseMetric
  let Fields := FiniteFrameAbelianGaugeC2Core period hPeriod frame ×
    FiniteFrameAbelianNonminimalC2Core period hPeriod
  let action := finiteFrameC2AbelianBRSTAction period hPeriod frame baseMetric
  let derivative := finiteFrameC2AbelianBRSTEuler period hPeriod frame baseMetric (metric, 0)
  have hAction : HasFDerivAt action derivative (metric, (0 : Fields)) := by
    exact finiteFrameC2AbelianBRSTAction_hasFDerivAt period hPeriod frame baseMetric
      (metric, (0 : Fields)) ⟨hMetric, Set.mem_univ _⟩
  have hRestricted : HasFDerivAt (fun current : Fields => action (metric, current))
      (derivative.comp (ContinuousLinearMap.inr Real Metric Fields)) 0 := by
    simpa only [Function.comp_def] using
      hAction.comp (0 : Fields) (hasFDerivAt_prodMk_right metric (0 : Fields))
  have hNegMap : HasFDerivAt (fun current : Fields => -current)
      (-(ContinuousLinearMap.id Real Fields)) 0 :=
    (hasFDerivAt_id (0 : Fields)).neg
  have hRestrictedNegZero : HasFDerivAt (fun current : Fields => action (metric, current))
      (derivative.comp (ContinuousLinearMap.inr Real Metric Fields)) (-(0 : Fields)) := by
    simpa using hRestricted
  have hNeg := hRestrictedNegZero.comp (0 : Fields) hNegMap
  simp only [Function.comp_def] at hNeg
  have hFunctions :
      (fun current : Fields => action (metric, -current)) =
        (fun current : Fields => action (metric, current)) := by
    funext current
    exact finiteFrameC2AbelianBRSTAction_neg_fields period hPeriod frame baseMetric metric current
  rw [hFunctions] at hNeg
  have hMaps := hNeg.unique hRestricted
  have hApply := DFunLike.congr_fun hMaps fields
  change derivative (0, -fields) = derivative (0, fields) at hApply
  have hPairNeg : ((0 : Metric), -fields) = -((0 : Metric), fields) := by simp
  rw [hPairNeg, map_neg] at hApply
  have : derivative (0, fields) = 0 := by linarith
  exact this

/-- The paired Abelian Euler map also vanishes on every pure field direction
at zero Abelian fields. -/
theorem finiteFramePairedC2AbelianBRSTEuler_zero_fields_apply_fields
    (plusFrame minusFrame : SmoothD8Frame period hPeriod)
    (plusMetric minusMetric : SmoothGeneralLorentzMetric period hPeriod)
    (plusBase : GeneralMetricRelativeC2Core period hPeriod plusFrame plusMetric)
    (minusBase : GeneralMetricRelativeC2Core period hPeriod minusFrame minusMetric)
    (hPlus : plusBase ∈
      generalMetricRelativeC2OpenDomain period hPeriod plusFrame plusMetric)
    (hMinus : minusBase ∈
      generalMetricRelativeC2OpenDomain period hPeriod minusFrame minusMetric)
    (fields : FiniteFramePairedC2AbelianGaugeFields period hPeriod plusFrame minusFrame) :
    finiteFramePairedC2AbelianBRSTEuler period hPeriod plusFrame minusFrame plusMetric
        minusMetric ((plusBase, 0), (minusBase, 0))
        ((0, fields.1), (0, fields.2)) = 0 := by
  rw [finiteFramePairedC2AbelianBRSTEuler_eq_sector_eulers period hPeriod plusFrame
    minusFrame plusMetric minusMetric ((plusBase, 0), (minusBase, 0))
      ⟨⟨hPlus, Set.mem_univ _⟩, ⟨hMinus, Set.mem_univ _⟩⟩]
  simp only [add_apply, ContinuousLinearMap.comp_apply]
  change
    finiteFrameC2AbelianBRSTEuler period hPeriod plusFrame plusMetric (plusBase, 0)
        (0, fields.1) +
      finiteFrameC2AbelianBRSTEuler period hPeriod minusFrame minusMetric (minusBase, 0)
        (0, fields.2) = 0
  rw [finiteFrameC2AbelianBRSTEuler_zero_fields_apply_fields period hPeriod plusFrame
      plusMetric plusBase hPlus fields.1,
    finiteFrameC2AbelianBRSTEuler_zero_fields_apply_fields period hPeriod minusFrame
      minusMetric minusBase hMinus fields.2]
  exact add_zero 0

/-- At the physical center, the entire Abelian field block of the actual
finite Euler map vanishes. -/
theorem finiteFramePairedC2PhysicalAbelianFieldsEuler_zero
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point))
    (hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric)
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    finiteFramePairedC2PhysicalAbelianFieldsEuler period hPeriod geometry frame hRegular
        couplings interactionScale coefficients 0 = 0 := by
  apply ContinuousLinearMap.ext
  intro fields
  rw [finiteFramePairedC2PhysicalAbelianFieldsEuler_apply period hPeriod geometry frame
    hRegular couplings interactionScale coefficients 0
      (zero_mem_finiteFramePairedC2PhysicalDomain period hPeriod geometry frame hRegular
        hMinusCenter) fields]
  simp only [finiteFramePairedC2PhysicalRecenter_zero,
    finiteFramePairedC2FullBRSTGaugeAbelianProjection_apply]
  change
    finiteFramePairedC2AbelianBRSTEuler period hPeriod frame frame geometry.plusMetric
        geometry.plusMetric
        ((0, 0), (finiteFramePairedC2MinusCenter period hPeriod geometry frame, 0))
        ((0, fields.1), (0, fields.2)) = 0
  exact finiteFramePairedC2AbelianBRSTEuler_zero_fields_apply_fields period hPeriod frame frame
    geometry.plusMetric geometry.plusMetric 0
    (finiteFramePairedC2MinusCenter period hPeriod geometry frame)
    (zero_mem_generalMetricRelativeC2OpenDomain period hPeriod frame geometry.plusMetric)
    hMinusCenter.1 fields

/-- Consequently, stationarity of all finite physical gauge fields at the
center is exactly the remaining diffeomorphism nonminimal equation. -/
theorem finiteFramePairedC2PhysicalFieldsEuler_zero_iff_diffeomorphism
    (geometry : GlobalCandidateAGeometry period hPeriod)
    (frame : SmoothD8Frame period hPeriod)
    (hRegular : ∀ point, Function.Bijective
      (intrinsicCandidateASylvesterAt period hPeriod geometry point))
    (hMinusCenter : finiteFramePairedC2MinusCenter period hPeriod geometry frame ∈
      generalMetricRelativeC2VolumeDomain period hPeriod frame geometry.plusMetric)
    (couplings : GlobalCandidateAActionCouplings)
    (interactionScale : Real) (coefficients : PotentialCoefficients) :
    finiteFramePairedC2PhysicalFieldsEuler period hPeriod geometry frame hRegular couplings
        interactionScale coefficients 0 = 0 ↔
      finiteFramePairedC2PhysicalDiffeomorphismFieldsEuler period hPeriod geometry frame hRegular
        couplings interactionScale coefficients 0 = 0 := by
  rw [finiteFramePairedC2PhysicalFieldsEuler_eq_zero_iff_gauge_restrictions period hPeriod
    geometry frame hRegular couplings interactionScale coefficients 0,
    finiteFramePairedC2PhysicalAbelianFieldsEuler_zero period hPeriod geometry frame hRegular
      hMinusCenter couplings interactionScale coefficients]
  simp

end
end P0EFTJanusFiniteFramePairedC2PhysicalFieldsCenterReduction4D
end JanusFormal
