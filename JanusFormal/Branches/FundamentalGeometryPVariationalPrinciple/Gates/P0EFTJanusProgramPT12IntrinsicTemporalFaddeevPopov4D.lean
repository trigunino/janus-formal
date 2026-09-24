import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicTemporalHolonomicPatch4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicTemporalPairedGhost4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12FrameFreeCurrentPullback4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12LorenzLocalDensity4D

/-! The actual paired Abelian FP acts as the negative second time derivative on periodic
temporal ghosts. The current and density are computed in the same genuine holonomic patch. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicTemporalFaddeevPopov4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusGlobalHolonomicScalarAction4D
open P0EFTJanusMappingTorusHolonomicCoordinateEquiv4D
open P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolume4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusLocalAbelianLorenzCodifferential4D
open P0EFTJanusMappingTorusAbelianLorenzCodifferentialTransition4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarLocalVolumeTransport4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPT12FrameFreeCurrentPullback4D
open P0EFTJanusProgramPT12LorenzLocalDensity4D
open P0EFTJanusProgramPT12IntrinsicTemporalLocalDivergence4D
open P0EFTJanusProgramPT12IntrinsicTemporalHolonomicPatch4D
open P0EFTJanusProgramPT12IntrinsicTemporalPairedGhost4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Vector4 := Fin 4 → Real
private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

variable (profiles : GlobalPairedAbelianLorenzCoordinateIndex → Real → Real)
  (hSmooth : ∀ index, ContDiff Real ∞ (profiles index))
  (hPeriodic : ∀ index, Function.Periodic (profiles index) period)

theorem periodicTemporalPairedGhost_localRaised
    (sector : Sector) (component : Fin 2) (shift : Real) (pole : StandardSphere) (coordinate : Vector4) :
    localRaisedAbelianGaugePotential period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      (exactGaugePotential period hPeriod
        (periodicTemporalPairedGhost period hPeriod profiles hSmooth hPeriodic sector))
      component (intrinsicTemporalHolonomicPatch period hPeriod shift pole) coordinate =
    (-deriv (profiles (sector, component)) (coordinate 0 + shift)) • Pi.single (0 : Fin 4) 1 := by
  let patch := intrinsicTemporalHolonomicPatch period hPeriod shift pole
  have hInjective : Function.Injective
      (mfderiv (modelWithCornersSelf Real Vector4) coverModelWithCorners patch.coordinateMap coordinate) := by
    rw [← frameFreeCoordinateDerivativeEquiv_coe]
    exact (frameFreeCoordinateDerivativeEquiv period hPeriod patch coordinate).injective
  apply hInjective
  rw [coordinateMap_mfderiv_localRaisedAbelianGaugePotential]
  change inverseMetricSharp period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod)
    (patch.coordinateMap coordinate)
    ((exactGaugePotential period hPeriod
      (periodicTemporalPairedGhost period hPeriod profiles hSmooth hPeriodic sector)).toFun component
        (patch.coordinateMap coordinate)) = _
  dsimp only [patch]
  rw [intrinsicTemporalHolonomicPatch_mfderiv, map_smul, holonomicCoordinateEquiv_symm_single]
  rw [intrinsicTemporalHolonomicPatch_coordinateMap, periodicTemporalPairedGhost_intrinsic_sharp,
    holonomicCoordinateEquiv_symm_time]
  simp [tangentCoordinate]

theorem periodicTemporalPairedGhost_faddeevPopov
    (sector : Sector) (component : Fin 2) (shift : Real) (pole : StandardSphere) (coordinate : Vector4) :
    globalGeneralMetricAbelianFaddeevPopov period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      (periodicTemporalPairedGhost period hPeriod profiles hSmooth hPeriodic sector)
      ((intrinsicTemporalHolonomicPatch period hPeriod shift pole).coordinateMap coordinate) component =
    -deriv (deriv (profiles (sector, component))) (coordinate 0 + shift) := by
  change globalGeneralMetricAbelianLorenzValue period hPeriod
    (intrinsicSmoothGeneralLorentzMetric period hPeriod)
    (exactGaugePotential period hPeriod
      (periodicTemporalPairedGhost period hPeriod profiles hSmooth hPeriodic sector)) component _ = _
  rw [globalGeneralMetricAbelianLorenzValue_eq_local, localLorenz_eq_densityDivergence]
  have hDensity : localMetricVolumeFactor period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      (intrinsicTemporalHolonomicPatch period hPeriod shift pole) = intrinsicTemporalCoordinateDensity := by
    funext point
    exact intrinsicTemporalHolonomicPatch_volumeFactor period hPeriod shift pole point
  have hCurrent : localRaisedAbelianGaugePotential period hPeriod
      (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      (exactGaugePotential period hPeriod
        (periodicTemporalPairedGhost period hPeriod profiles hSmooth hPeriodic sector))
      component (intrinsicTemporalHolonomicPatch period hPeriod shift pole) =
      fun point => (-deriv (profiles (sector, component)) (point 0 + shift)) • Pi.single (0 : Fin 4) 1 := by
    funext point
    exact periodicTemporalPairedGhost_localRaised period hPeriod profiles hSmooth hPeriodic
      sector component shift pole point
  rw [hDensity, hCurrent]
  have hC2 : ContDiff Real 2 (fun time => profiles (sector, component) (time + shift)) :=
    ((hSmooth (sector, component)).of_le (by decide)).comp (contDiff_id.add contDiff_const)
  have h := intrinsicTemporalLocalDivergence_eq_negative_second_deriv
    (fun time => profiles (sector, component) (time + shift)) hC2 coordinate
  have hShift : deriv (fun time => profiles (sector, component) (time + shift)) =
      fun time => deriv (profiles (sector, component)) (time + shift) := by
    funext time
    exact deriv_comp_add_const _ shift time
  rw [hShift] at h
  simpa only [deriv_comp_add_const] using h

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicTemporalFaddeevPopov4D
