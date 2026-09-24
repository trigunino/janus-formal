import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicTemporalFaddeevPopov4D

/-! Global temporal FP formula on the actual quotient. The local computation
extends through the genuine stereographic cover. No spectral completeness or
Fredholm property is asserted. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicTemporalFPGlobal4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusHolonomicCoordinateEquiv4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarLocalVolumeTransport4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPT12IntrinsicTemporalGradient4D
open P0EFTJanusProgramPT12IntrinsicTemporalHolonomicPatch4D
open P0EFTJanusProgramPT12IntrinsicTemporalPairedGhost4D
open P0EFTJanusProgramPT12IntrinsicTemporalFaddeevPopov4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev Cover := MappingTorusCover (reflectedSphereData period hPeriod)
private abbrev QuotientSpace := MappingTorus (reflectedSphereData period hPeriod)
private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1
local instance : ChartedSpace CoverModel (QuotientSpace period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (QuotientSpace period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

theorem exists_intrinsicTemporalHolonomicPatch (point : QuotientSpace period hPeriod) :
    ∃ (shift : Real) (pole : StandardSphere) (coordinate : Fin 4 → Real),
      (intrinsicTemporalHolonomicPatch period hPeriod shift pole).coordinateMap coordinate = point := by
  obtain ⟨shift, pole, source, hSource⟩ := exists_shiftedStereographicChart_mem period hPeriod point
  refine ⟨shift, pole, holonomicCoordinateEquiv
    (canonicalInteriorStereographicCoordinateInclusion period source), ?_⟩
  rw [intrinsicTemporalHolonomicPatch_coordinateMap, holonomicCoordinateEquiv.symm_apply_apply,
    shiftedStereographicPhysicalMapAmbient_agrees]
  exact hSource

theorem temporalProfile_deriv_periodic (profile : Real → Real)
    (hPeriodic : Function.Periodic profile period) :
    Function.Periodic (deriv profile) period := by
  have hShift : (fun time => profile (time + period)) = profile := funext hPeriodic
  intro time
  have h := congrArg (fun function : Real → Real => deriv function time) hShift
  simpa only [deriv_comp_add_const] using h

theorem temporalNegativeSecondDerivative_contDiff (profile : Real → Real)
    (hSmooth : ContDiff Real ∞ profile) :
    ContDiff Real ∞ (fun time => -deriv (deriv profile) time) :=
  ((contDiff_infty_iff_deriv.mp (contDiff_infty_iff_deriv.mp hSmooth).2).2).neg

theorem temporalNegativeSecondDerivative_periodic (profile : Real → Real)
    (hPeriodic : Function.Periodic profile period) :
    Function.Periodic (fun time => -deriv (deriv profile) time) period := by
  intro time
  exact congrArg Neg.neg (temporalProfile_deriv_periodic period (deriv profile)
    (temporalProfile_deriv_periodic period profile hPeriodic) time)

def periodicTemporalWaveScalar (profile : Real → Real)
    (hSmooth : ContDiff Real ∞ profile) (hPeriodic : Function.Periodic profile period) :
    SmoothScalarField period hPeriod :=
  periodicTemporalScalar period hPeriod (fun time => -deriv (deriv profile) time)
    (temporalNegativeSecondDerivative_contDiff profile hSmooth)
    (temporalNegativeSecondDerivative_periodic period profile hPeriodic)

variable (profiles : GlobalPairedAbelianLorenzCoordinateIndex → Real → Real)
  (hSmooth : ∀ index, ContDiff Real ∞ (profiles index))
  (hPeriodic : ∀ index, Function.Periodic (profiles index) period)

/-- Pointwise identity on the whole quotient, with a genuine descended right-hand side. -/
theorem periodicTemporalPairedGhost_faddeevPopov_global
    (sector : Sector) (component : Fin 2) (point : QuotientSpace period hPeriod) :
    globalGeneralMetricAbelianFaddeevPopov period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (periodicTemporalPairedGhost period hPeriod profiles hSmooth hPeriodic sector)
        point component =
      periodicTemporalWaveScalar period hPeriod (profiles (sector, component))
        (hSmooth (sector, component)) (hPeriodic (sector, component)) point := by
  obtain ⟨shift, pole, coordinate, hPoint⟩ := exists_intrinsicTemporalHolonomicPatch period hPeriod point
  rw [← hPoint, periodicTemporalPairedGhost_faddeevPopov,
    intrinsicTemporalHolonomicPatch_coordinateMap]
  simp only [periodicTemporalWaveScalar, periodicTemporalScalar_stereographic,
    holonomicCoordinateEquiv_symm_time]

/-- The same identity at every cover representative, without selecting a fundamental strip. -/
theorem periodicTemporalPairedGhost_faddeevPopov_mk
    (sector : Sector) (component : Fin 2) (point : Cover period hPeriod) :
    globalGeneralMetricAbelianFaddeevPopov period hPeriod
        (intrinsicSmoothGeneralLorentzMetric period hPeriod)
        (periodicTemporalPairedGhost period hPeriod profiles hSmooth hPeriodic sector)
        (mappingTorusMk (reflectedSphereData period hPeriod) point) component =
      -deriv (deriv (profiles (sector, component))) point.time :=
  periodicTemporalPairedGhost_faddeevPopov_global period hPeriod profiles hSmooth hPeriodic
    sector component (mappingTorusMk (reflectedSphereData period hPeriod) point)

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicTemporalFPGlobal4D
