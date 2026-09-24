import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12IntrinsicTemporalGradient4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalAbelianFaddeevPopovGreenStokes4D

/-! Four genuine periodic ghost components and their exact intrinsic raised differential. -/
namespace JanusFormal.P0EFTJanusProgramPT12IntrinsicTemporalPairedGhost4D
set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusIntrinsicLorentzScalarAction4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusCanonicalPhysicalScalarLocalVolumeTransport4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalAbelianLorenzGraphRiesz4D
open P0EFTJanusProgramPGlobalAbelianBRSTOffShellGraphC2Chart4D
open P0EFTJanusProgramPGlobalAbelianFaddeevPopovGreenStokes4D
open P0EFTJanusProgramPT12IntrinsicTemporalGradient4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)
private abbrev Space3 := EuclideanSpace Real (Fin 3)
private abbrev Coordinates := Space3 × Real
private abbrev StandardSphere := Metric.sphere (0 : EuclideanR4) 1
local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

variable (profiles : GlobalPairedAbelianLorenzCoordinateIndex → Real → Real)
  (hSmooth : ∀ index, ContDiff Real ∞ (profiles index))
  (hPeriodic : ∀ index, Function.Periodic (profiles index) period)

def periodicTemporalPairedGhost : GlobalPairedGaugeLieSmooth period hPeriod :=
  globalPairedGaugeLieSmoothOfComponents period hPeriod
    (fun index => periodicTemporalScalar period hPeriod (profiles index) (hSmooth index) (hPeriodic index))

@[simp] theorem periodicTemporalPairedGhost_component
    (sector : Sector) (component : Fin 2) :
    ghostComponent period hPeriod
      (periodicTemporalPairedGhost period hPeriod profiles hSmooth hPeriodic sector) component =
    periodicTemporalScalar period hPeriod (profiles (sector, component))
      (hSmooth (sector, component)) (hPeriodic (sector, component)) :=
  ghostComponent_globalPairedGaugeLieSmoothOfComponents period hPeriod _ (sector, component)

theorem periodicTemporalPairedGhost_exact_potential
    (sector : Sector) (component : Fin 2) (point : EffectiveQuotient period hPeriod) :
    (exactGaugePotential period hPeriod
      (periodicTemporalPairedGhost period hPeriod profiles hSmooth hPeriodic sector)).toFun component point =
    scalarDifferential period hPeriod
      (periodicTemporalScalar period hPeriod (profiles (sector, component))
        (hSmooth (sector, component)) (hPeriodic (sector, component))) point := by
  change mvfderiv coverModelWithCorners
    (ghostComponent period hPeriod
      (periodicTemporalPairedGhost period hPeriod profiles hSmooth hPeriodic sector) component).toFun point = _
  rw [periodicTemporalPairedGhost_component]
  rfl

theorem periodicTemporalPairedGhost_intrinsic_sharp
    (sector : Sector) (component : Fin 2) (shift : Real) (pole : StandardSphere) (point : Coordinates) :
    inverseMetricSharp period hPeriod (intrinsicSmoothGeneralLorentzMetric period hPeriod)
      (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole point)
      ((exactGaugePotential period hPeriod
        (periodicTemporalPairedGhost period hPeriod profiles hSmooth hPeriodic sector)).toFun component
          (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole point)) =
    mfderiv coverModelWithCorners coverModelWithCorners
      (shiftedStereographicPhysicalMapAmbient period hPeriod shift pole) point
      (0, -deriv (profiles (sector, component)) (point.2 + shift)) := by
  rw [periodicTemporalPairedGhost_exact_potential]
  exact periodicTemporalScalar_intrinsic_sharp period hPeriod _ _ _ shift pole point

end
end JanusFormal.P0EFTJanusProgramPT12IntrinsicTemporalPairedGhost4D
