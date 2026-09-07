import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D

/-! # Exact Abelian BRST action defect under a change of metric

The physical state and canonical integration measure are held fixed. The
change of the genuine Lorenz and Faddeev--Popov operators supplies the entire
action difference; no metric independence of gauge fixing is assumed.
-/

namespace JanusFormal
namespace P0EFTJanusAbelianBRSTMetricChangeDefect4D

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 600000

noncomputable section
open MeasureTheory
open scoped BigOperators Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusMappingTorusCanonicalLorentzVolumeGluing4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev EffectiveQuotient := MappingTorus (reflectedSphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl
local instance : IsFiniteMeasure
    (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  intrinsicCanonicalLorentzVolumeMeasure_isFinite period hPeriod

/-- Difference of the two genuine Lorenz fields on the same potential. -/
def abelianLorenzMetricChange
    (metric reference : SmoothGeneralLorentzMetric period hPeriod)
    (potential : SmoothAbelianGaugePotential period hPeriod) :
    SmoothQuotientField period hPeriod GaugeLieAlgebra :=
  globalGeneralMetricAbelianLorenzCodifferential period hPeriod metric potential -
    globalGeneralMetricAbelianLorenzCodifferential period hPeriod reference potential

/-- Difference of the actual `δ_g d` fields on the same ghost. -/
def abelianFPMetricChange
    (metric reference : SmoothGeneralLorentzMetric period hPeriod)
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    SmoothQuotientField period hPeriod GaugeLieAlgebra :=
  globalGeneralMetricAbelianFaddeevPopov period hPeriod metric ghost -
    globalGeneralMetricAbelianFaddeevPopov period hPeriod reference ghost

theorem abelianFPMetricChange_eq_lorenz
    (metric reference : SmoothGeneralLorentzMetric period hPeriod)
    (ghost : SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    abelianFPMetricChange period hPeriod metric reference ghost =
      abelianLorenzMetricChange period hPeriod metric reference
        (exactGaugePotential period hPeriod ghost) := rfl

private theorem gaugeLiePairing_sub_second
    (first second third : SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (point : EffectiveQuotient period hPeriod) :
    globalGaugeLiePairingAt period hPeriod first (second - third) point =
      globalGaugeLiePairingAt period hPeriod first second point -
        globalGaugeLiePairingAt period hPeriod first third point := by
  rw [sub_eq_add_neg, globalGaugeLiePairingAt_add_second,
    globalGaugeLiePairingAt_neg_second, sub_eq_add_neg]

/-- Only the `B δA` and `cbar FP(c)` terms change; the auxiliary square cancels. -/
def globalPairedAbelianBRSTMetricChangeDensity
    (metric reference : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  ∑ sector : Sector,
    (globalGaugeLiePairingAt period hPeriod
        (state.nonminimal sector).nakanishiLautrup.field
        (abelianLorenzMetricChange period hPeriod (metric sector) (reference sector)
          (state.potential sector)) point +
      globalGaugeLiePairingAt period hPeriod
        (state.nonminimal sector).antighost.field
        (abelianFPMetricChange period hPeriod (metric sector) (reference sector)
          (state.nonminimal sector).ghost.field) point)

theorem globalPairedAbelianBRSTMetricChangeDensity_eq_sub
    (metric reference : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalPairedAbelianBRSTMetricChangeDensity period hPeriod metric reference state point =
      globalPairedAbelianGaugeFermionBRSTDensity period hPeriod metric state point -
        globalPairedAbelianGaugeFermionBRSTDensity period hPeriod reference state point := by
  unfold globalPairedAbelianBRSTMetricChangeDensity globalPairedAbelianGaugeFermionBRSTDensity
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro sector _
  simp only [abelianLorenzMetricChange, abelianFPMetricChange, gaugeLiePairing_sub_second]
  ring

theorem globalPairedAbelianBRSTMetricChangeDensity_continuous
    (metric reference : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    Continuous (globalPairedAbelianBRSTMetricChangeDensity
      period hPeriod metric reference state) := by
  unfold globalPairedAbelianBRSTMetricChangeDensity
  apply continuous_finsetSum Finset.univ
  intro sector _
  exact (globalGaugeLiePairingAt_continuous period hPeriod _ _).add
    (globalGaugeLiePairingAt_continuous period hPeriod _ _)

/-- Integrability follows from smoothness and compactness of the quotient. -/
theorem globalPairedAbelianBRSTMetricChangeDensity_integrable
    (metric reference : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    Integrable (globalPairedAbelianBRSTMetricChangeDensity
      period hPeriod metric reference state)
      (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) :=
  (globalPairedAbelianBRSTMetricChangeDensity_continuous
    period hPeriod metric reference state).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

def globalPairedAbelianBRSTMetricChangeAction
    (metric reference : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod) : Real :=
  ∫ point, globalPairedAbelianBRSTMetricChangeDensity
    period hPeriod metric reference state point
      ∂intrinsicCanonicalLorentzVolumeMeasure period hPeriod

/-- Exact action difference at fixed physical and nonminimal fields. -/
theorem globalPairedAbelianGaugeFermionBRSTAction_sub_eq_metricChange
    (metric reference : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric state
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) -
      globalPairedAbelianGaugeFermionBRSTAction period hPeriod reference state
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      globalPairedAbelianBRSTMetricChangeAction period hPeriod metric reference state := by
  unfold globalPairedAbelianGaugeFermionBRSTAction globalPairedAbelianBRSTMetricChangeAction
  rw [← integral_sub
    (globalPairedAbelianGaugeFermionBRSTDensity_integrable period hPeriod metric state _)
    (globalPairedAbelianGaugeFermionBRSTDensity_integrable period hPeriod reference state _)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun point =>
    (globalPairedAbelianBRSTMetricChangeDensity_eq_sub
      period hPeriod metric reference state point).symm

/-- A frozen-metric action agrees with the moving-metric action precisely
when the concrete integral defect vanishes. -/
theorem globalPairedAbelianGaugeFermionBRSTAction_eq_iff_metricChange_zero
    (metric reference : Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric state
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) =
      globalPairedAbelianGaugeFermionBRSTAction period hPeriod reference state
        (intrinsicCanonicalLorentzVolumeMeasure period hPeriod) ↔
      globalPairedAbelianBRSTMetricChangeAction period hPeriod metric reference state = 0 := by
  rw [← sub_eq_zero, globalPairedAbelianGaugeFermionBRSTAction_sub_eq_metricChange]

end
end P0EFTJanusAbelianBRSTMetricChangeDefect4D
end JanusFormal
