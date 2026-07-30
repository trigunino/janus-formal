import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D

/-!
# Global paired Abelian BRST gauge fermion

This gate installs the Abelian nonminimal BRST differential on both outer
Candidate-A sectors.  For a supplied smooth Lorentz metric in each sector it
uses the genuine global Lorenz codifferential and the exact Faddeev--Popov
operator `δ_g d`.

The integrated action is taken against a supplied finite Borel measure.  No
Green operator, formal adjoint, Fredholm realization or Berezin calculus is
asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 600000
set_option maxHeartbeats 600000

noncomputable section

open scoped BigOperators Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusSmoothFieldLinearSpace4D
open P0EFTJanusMappingTorusGeneralHolonomicScalarDensity4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalScalarJet4D
open P0EFTJanusScalarStressCovariantJetConservation4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusMappingTorusAbelianGaugeNoetherOperator4D
open P0EFTJanusMappingTorusGlobalGeneralMetricAbelianLorenzCodifferential4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveQuotient :=
  MappingTorus (reflectedSphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

local instance effectiveQuotientCompactSpace :
    CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

local instance effectiveQuotientMeasurableSpace :
    MeasurableSpace (EffectiveQuotient period hPeriod) :=
  borel _

local instance effectiveQuotientBorelSpace :
    BorelSpace (EffectiveQuotient period hPeriod) where
  measurable_eq := rfl

/-- The two physical Abelian potentials together with their independently
typed nonminimal fields. -/
@[ext]
structure GlobalPairedAbelianBRSTState where
  potential :
    Sector → SmoothAbelianGaugePotential period hPeriod
  nonminimal :
    Sector → GlobalAbelianNonminimalFields period hPeriod

def globalPairedAbelianBRSTStateEquiv :
    GlobalPairedAbelianBRSTState period hPeriod ≃
      (Sector → SmoothAbelianGaugePotential period hPeriod) ×
        (Sector → GlobalAbelianNonminimalFields period hPeriod) where
  toFun state := (state.potential, state.nonminimal)
  invFun fields := ⟨fields.1, fields.2⟩
  left_inv state := by cases state; rfl
  right_inv fields := by cases fields; rfl

instance globalPairedAbelianBRSTStateAddCommGroup :
    AddCommGroup (GlobalPairedAbelianBRSTState period hPeriod) :=
  Equiv.addCommGroup
    (globalPairedAbelianBRSTStateEquiv period hPeriod)

instance globalPairedAbelianBRSTStateModule :
    Module Real (GlobalPairedAbelianBRSTState period hPeriod) :=
  Equiv.module Real
    (globalPairedAbelianBRSTStateEquiv period hPeriod)

@[simp]
theorem globalPairedAbelianBRSTState_add_potential
    (first second : GlobalPairedAbelianBRSTState period hPeriod)
    (sector : Sector) :
    (first + second).potential sector =
      first.potential sector + second.potential sector :=
  rfl

@[simp]
theorem globalPairedAbelianBRSTState_add_nonminimal
    (first second : GlobalPairedAbelianBRSTState period hPeriod)
    (sector : Sector) :
    (first + second).nonminimal sector =
      first.nonminimal sector + second.nonminimal sector :=
  rfl

@[simp]
theorem globalPairedAbelianBRSTState_smul_potential
    (scalar : Real)
    (state : GlobalPairedAbelianBRSTState period hPeriod)
    (sector : Sector) :
    (scalar • state).potential sector =
      scalar • state.potential sector :=
  rfl

@[simp]
theorem globalPairedAbelianBRSTState_smul_nonminimal
    (scalar : Real)
    (state : GlobalPairedAbelianBRSTState period hPeriod)
    (sector : Sector) :
    (scalar • state).nonminimal sector =
      scalar • state.nonminimal sector :=
  rfl

@[simp]
theorem globalPairedAbelianBRSTState_add_ghost_field
    (first second : GlobalPairedAbelianBRSTState period hPeriod)
    (sector : Sector) :
    ((first + second).nonminimal sector).ghost.field =
      (first.nonminimal sector).ghost.field +
        (second.nonminimal sector).ghost.field :=
  rfl

@[simp]
theorem globalPairedAbelianBRSTState_add_antighost_field
    (first second : GlobalPairedAbelianBRSTState period hPeriod)
    (sector : Sector) :
    ((first + second).nonminimal sector).antighost.field =
      (first.nonminimal sector).antighost.field +
        (second.nonminimal sector).antighost.field :=
  rfl

@[simp]
theorem globalPairedAbelianBRSTState_add_nakanishiLautrup_field
    (first second : GlobalPairedAbelianBRSTState period hPeriod)
    (sector : Sector) :
    ((first + second).nonminimal sector).nakanishiLautrup.field =
      (first.nonminimal sector).nakanishiLautrup.field +
        (second.nonminimal sector).nakanishiLautrup.field :=
  rfl

@[simp]
theorem globalPairedAbelianBRSTState_smul_ghost_field
    (scalar : Real)
    (state : GlobalPairedAbelianBRSTState period hPeriod)
    (sector : Sector) :
    ((scalar • state).nonminimal sector).ghost.field =
      scalar • (state.nonminimal sector).ghost.field :=
  rfl

@[simp]
theorem globalPairedAbelianBRSTState_smul_antighost_field
    (scalar : Real)
    (state : GlobalPairedAbelianBRSTState period hPeriod)
    (sector : Sector) :
    ((scalar • state).nonminimal sector).antighost.field =
      scalar • (state.nonminimal sector).antighost.field :=
  rfl

@[simp]
theorem globalPairedAbelianBRSTState_smul_nakanishiLautrup_field
    (scalar : Real)
    (state : GlobalPairedAbelianBRSTState period hPeriod)
    (sector : Sector) :
    ((scalar • state).nonminimal sector).nakanishiLautrup.field =
      scalar • (state.nonminimal sector).nakanishiLautrup.field :=
  rfl

def zeroGlobalPairedAbelianBRSTState :
    GlobalPairedAbelianBRSTState period hPeriod where
  potential := fun _ => 0
  nonminimal := fun _ =>
    zeroGlobalAbelianNonminimalFields period hPeriod

/-- The genuine global Abelian rule
`s A = -dc`, `s c = 0`, `s cbar = B`, `s B = 0`, sector by sector. -/
def globalPairedAbelianBRST
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    GlobalPairedAbelianBRSTState period hPeriod where
  potential := fun sector =>
    -exactGaugePotential period hPeriod
      (state.nonminimal sector).ghost.field
  nonminimal := fun sector =>
    globalAbelianNonminimalBRST period hPeriod
      (state.nonminimal sector)

theorem globalPairedAbelianBRST_potential
    (state : GlobalPairedAbelianBRSTState period hPeriod)
    (sector : Sector) :
    (globalPairedAbelianBRST period hPeriod state).potential sector =
      -exactGaugePotential period hPeriod
        (state.nonminimal sector).ghost.field :=
  rfl

/-- The paired global differential is exactly square-zero. -/
theorem globalPairedAbelianBRST_square_zero
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    globalPairedAbelianBRST period hPeriod
        (globalPairedAbelianBRST period hPeriod state) =
      zeroGlobalPairedAbelianBRSTState period hPeriod := by
  apply GlobalPairedAbelianBRSTState.ext
  · funext sector
    change
      -exactGaugePotential period hPeriod
          (0 : SmoothQuotientField period hPeriod GaugeLieAlgebra) = 0
    rw [exactGaugePotential_zero]
    exact neg_zero
  · funext sector
    exact globalAbelianNonminimalBRST_square_zero period hPeriod
      (state.nonminimal sector)

/-- Euclidean pairing of two genuine `GaugeLieAlgebra` fields at one point. -/
def globalGaugeLiePairingAt
    (first second :
      SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (point : EffectiveQuotient period hPeriod) : Real :=
  ∑ component : Fin 2,
    first point component * second point component

theorem globalGaugeLiePairingAt_continuous
    (first second :
      SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    Continuous
      (globalGaugeLiePairingAt period hPeriod first second) := by
  unfold globalGaugeLiePairingAt
  apply continuous_finsetSum Finset.univ
  intro component _
  exact
    ((ghostComponent period hPeriod first component).contMDiff_toFun.continuous).mul
      ((ghostComponent period hPeriod second component).contMDiff_toFun.continuous)

theorem globalGaugeLiePairingAt_neg_second
    (first second :
      SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (point : EffectiveQuotient period hPeriod) :
    globalGaugeLiePairingAt period hPeriod first (-second) point =
      -globalGaugeLiePairingAt period hPeriod first second point := by
  unfold globalGaugeLiePairingAt
  simp only [Fin.sum_univ_two]
  change
    first point (0 : Fin 2) * (-second point (0 : Fin 2)) +
        first point (1 : Fin 2) * (-second point (1 : Fin 2)) =
      -(first point (0 : Fin 2) * second point (0 : Fin 2) +
        first point (1 : Fin 2) * second point (1 : Fin 2))
  ring

theorem globalGaugeLiePairingAt_add_first
    (first second third :
      SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (point : EffectiveQuotient period hPeriod) :
    globalGaugeLiePairingAt period hPeriod (first + second) third point =
      globalGaugeLiePairingAt period hPeriod first third point +
        globalGaugeLiePairingAt period hPeriod second third point := by
  unfold globalGaugeLiePairingAt
  simp only [Fin.sum_univ_two]
  change
    (first point 0 + second point 0) * third point 0 +
        (first point 1 + second point 1) * third point 1 =
      (first point 0 * third point 0 + first point 1 * third point 1) +
        (second point 0 * third point 0 + second point 1 * third point 1)
  ring

theorem globalGaugeLiePairingAt_add_second
    (first second third :
      SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (point : EffectiveQuotient period hPeriod) :
    globalGaugeLiePairingAt period hPeriod first (second + third) point =
      globalGaugeLiePairingAt period hPeriod first second point +
        globalGaugeLiePairingAt period hPeriod first third point := by
  unfold globalGaugeLiePairingAt
  simp only [Fin.sum_univ_two]
  change
    first point 0 * (second point 0 + third point 0) +
        first point 1 * (second point 1 + third point 1) =
      (first point 0 * second point 0 + first point 1 * second point 1) +
        (first point 0 * third point 0 + first point 1 * third point 1)
  ring

theorem globalGaugeLiePairingAt_smul_first
    (scalar : Real)
    (first second :
      SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (point : EffectiveQuotient period hPeriod) :
    globalGaugeLiePairingAt period hPeriod (scalar • first) second point =
      scalar *
        globalGaugeLiePairingAt period hPeriod first second point := by
  unfold globalGaugeLiePairingAt
  simp only [Fin.sum_univ_two]
  change
    scalar * first point 0 * second point 0 +
        scalar * first point 1 * second point 1 =
      scalar *
        (first point 0 * second point 0 + first point 1 * second point 1)
  ring

theorem globalGaugeLiePairingAt_smul_second
    (scalar : Real)
    (first second :
      SmoothQuotientField period hPeriod GaugeLieAlgebra)
    (point : EffectiveQuotient period hPeriod) :
    globalGaugeLiePairingAt period hPeriod first (scalar • second) point =
      scalar *
        globalGaugeLiePairingAt period hPeriod first second point := by
  unfold globalGaugeLiePairingAt
  simp only [Fin.sum_univ_two]
  change
    first point 0 * (scalar * second point 0) +
        first point 1 * (scalar * second point 1) =
      scalar *
        (first point 0 * second point 0 + first point 1 * second point 1)
  ring

theorem globalGeneralMetricAbelianFaddeevPopov_add
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (first second :
      SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    globalGeneralMetricAbelianFaddeevPopov period hPeriod metric
        (first + second) =
      globalGeneralMetricAbelianFaddeevPopov period hPeriod metric first +
        globalGeneralMetricAbelianFaddeevPopov period hPeriod metric second := by
  unfold globalGeneralMetricAbelianFaddeevPopov
  rw [exactGaugePotential_add,
    globalGeneralMetricAbelianLorenzCodifferential_add]

theorem globalGeneralMetricAbelianFaddeevPopov_smul
    (metric : SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (field : SmoothQuotientField period hPeriod GaugeLieAlgebra) :
    globalGeneralMetricAbelianFaddeevPopov period hPeriod metric
        (scalar • field) =
      scalar •
        globalGeneralMetricAbelianFaddeevPopov period hPeriod metric field := by
  unfold globalGeneralMetricAbelianFaddeevPopov
  rw [exactGaugePotential_smul,
    globalGeneralMetricAbelianLorenzCodifferential_smul]

/-- Real coefficient of the odd gauge fermion
`Σ cbar (δ_g A - B/2)`.  Its Grassmann parity is recorded by the graded
variation below rather than by a new Berezin scalar type. -/
def globalPairedAbelianGaugeFermionDensity
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  ∑ sector : Sector, (
    globalGaugeLiePairingAt period hPeriod
        (state.nonminimal sector).antighost.field
        (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
          (metric sector) (state.potential sector)) point -
      (1 / 2 : Real) *
        globalGaugeLiePairingAt period hPeriod
          (state.nonminimal sector).antighost.field
          (state.nonminimal sector).nakanishiLautrup.field point)

/-- The actual off-shell `sΨ` density:
`B δ_g A - B²/2 + cbar (δ_g d)c`. -/
def globalPairedAbelianGaugeFermionBRSTDensity
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  ∑ sector : Sector, (
    globalGaugeLiePairingAt period hPeriod
        (state.nonminimal sector).nakanishiLautrup.field
        (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
          (metric sector) (state.potential sector)) point -
      (1 / 2 : Real) *
        globalGaugeLiePairingAt period hPeriod
          (state.nonminimal sector).nakanishiLautrup.field
          (state.nonminimal sector).nakanishiLautrup.field point +
      globalGaugeLiePairingAt period hPeriod
        (state.nonminimal sector).antighost.field
        (globalGeneralMetricAbelianFaddeevPopov period hPeriod
          (metric sector) (state.nonminimal sector).ghost.field) point)

/-- Direct graded-Leibniz evaluation before replacing `δ_g(sA)` by the
Faddeev--Popov operator. -/
def globalPairedAbelianGaugeFermionGradedVariationDensity
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  ∑ sector : Sector, (
    globalGaugeLiePairingAt period hPeriod
        (state.nonminimal sector).nakanishiLautrup.field
        (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
          (metric sector) (state.potential sector)) point -
      (1 / 2 : Real) *
        globalGaugeLiePairingAt period hPeriod
          (state.nonminimal sector).nakanishiLautrup.field
          (state.nonminimal sector).nakanishiLautrup.field point -
      globalGaugeLiePairingAt period hPeriod
        (state.nonminimal sector).antighost.field
        (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
          (metric sector)
          ((globalPairedAbelianBRST period hPeriod state).potential sector))
        point)

theorem globalPairedAbelianBRST_lorenz_eq_neg_faddeevPopov
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod)
    (sector : Sector) :
    globalGeneralMetricAbelianLorenzCodifferential period hPeriod
        (metric sector)
        ((globalPairedAbelianBRST period hPeriod state).potential sector) =
      -globalGeneralMetricAbelianFaddeevPopov period hPeriod
        (metric sector) (state.nonminimal sector).ghost.field := by
  simpa [globalPairedAbelianBRST,
    globalGeneralMetricAbelianFaddeevPopov] using
    (globalGeneralMetricAbelianLorenzCodifferential_smul period hPeriod
      (metric sector) (-1 : Real)
      (exactGaugePotential period hPeriod
        (state.nonminimal sector).ghost.field))

/-- Exact identification of the graded variation with the off-shell
auxiliary plus Faddeev--Popov density. -/
theorem globalPairedAbelianGaugeFermionGradedVariationDensity_eq
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalPairedAbelianGaugeFermionGradedVariationDensity period hPeriod
        metric state point =
      globalPairedAbelianGaugeFermionBRSTDensity period hPeriod metric
        state point := by
  unfold globalPairedAbelianGaugeFermionGradedVariationDensity
    globalPairedAbelianGaugeFermionBRSTDensity
  apply Finset.sum_congr rfl
  intro sector _
  rw [globalPairedAbelianBRST_lorenz_eq_neg_faddeevPopov
    period hPeriod metric state sector]
  rw [globalGaugeLiePairingAt_neg_second]
  ring

theorem globalPairedAbelianGaugeFermionBRSTDensity_continuous
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod) :
    Continuous
      (globalPairedAbelianGaugeFermionBRSTDensity period hPeriod metric
        state) := by
  unfold globalPairedAbelianGaugeFermionBRSTDensity
  apply continuous_finsetSum Finset.univ
  intro sector _
  exact
    (((globalGaugeLiePairingAt_continuous period hPeriod
          (state.nonminimal sector).nakanishiLautrup.field
          (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
            (metric sector) (state.potential sector))).sub
        (continuous_const.mul
          (globalGaugeLiePairingAt_continuous period hPeriod
            (state.nonminimal sector).nakanishiLautrup.field
            (state.nonminimal sector).nakanishiLautrup.field))).add
      (globalGaugeLiePairingAt_continuous period hPeriod
        (state.nonminimal sector).antighost.field
        (globalGeneralMetricAbelianFaddeevPopov period hPeriod
          (metric sector) (state.nonminimal sector).ghost.field)))

theorem globalPairedAbelianGaugeFermionBRSTDensity_integrable
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    Integrable
      (globalPairedAbelianGaugeFermionBRSTDensity period hPeriod metric
        state) measure :=
  (globalPairedAbelianGaugeFermionBRSTDensity_continuous period hPeriod
      metric state).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Integrated off-shell paired Abelian gauge-fixing action. -/
def globalPairedAbelianGaugeFermionBRSTAction
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] : Real :=
  ∫ point,
    globalPairedAbelianGaugeFermionBRSTDensity period hPeriod metric
      state point ∂measure

/-- Bilinear form whose diagonal is exactly `sΨ`. -/
def globalPairedAbelianGaugeFermionBRSTMixedDensity
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalPairedAbelianBRSTState period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  ∑ sector : Sector, (
    globalGaugeLiePairingAt period hPeriod
        (first.nonminimal sector).nakanishiLautrup.field
        (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
          (metric sector) (second.potential sector)) point -
      (1 / 2 : Real) *
        globalGaugeLiePairingAt period hPeriod
          (first.nonminimal sector).nakanishiLautrup.field
          (second.nonminimal sector).nakanishiLautrup.field point +
      globalGaugeLiePairingAt period hPeriod
        (first.nonminimal sector).antighost.field
        (globalGeneralMetricAbelianFaddeevPopov period hPeriod
          (metric sector) (second.nonminimal sector).ghost.field) point)

theorem globalPairedAbelianGaugeFermionBRSTMixedDensity_self
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalPairedAbelianGaugeFermionBRSTMixedDensity period hPeriod metric
        state state point =
      globalPairedAbelianGaugeFermionBRSTDensity period hPeriod metric
        state point :=
  rfl

theorem globalPairedAbelianGaugeFermionBRSTMixedDensity_add_first
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second third : GlobalPairedAbelianBRSTState period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalPairedAbelianGaugeFermionBRSTMixedDensity period hPeriod metric
        (first + second) third point =
      globalPairedAbelianGaugeFermionBRSTMixedDensity period hPeriod metric
          first third point +
        globalPairedAbelianGaugeFermionBRSTMixedDensity period hPeriod metric
          second third point := by
  unfold globalPairedAbelianGaugeFermionBRSTMixedDensity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro sector _
  simp only [globalPairedAbelianBRSTState_add_nakanishiLautrup_field,
    globalPairedAbelianBRSTState_add_antighost_field]
  rw [globalGaugeLiePairingAt_add_first,
    globalGaugeLiePairingAt_add_first,
    globalGaugeLiePairingAt_add_first]
  ring

theorem globalPairedAbelianGaugeFermionBRSTMixedDensity_add_second
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second third : GlobalPairedAbelianBRSTState period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalPairedAbelianGaugeFermionBRSTMixedDensity period hPeriod metric
        first (second + third) point =
      globalPairedAbelianGaugeFermionBRSTMixedDensity period hPeriod metric
          first second point +
        globalPairedAbelianGaugeFermionBRSTMixedDensity period hPeriod metric
          first third point := by
  unfold globalPairedAbelianGaugeFermionBRSTMixedDensity
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro sector _
  simp only [globalPairedAbelianBRSTState_add_potential,
    globalPairedAbelianBRSTState_add_nakanishiLautrup_field,
    globalPairedAbelianBRSTState_add_ghost_field]
  rw [globalGeneralMetricAbelianLorenzCodifferential_add,
    globalGeneralMetricAbelianFaddeevPopov_add,
    globalGaugeLiePairingAt_add_second,
    globalGaugeLiePairingAt_add_second,
    globalGaugeLiePairingAt_add_second]
  ring

theorem globalPairedAbelianGaugeFermionBRSTMixedDensity_smul_first
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (first second : GlobalPairedAbelianBRSTState period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalPairedAbelianGaugeFermionBRSTMixedDensity period hPeriod metric
        (scalar • first) second point =
      scalar *
        globalPairedAbelianGaugeFermionBRSTMixedDensity period hPeriod metric
          first second point := by
  unfold globalPairedAbelianGaugeFermionBRSTMixedDensity
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sector _
  simp only [globalPairedAbelianBRSTState_smul_nakanishiLautrup_field,
    globalPairedAbelianBRSTState_smul_antighost_field]
  rw [globalGaugeLiePairingAt_smul_first,
    globalGaugeLiePairingAt_smul_first,
    globalGaugeLiePairingAt_smul_first]
  ring

theorem globalPairedAbelianGaugeFermionBRSTMixedDensity_smul_second
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (first second : GlobalPairedAbelianBRSTState period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalPairedAbelianGaugeFermionBRSTMixedDensity period hPeriod metric
        first (scalar • second) point =
      scalar *
        globalPairedAbelianGaugeFermionBRSTMixedDensity period hPeriod metric
          first second point := by
  unfold globalPairedAbelianGaugeFermionBRSTMixedDensity
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro sector _
  simp only [globalPairedAbelianBRSTState_smul_potential,
    globalPairedAbelianBRSTState_smul_nakanishiLautrup_field,
    globalPairedAbelianBRSTState_smul_ghost_field]
  rw [globalGeneralMetricAbelianLorenzCodifferential_smul,
    globalGeneralMetricAbelianFaddeevPopov_smul,
    globalGaugeLiePairingAt_smul_second,
    globalGaugeLiePairingAt_smul_second,
    globalGaugeLiePairingAt_smul_second]
  ring

theorem globalPairedAbelianGaugeFermionBRSTMixedDensity_continuous
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalPairedAbelianBRSTState period hPeriod) :
    Continuous
      (globalPairedAbelianGaugeFermionBRSTMixedDensity period hPeriod
        metric first second) := by
  unfold globalPairedAbelianGaugeFermionBRSTMixedDensity
  apply continuous_finsetSum Finset.univ
  intro sector _
  exact
    (((globalGaugeLiePairingAt_continuous period hPeriod
          (first.nonminimal sector).nakanishiLautrup.field
          (globalGeneralMetricAbelianLorenzCodifferential period hPeriod
            (metric sector) (second.potential sector))).sub
        (continuous_const.mul
          (globalGaugeLiePairingAt_continuous period hPeriod
            (first.nonminimal sector).nakanishiLautrup.field
            (second.nonminimal sector).nakanishiLautrup.field))).add
      (globalGaugeLiePairingAt_continuous period hPeriod
        (first.nonminimal sector).antighost.field
        (globalGeneralMetricAbelianFaddeevPopov period hPeriod
          (metric sector) (second.nonminimal sector).ghost.field)))

theorem globalPairedAbelianGaugeFermionBRSTMixedDensity_integrable
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalPairedAbelianBRSTState period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    Integrable
      (globalPairedAbelianGaugeFermionBRSTMixedDensity period hPeriod
        metric first second) measure :=
  (globalPairedAbelianGaugeFermionBRSTMixedDensity_continuous period hPeriod
      metric first second).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

/-- Integrated real-bilinear form whose diagonal is the off-shell `sΨ`
action. -/
def globalPairedAbelianGaugeFermionBRSTMixedAction
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalPairedAbelianBRSTState period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] : Real :=
  ∫ point,
    globalPairedAbelianGaugeFermionBRSTMixedDensity period hPeriod metric
      first second point ∂measure

theorem globalPairedAbelianGaugeFermionBRSTMixedAction_add_first
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second third : GlobalPairedAbelianBRSTState period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    globalPairedAbelianGaugeFermionBRSTMixedAction period hPeriod metric
        (first + second) third measure =
      globalPairedAbelianGaugeFermionBRSTMixedAction period hPeriod metric
          first third measure +
        globalPairedAbelianGaugeFermionBRSTMixedAction period hPeriod metric
          second third measure := by
  unfold globalPairedAbelianGaugeFermionBRSTMixedAction
  simp_rw [globalPairedAbelianGaugeFermionBRSTMixedDensity_add_first
    period hPeriod metric first second third]
  exact integral_add
    (globalPairedAbelianGaugeFermionBRSTMixedDensity_integrable period hPeriod
      metric first third measure)
    (globalPairedAbelianGaugeFermionBRSTMixedDensity_integrable period hPeriod
      metric second third measure)

theorem globalPairedAbelianGaugeFermionBRSTMixedAction_add_second
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second third : GlobalPairedAbelianBRSTState period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    globalPairedAbelianGaugeFermionBRSTMixedAction period hPeriod metric
        first (second + third) measure =
      globalPairedAbelianGaugeFermionBRSTMixedAction period hPeriod metric
          first second measure +
        globalPairedAbelianGaugeFermionBRSTMixedAction period hPeriod metric
          first third measure := by
  unfold globalPairedAbelianGaugeFermionBRSTMixedAction
  simp_rw [globalPairedAbelianGaugeFermionBRSTMixedDensity_add_second
    period hPeriod metric first second third]
  exact integral_add
    (globalPairedAbelianGaugeFermionBRSTMixedDensity_integrable period hPeriod
      metric first second measure)
    (globalPairedAbelianGaugeFermionBRSTMixedDensity_integrable period hPeriod
      metric first third measure)

theorem globalPairedAbelianGaugeFermionBRSTMixedAction_smul_first
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (first second : GlobalPairedAbelianBRSTState period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    globalPairedAbelianGaugeFermionBRSTMixedAction period hPeriod metric
        (scalar • first) second measure =
      scalar *
        globalPairedAbelianGaugeFermionBRSTMixedAction period hPeriod metric
          first second measure := by
  unfold globalPairedAbelianGaugeFermionBRSTMixedAction
  simp_rw [globalPairedAbelianGaugeFermionBRSTMixedDensity_smul_first
    period hPeriod metric scalar first second]
  rw [integral_const_mul]

theorem globalPairedAbelianGaugeFermionBRSTMixedAction_smul_second
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (scalar : Real)
    (first second : GlobalPairedAbelianBRSTState period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    globalPairedAbelianGaugeFermionBRSTMixedAction period hPeriod metric
        first (scalar • second) measure =
      scalar *
        globalPairedAbelianGaugeFermionBRSTMixedAction period hPeriod metric
          first second measure := by
  unfold globalPairedAbelianGaugeFermionBRSTMixedAction
  simp_rw [globalPairedAbelianGaugeFermionBRSTMixedDensity_smul_second
    period hPeriod metric scalar first second]
  rw [integral_const_mul]

theorem globalPairedAbelianGaugeFermionBRSTAction_eq_mixed_self
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric state
        measure =
      globalPairedAbelianGaugeFermionBRSTMixedAction period hPeriod metric
        state state measure :=
  rfl

/-- Exact polarization of the quadratic off-shell density. -/
def globalPairedAbelianGaugeFermionBRSTPolarizationDensity
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalPairedAbelianBRSTState period hPeriod)
    (point : EffectiveQuotient period hPeriod) : Real :=
  globalPairedAbelianGaugeFermionBRSTMixedDensity period hPeriod metric
      first second point +
    globalPairedAbelianGaugeFermionBRSTMixedDensity period hPeriod metric
      second first point

theorem globalPairedAbelianGaugeFermionBRSTPolarizationDensity_symmetric
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalPairedAbelianBRSTState period hPeriod) :
    globalPairedAbelianGaugeFermionBRSTPolarizationDensity period hPeriod
        metric first second =
      globalPairedAbelianGaugeFermionBRSTPolarizationDensity period hPeriod
        metric second first := by
  funext point
  simp only [globalPairedAbelianGaugeFermionBRSTPolarizationDensity]
  exact add_comm _ _

theorem globalPairedAbelianGaugeFermionBRSTPolarizationDensity_self
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod)
    (point : EffectiveQuotient period hPeriod) :
    globalPairedAbelianGaugeFermionBRSTPolarizationDensity period hPeriod
        metric state state point =
      2 *
        globalPairedAbelianGaugeFermionBRSTDensity period hPeriod metric
          state point := by
  rw [globalPairedAbelianGaugeFermionBRSTPolarizationDensity,
    globalPairedAbelianGaugeFermionBRSTMixedDensity_self]
  ring

/-- Integrated exact polarization of the gauge-fixing action. -/
def globalPairedAbelianGaugeFermionBRSTPolarizationAction
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalPairedAbelianBRSTState period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] : Real :=
  ∫ point,
    globalPairedAbelianGaugeFermionBRSTPolarizationDensity period hPeriod
      metric first second point ∂measure

theorem globalPairedAbelianGaugeFermionBRSTPolarizationAction_symmetric
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalPairedAbelianBRSTState period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    globalPairedAbelianGaugeFermionBRSTPolarizationAction period hPeriod
        metric first second measure =
      globalPairedAbelianGaugeFermionBRSTPolarizationAction period hPeriod
        metric second first measure := by
  unfold globalPairedAbelianGaugeFermionBRSTPolarizationAction
  congr 1
  exact
    globalPairedAbelianGaugeFermionBRSTPolarizationDensity_symmetric
      period hPeriod metric first second

theorem globalPairedAbelianGaugeFermionBRSTPolarizationAction_eq_mixed
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (first second : GlobalPairedAbelianBRSTState period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    globalPairedAbelianGaugeFermionBRSTPolarizationAction period hPeriod
        metric first second measure =
      globalPairedAbelianGaugeFermionBRSTMixedAction period hPeriod metric
          first second measure +
        globalPairedAbelianGaugeFermionBRSTMixedAction period hPeriod metric
          second first measure := by
  unfold globalPairedAbelianGaugeFermionBRSTPolarizationAction
    globalPairedAbelianGaugeFermionBRSTPolarizationDensity
    globalPairedAbelianGaugeFermionBRSTMixedAction
  exact integral_add
    (globalPairedAbelianGaugeFermionBRSTMixedDensity_integrable period hPeriod
      metric first second measure)
    (globalPairedAbelianGaugeFermionBRSTMixedDensity_integrable period hPeriod
      metric second first measure)

theorem globalPairedAbelianGaugeFermionBRSTPolarizationAction_self
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    globalPairedAbelianGaugeFermionBRSTPolarizationAction period hPeriod
        metric state state measure =
      2 *
        globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric state
          measure := by
  rw [globalPairedAbelianGaugeFermionBRSTPolarizationAction_eq_mixed,
    globalPairedAbelianGaugeFermionBRSTAction_eq_mixed_self]
  ring

/-- The quadratic gauge-fixing action restricted to an affine line. -/
def globalPairedAbelianGaugeFermionBRSTLineAction
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state direction : GlobalPairedAbelianBRSTState period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (parameter : Real) : Real :=
  globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric
    (state + parameter • direction) measure

/-- Polarization against the line direction; this is the actual first
derivative curve proved below. -/
def globalPairedAbelianGaugeFermionBRSTLineFirstVariation
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state direction : GlobalPairedAbelianBRSTState period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (parameter : Real) : Real :=
  globalPairedAbelianGaugeFermionBRSTPolarizationAction period hPeriod
    metric (state + parameter • direction) direction measure

theorem globalPairedAbelianGaugeFermionBRSTLineAction_expansion
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state direction : GlobalPairedAbelianBRSTState period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (parameter : Real) :
    globalPairedAbelianGaugeFermionBRSTLineAction period hPeriod metric
        state direction measure parameter =
      globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric state
          measure +
        parameter *
          globalPairedAbelianGaugeFermionBRSTPolarizationAction period hPeriod
            metric state direction measure +
        parameter ^ 2 *
          globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric
            direction measure := by
  unfold globalPairedAbelianGaugeFermionBRSTLineAction
  rw [globalPairedAbelianGaugeFermionBRSTAction_eq_mixed_self,
    globalPairedAbelianGaugeFermionBRSTMixedAction_add_first,
    globalPairedAbelianGaugeFermionBRSTMixedAction_add_second,
    globalPairedAbelianGaugeFermionBRSTMixedAction_add_second,
    globalPairedAbelianGaugeFermionBRSTMixedAction_smul_second,
    globalPairedAbelianGaugeFermionBRSTMixedAction_smul_first,
    globalPairedAbelianGaugeFermionBRSTMixedAction_smul_first,
    globalPairedAbelianGaugeFermionBRSTMixedAction_smul_second,
    globalPairedAbelianGaugeFermionBRSTPolarizationAction_eq_mixed,
    globalPairedAbelianGaugeFermionBRSTAction_eq_mixed_self]
  rw [globalPairedAbelianGaugeFermionBRSTAction_eq_mixed_self
    period hPeriod metric direction measure]
  ring

theorem globalPairedAbelianGaugeFermionBRSTLineFirstVariation_affine
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state direction : GlobalPairedAbelianBRSTState period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure]
    (parameter : Real) :
    globalPairedAbelianGaugeFermionBRSTLineFirstVariation period hPeriod
        metric state direction measure parameter =
      globalPairedAbelianGaugeFermionBRSTPolarizationAction period hPeriod
          metric state direction measure +
        parameter *
          globalPairedAbelianGaugeFermionBRSTPolarizationAction period hPeriod
            metric direction direction measure := by
  unfold globalPairedAbelianGaugeFermionBRSTLineFirstVariation
  rw [globalPairedAbelianGaugeFermionBRSTPolarizationAction_eq_mixed,
    globalPairedAbelianGaugeFermionBRSTPolarizationAction_eq_mixed,
    globalPairedAbelianGaugeFermionBRSTPolarizationAction_eq_mixed,
    globalPairedAbelianGaugeFermionBRSTMixedAction_add_first,
    globalPairedAbelianGaugeFermionBRSTMixedAction_smul_first,
    globalPairedAbelianGaugeFermionBRSTMixedAction_add_second,
    globalPairedAbelianGaugeFermionBRSTMixedAction_smul_second]
  ring

theorem globalPairedAbelianGaugeFermionBRSTLineAction_hasDerivAt_zero
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state direction : GlobalPairedAbelianBRSTState period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    HasDerivAt
      (globalPairedAbelianGaugeFermionBRSTLineAction period hPeriod metric
        state direction measure)
      (globalPairedAbelianGaugeFermionBRSTPolarizationAction period hPeriod
        metric state direction measure) 0 := by
  rw [show
      globalPairedAbelianGaugeFermionBRSTLineAction period hPeriod metric
          state direction measure =
        fun parameter : Real =>
          globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric
              state measure +
            parameter *
              globalPairedAbelianGaugeFermionBRSTPolarizationAction period
                hPeriod metric state direction measure +
            parameter ^ 2 *
              globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric
                direction measure by
      funext parameter
      exact globalPairedAbelianGaugeFermionBRSTLineAction_expansion
        period hPeriod metric state direction measure parameter]
  have hLinear :=
    ((hasDerivAt_id (𝕜 := Real) 0).mul_const
      (globalPairedAbelianGaugeFermionBRSTPolarizationAction period hPeriod
        metric state direction measure)).const_add
      (globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric state
        measure)
  have hQuadratic :=
    ((hasDerivAt_id (𝕜 := Real) 0).pow 2).mul_const
      (globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric
        direction measure)
  change HasDerivAt
    ((fun parameter : Real =>
        globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric state
            measure +
          parameter *
            globalPairedAbelianGaugeFermionBRSTPolarizationAction period
              hPeriod metric state direction measure) +
      (fun parameter : Real =>
        parameter ^ 2 *
          globalPairedAbelianGaugeFermionBRSTAction period hPeriod metric
            direction measure)) _ 0
  exact (hLinear.add hQuadratic).congr_deriv (by norm_num)

theorem globalPairedAbelianGaugeFermionBRSTLineFirstVariation_hasDerivAt_zero
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state direction : GlobalPairedAbelianBRSTState period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    HasDerivAt
      (globalPairedAbelianGaugeFermionBRSTLineFirstVariation period hPeriod
        metric state direction measure)
      (globalPairedAbelianGaugeFermionBRSTPolarizationAction period hPeriod
        metric direction direction measure) 0 := by
  rw [show
      globalPairedAbelianGaugeFermionBRSTLineFirstVariation period hPeriod
          metric state direction measure =
        fun parameter : Real =>
          globalPairedAbelianGaugeFermionBRSTPolarizationAction period hPeriod
              metric state direction measure +
            parameter *
              globalPairedAbelianGaugeFermionBRSTPolarizationAction period
                hPeriod metric direction direction measure by
      funext parameter
      exact globalPairedAbelianGaugeFermionBRSTLineFirstVariation_affine
        period hPeriod metric state direction measure parameter]
  simpa using
    ((hasDerivAt_id (𝕜 := Real) 0).mul_const
      (globalPairedAbelianGaugeFermionBRSTPolarizationAction period hPeriod
        metric direction direction measure)).const_add
      (globalPairedAbelianGaugeFermionBRSTPolarizationAction period hPeriod
        metric state direction measure)

/-- Genuine second derivative of
`t ↦ sΨ(state + t • direction)` at zero.  The first component identifies its
first derivative curve; the second differentiates that curve and returns the
diagonal polarization. -/
theorem globalPairedAbelianGaugeFermionBRSTLine_hasSecondDerivAt_zero
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state direction : GlobalPairedAbelianBRSTState period hPeriod)
    (measure : Measure (EffectiveQuotient period hPeriod))
    [IsFiniteMeasure measure] :
    HasDerivAt
        (globalPairedAbelianGaugeFermionBRSTLineAction period hPeriod metric
          state direction measure)
        (globalPairedAbelianGaugeFermionBRSTLineFirstVariation period hPeriod
          metric state direction measure 0) 0 ∧
      HasDerivAt
        (globalPairedAbelianGaugeFermionBRSTLineFirstVariation period hPeriod
          metric state direction measure)
        (globalPairedAbelianGaugeFermionBRSTPolarizationAction period hPeriod
          metric direction direction measure) 0 := by
  constructor
  · simpa [globalPairedAbelianGaugeFermionBRSTLineFirstVariation_affine]
      using
        (globalPairedAbelianGaugeFermionBRSTLineAction_hasDerivAt_zero
          period hPeriod metric state direction measure)
  · exact
      globalPairedAbelianGaugeFermionBRSTLineFirstVariation_hasDerivAt_zero
        period hPeriod metric state direction measure

/-- The ghost block is locally the already proved covariant scalar wave:
this is the exact `δ_g d` Faddeev--Popov identification. -/
theorem globalPairedAbelianFaddeevPopov_apply_local
    (metric :
      Sector → SmoothGeneralLorentzMetric period hPeriod)
    (state : GlobalPairedAbelianBRSTState period hPeriod)
    (sector : Sector)
    (component : Fin 2)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate :
      P0EFTJanusMetricCoupledScalarMatterJetVariation.Vector4) :
    globalGeneralMetricAbelianFaddeevPopov period hPeriod
        (metric sector) (state.nonminimal sector).ghost.field
        (patch.coordinateMap coordinate) component =
      covariantScalarJetWave
        (localFixedSignMetric period hPeriod (metric sector) patch coordinate)
        (localCovariantScalarJet period hPeriod (metric sector) patch
          (ghostComponent period hPeriod
            (state.nonminimal sector).ghost.field component) coordinate) :=
  globalGeneralMetricAbelianFaddeevPopov_apply_local period hPeriod
    (metric sector) (state.nonminimal sector).ghost.field component patch
      coordinate

end
end P0EFTJanusProgramPGlobalPairedAbelianBRSTGaugeFermion4D
end JanusFormal
