import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D

/-!
# Actual bulk Abelian nonminimal chartwise second-order jets

The ghost, antighost and Nakanishi--Lautrup fields of each physical Abelian
sector are pulled back through one supplied bulk holonomic chart.  Their
global smoothness supplies the genuine value, first derivative and symmetric
second derivative required by the physical jet carrier.

No diffeomorphism-nonminimal jet, background completion, overlap law or full
bulk-carrier extraction is asserted here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualBulkAbelianNonminimalChartwiseSecondOrderJetExtraction4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusMappingTorusAbelianGaugeBRST4D
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D

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

universe u

private def smoothBulkQuotientFieldChartGerm
    {Fiber : Type u}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothQuotientField period hPeriod Fiber)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    CoverCoordinates → Fiber :=
  fun coordinate =>
    field (patch.coordinateMap (coverToHolonomicEquiv coordinate))

private theorem smoothBulkQuotientFieldChartGerm_contDiff
    {Fiber : Type u}
    [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]
    (field : SmoothQuotientField period hPeriod Fiber)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (smoothBulkQuotientFieldChartGerm period hPeriod field patch) := by
  have hHolonomic : ContDiff Real ∞ (fun coordinate =>
      field (patch.coordinateMap coordinate)) := by
    exact
      ((field.contMDiff_toFun.of_le (m := ∞) (by simp)).comp
        patch.coordinateMap_contMDiff).contDiff
  exact hHolonomic.comp coverToHolonomicEquiv.contDiff

/-! ## Sectorwise coordinate germs -/

/-- Actual Abelian ghost in the selected bulk chart. -/
def globalGaugeFixedBulkAbelianGhostChartGerm
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    CoverCoordinates → GaugeLieAlgebra :=
  smoothBulkQuotientFieldChartGerm period hPeriod
    (configuration.nonminimal.abelian sector).ghost.field patch

theorem globalGaugeFixedBulkAbelianGhostChartGerm_contDiff
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (globalGaugeFixedBulkAbelianGhostChartGerm
        period hPeriod configuration sector patch) :=
  smoothBulkQuotientFieldChartGerm_contDiff period hPeriod
    (configuration.nonminimal.abelian sector).ghost.field patch

/-- Actual Abelian antighost in the selected bulk chart. -/
def globalGaugeFixedBulkAbelianAntighostChartGerm
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    CoverCoordinates → GaugeLieAlgebra :=
  smoothBulkQuotientFieldChartGerm period hPeriod
    (configuration.nonminimal.abelian sector).antighost.field patch

theorem globalGaugeFixedBulkAbelianAntighostChartGerm_contDiff
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (globalGaugeFixedBulkAbelianAntighostChartGerm
        period hPeriod configuration sector patch) :=
  smoothBulkQuotientFieldChartGerm_contDiff period hPeriod
    (configuration.nonminimal.abelian sector).antighost.field patch

/-- Actual Abelian Nakanishi--Lautrup field in the selected bulk chart. -/
def globalGaugeFixedBulkAbelianNakanishiLautrupChartGerm
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    CoverCoordinates → GaugeLieAlgebra :=
  smoothBulkQuotientFieldChartGerm period hPeriod
    (configuration.nonminimal.abelian sector).nakanishiLautrup.field patch

theorem globalGaugeFixedBulkAbelianNakanishiLautrupChartGerm_contDiff
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContDiff Real ∞
      (globalGaugeFixedBulkAbelianNakanishiLautrupChartGerm
        period hPeriod configuration sector patch) :=
  smoothBulkQuotientFieldChartGerm_contDiff period hPeriod
    (configuration.nonminimal.abelian sector).nakanishiLautrup.field patch

/-! ## Sectorwise second-order jets -/

/-- Actual second jet of one sector's Abelian ghost. -/
def globalGaugeFixedBulkAbelianGhostSecondOrderJetAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    FramedSecondOrderJet CoverCoordinates GaugeLieAlgebra :=
  chartwiseSecondOrderJetAt
    (globalGaugeFixedBulkAbelianGhostChartGerm
      period hPeriod configuration sector patch)
    coordinate
    ((globalGaugeFixedBulkAbelianGhostChartGerm_contDiff
      period hPeriod configuration sector patch).contDiffAt.of_le (by
        show (2 : ℕ∞ω) ≤ ∞
        exact WithTop.coe_le_coe.mpr le_top))

@[simp]
theorem globalGaugeFixedBulkAbelianGhostSecondOrderJetAt_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    (globalGaugeFixedBulkAbelianGhostSecondOrderJetAt period hPeriod
      configuration sector patch coordinate).value =
      (configuration.nonminimal.abelian sector).ghost.field
        (patch.coordinateMap (coverToHolonomicEquiv coordinate)) := by
  rw [globalGaugeFixedBulkAbelianGhostSecondOrderJetAt,
    chartwiseSecondOrderJetAt_value]
  rfl

/-- Actual second jet of one sector's Abelian antighost. -/
def globalGaugeFixedBulkAbelianAntighostSecondOrderJetAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    FramedSecondOrderJet CoverCoordinates GaugeLieAlgebra :=
  chartwiseSecondOrderJetAt
    (globalGaugeFixedBulkAbelianAntighostChartGerm
      period hPeriod configuration sector patch)
    coordinate
    ((globalGaugeFixedBulkAbelianAntighostChartGerm_contDiff
      period hPeriod configuration sector patch).contDiffAt.of_le (by
        show (2 : ℕ∞ω) ≤ ∞
        exact WithTop.coe_le_coe.mpr le_top))

@[simp]
theorem globalGaugeFixedBulkAbelianAntighostSecondOrderJetAt_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    (globalGaugeFixedBulkAbelianAntighostSecondOrderJetAt period hPeriod
      configuration sector patch coordinate).value =
      (configuration.nonminimal.abelian sector).antighost.field
        (patch.coordinateMap (coverToHolonomicEquiv coordinate)) := by
  rw [globalGaugeFixedBulkAbelianAntighostSecondOrderJetAt,
    chartwiseSecondOrderJetAt_value]
  rfl

/-- Actual second jet of one sector's Abelian Nakanishi--Lautrup field. -/
def globalGaugeFixedBulkAbelianNakanishiLautrupSecondOrderJetAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    FramedSecondOrderJet CoverCoordinates GaugeLieAlgebra :=
  chartwiseSecondOrderJetAt
    (globalGaugeFixedBulkAbelianNakanishiLautrupChartGerm
      period hPeriod configuration sector patch)
    coordinate
    ((globalGaugeFixedBulkAbelianNakanishiLautrupChartGerm_contDiff
      period hPeriod configuration sector patch).contDiffAt.of_le (by
        show (2 : ℕ∞ω) ≤ ∞
        exact WithTop.coe_le_coe.mpr le_top))

@[simp]
theorem globalGaugeFixedBulkAbelianNakanishiLautrupSecondOrderJetAt_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    (globalGaugeFixedBulkAbelianNakanishiLautrupSecondOrderJetAt period hPeriod
      configuration sector patch coordinate).value =
      (configuration.nonminimal.abelian sector).nakanishiLautrup.field
        (patch.coordinateMap (coverToHolonomicEquiv coordinate)) := by
  rw [globalGaugeFixedBulkAbelianNakanishiLautrupSecondOrderJetAt,
    chartwiseSecondOrderJetAt_value]
  rfl

/-! ## Aggregated carrier slots -/

/-- The three sectorized Abelian nonminimal slots of the bulk carrier.
These are ordinary real Fréchet jets of the coefficient representatives;
Grassmann parity remains a field label and no supermanifold jet calculus is
asserted. -/
structure GlobalBulkAbelianNonminimalSecondOrderJets where
  abelianGhost :
    Sector → FramedSecondOrderJet CoverCoordinates GaugeLieAlgebra
  abelianAntighost :
    Sector → FramedSecondOrderJet CoverCoordinates GaugeLieAlgebra
  abelianNakanishiLautrup :
    Sector → FramedSecondOrderJet CoverCoordinates GaugeLieAlgebra

/-- Simultaneous extraction of all three Abelian nonminimal bulk slots in one
fixed holonomic chart. -/
def globalGaugeFixedBulkAbelianNonminimalSecondOrderJetsAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    GlobalBulkAbelianNonminimalSecondOrderJets where
  abelianGhost := fun sector =>
    globalGaugeFixedBulkAbelianGhostSecondOrderJetAt period hPeriod
      configuration sector patch coordinate
  abelianAntighost := fun sector =>
    globalGaugeFixedBulkAbelianAntighostSecondOrderJetAt period hPeriod
      configuration sector patch coordinate
  abelianNakanishiLautrup := fun sector =>
    globalGaugeFixedBulkAbelianNakanishiLautrupSecondOrderJetAt period hPeriod
      configuration sector patch coordinate

@[simp]
theorem globalGaugeFixedBulkAbelianNonminimalSecondOrderJetsAt_ghost_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) (sector : Sector) :
    ((globalGaugeFixedBulkAbelianNonminimalSecondOrderJetsAt period hPeriod
      configuration patch coordinate).abelianGhost sector).value =
      (configuration.nonminimal.abelian sector).ghost.field
        (patch.coordinateMap (coverToHolonomicEquiv coordinate)) := by
  exact globalGaugeFixedBulkAbelianGhostSecondOrderJetAt_value period hPeriod
    configuration sector patch coordinate

@[simp]
theorem globalGaugeFixedBulkAbelianNonminimalSecondOrderJetsAt_antighost_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) (sector : Sector) :
    ((globalGaugeFixedBulkAbelianNonminimalSecondOrderJetsAt period hPeriod
      configuration patch coordinate).abelianAntighost sector).value =
      (configuration.nonminimal.abelian sector).antighost.field
        (patch.coordinateMap (coverToHolonomicEquiv coordinate)) := by
  exact globalGaugeFixedBulkAbelianAntighostSecondOrderJetAt_value
    period hPeriod configuration sector patch coordinate

@[simp]
theorem globalGaugeFixedBulkAbelianNonminimalSecondOrderJetsAt_nakanishiLautrup_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) (sector : Sector) :
    ((globalGaugeFixedBulkAbelianNonminimalSecondOrderJetsAt period hPeriod
      configuration patch coordinate).abelianNakanishiLautrup sector).value =
      (configuration.nonminimal.abelian sector).nakanishiLautrup.field
        (patch.coordinateMap (coverToHolonomicEquiv coordinate)) := by
  exact globalGaugeFixedBulkAbelianNakanishiLautrupSecondOrderJetAt_value
    period hPeriod configuration sector patch coordinate

end
end P0EFTJanusProgramPActualBulkAbelianNonminimalChartwiseSecondOrderJetExtraction4D
end JanusFormal
