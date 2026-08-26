import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D

/-!
# Actual bulk diffeomorphism-nonminimal second jets

The three genuine smooth tangent fields in the gauge-fixed nonminimal packet
are written in the tangent-bundle trivialization centered at one actual bulk
point.  Their coordinate representatives are then pulled back through a
supplied holonomic chart and the fixed linear identification between
`CoverCoordinates` and the chart's `Fin 4` model.

This produces exactly the three `FramedSecondOrderJet CoverCoordinates
CoverCoordinates` fields used by the bulk physical carrier.  The extraction
is local to the selected chart and tangent trivialization.  No overlap law,
global jet bundle, BRST orbit classification, or complete bulk-carrier
constructor is asserted.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualBulkDiffeomorphismNonminimalChartwiseSecondOrderJetExtraction4D

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralScalarFunctionalAction4D
open P0EFTJanusMappingTorusGeneralLorentzMetricLocalLeviCivitaPatch4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D
open P0EFTJanusProgramPGlobalMetricChartwiseSecondOrderJetExtraction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev SphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient :=
  MappingTorus (SphereData period hPeriod)

local instance effectiveQuotientChartedSpace :
    ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

local instance effectiveQuotientIsManifold :
    IsManifold coverModelWithCorners ω
      (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private abbrev TangentFiber
    (point : EffectiveQuotient period hPeriod) :=
  TangentSpace coverModelWithCorners point

/-! ## Fixed tangent coordinates and holonomic pullback -/

/-- Coordinates of a genuine smooth tangent field in the tangent
trivialization centered at `anchor`. -/
def bulkTangentFieldCoordinates
    (field : SmoothTangentField period hPeriod)
    (anchor current : EffectiveQuotient period hPeriod) :
    CoverCoordinates :=
  ((trivializationAt CoverCoordinates (TangentFiber period hPeriod) anchor)
    ⟨current, field current⟩).2

@[simp]
theorem bulkTangentFieldCoordinates_anchor
    (field : SmoothTangentField period hPeriod)
    (anchor : EffectiveQuotient period hPeriod) :
    bulkTangentFieldCoordinates period hPeriod field anchor anchor =
      ((trivializationAt CoverCoordinates
        (TangentFiber period hPeriod) anchor) ⟨anchor, field anchor⟩).2 :=
  rfl

/-- Smoothness of a global tangent section gives smooth fixed-trivialization
coordinates at the center point. -/
theorem bulkTangentFieldCoordinates_contMDiffAt
    (field : SmoothTangentField period hPeriod)
    (anchor : EffectiveQuotient period hPeriod) :
    ContMDiffAt coverModelWithCorners
      (modelWithCornersSelf Real CoverCoordinates) ∞
      (bulkTangentFieldCoordinates period hPeriod field anchor) anchor := by
  let trivialization :=
    trivializationAt CoverCoordinates (TangentFiber period hPeriod) anchor
  have hBase : anchor ∈ trivialization.baseSet :=
    mem_baseSet_trivializationAt CoverCoordinates
      (TangentFiber period hPeriod) anchor
  exact (trivialization.contMDiffAt_section_iff hBase).mp
    (field.contMDiff anchor)

/-- The supplied holonomic chart, with its `Fin 4` coordinate domain
transported to the carrier's split cover-coordinate model. -/
def bulkHolonomicChartMap
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    CoverCoordinates → EffectiveQuotient period hPeriod :=
  fun coordinate =>
    patch.coordinateMap (coverToHolonomicEquiv coordinate)

theorem bulkHolonomicChartMap_contMDiff
    (patch : SmoothHolonomicFrameChart4 period hPeriod) :
    ContMDiff (modelWithCornersSelf Real CoverCoordinates)
      coverModelWithCorners ∞
      (bulkHolonomicChartMap period hPeriod patch) :=
  patch.coordinateMap_contMDiff.comp
    coverToHolonomicEquiv.contDiff.contMDiff

/-- Coordinate germ of one tangent field.  The fiber trivialization stays
fixed at the point represented by `coordinate`. -/
def bulkTangentFieldHolonomicChartGerm
    (field : SmoothTangentField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    CoverCoordinates → CoverCoordinates :=
  fun current =>
    bulkTangentFieldCoordinates period hPeriod field
      (bulkHolonomicChartMap period hPeriod patch coordinate)
      (bulkHolonomicChartMap period hPeriod patch current)

@[simp]
theorem bulkTangentFieldHolonomicChartGerm_center
    (field : SmoothTangentField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    bulkTangentFieldHolonomicChartGerm period hPeriod field patch coordinate
        coordinate =
      bulkTangentFieldCoordinates period hPeriod field
        (bulkHolonomicChartMap period hPeriod patch coordinate)
        (bulkHolonomicChartMap period hPeriod patch coordinate) :=
  rfl

/-- The pulled-back tangent-coordinate germ is `C²` at the selected
cover-coordinate point. -/
theorem bulkTangentFieldHolonomicChartGerm_contDiffAt_two
    (field : SmoothTangentField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    ContDiffAt Real 2
      (bulkTangentFieldHolonomicChartGerm
        period hPeriod field patch coordinate) coordinate := by
  let anchor := bulkHolonomicChartMap period hPeriod patch coordinate
  have hField : ContMDiffAt coverModelWithCorners
      (modelWithCornersSelf Real CoverCoordinates) 2
      (bulkTangentFieldCoordinates period hPeriod field anchor) anchor :=
    (bulkTangentFieldCoordinates_contMDiffAt
      period hPeriod field anchor).of_le (by
        show (2 : ℕ∞ω) ≤ ∞
        exact WithTop.coe_le_coe.mpr le_top)
  have hMap : ContMDiffAt
      (modelWithCornersSelf Real CoverCoordinates) coverModelWithCorners 2
      (bulkHolonomicChartMap period hPeriod patch) coordinate :=
    (bulkHolonomicChartMap_contMDiff period hPeriod patch).of_le (by
      show (2 : ℕ∞ω) ≤ ∞
      exact WithTop.coe_le_coe.mpr le_top) |>.contMDiffAt
  have hComposed := hField.comp coordinate hMap
  have hLocal : ContMDiffAt
      (modelWithCornersSelf Real CoverCoordinates)
      (modelWithCornersSelf Real CoverCoordinates) 2
      (bulkTangentFieldHolonomicChartGerm
        period hPeriod field patch coordinate) coordinate := by
    change ContMDiffAt
      (modelWithCornersSelf Real CoverCoordinates)
      (modelWithCornersSelf Real CoverCoordinates) 2
      (fun current =>
        bulkTangentFieldCoordinates period hPeriod field
          (bulkHolonomicChartMap period hPeriod patch coordinate)
          (bulkHolonomicChartMap period hPeriod patch current)) coordinate
    exact hComposed
  have hSource := (contMDiffAt_iff_source).mp hLocal
  have hRange : Set.range
      (modelWithCornersSelf Real CoverCoordinates) = Set.univ := by
    ext current
    simp
  rw [hRange, contMDiffWithinAt_univ] at hSource
  exact hSource.contDiffAt

/-! ## Generic tangent-field jet -/

/-- Actual second jet of one smooth tangent field in the chosen chart and
fixed tangent trivialization. -/
def bulkTangentFieldHolonomicSecondOrderJetAt
    (field : SmoothTangentField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    FramedSecondOrderJet CoverCoordinates CoverCoordinates :=
  chartwiseSecondOrderJetAt
    (bulkTangentFieldHolonomicChartGerm
      period hPeriod field patch coordinate)
    coordinate
    (bulkTangentFieldHolonomicChartGerm_contDiffAt_two
      period hPeriod field patch coordinate)

@[simp]
theorem bulkTangentFieldHolonomicSecondOrderJetAt_value
    (field : SmoothTangentField period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    (bulkTangentFieldHolonomicSecondOrderJetAt
      period hPeriod field patch coordinate).value =
      bulkTangentFieldCoordinates period hPeriod field
        (bulkHolonomicChartMap period hPeriod patch coordinate)
        (bulkHolonomicChartMap period hPeriod patch coordinate) := by
  rw [bulkTangentFieldHolonomicSecondOrderJetAt,
    chartwiseSecondOrderJetAt_value,
    bulkTangentFieldHolonomicChartGerm_center]

/-! ## The three actual nonminimal diffeomorphism jets -/

def globalGaugeFixedBulkDiffeomorphismGhostSecondOrderJetAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    FramedSecondOrderJet CoverCoordinates CoverCoordinates :=
  bulkTangentFieldHolonomicSecondOrderJetAt period hPeriod
    configuration.nonminimal.diffeomorphism.ghost.field patch coordinate

def globalGaugeFixedBulkDiffeomorphismAntighostSecondOrderJetAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    FramedSecondOrderJet CoverCoordinates CoverCoordinates :=
  bulkTangentFieldHolonomicSecondOrderJetAt period hPeriod
    configuration.nonminimal.diffeomorphism.antighost.field patch coordinate

def globalGaugeFixedBulkDiffeomorphismNakanishiLautrupSecondOrderJetAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    FramedSecondOrderJet CoverCoordinates CoverCoordinates :=
  bulkTangentFieldHolonomicSecondOrderJetAt period hPeriod
    configuration.nonminimal.diffeomorphism.nakanishiLautrup.field
    patch coordinate

@[simp]
theorem globalGaugeFixedBulkDiffeomorphismGhostSecondOrderJetAt_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    (globalGaugeFixedBulkDiffeomorphismGhostSecondOrderJetAt
      period hPeriod configuration patch coordinate).value =
      bulkTangentFieldCoordinates period hPeriod
        configuration.nonminimal.diffeomorphism.ghost.field
        (bulkHolonomicChartMap period hPeriod patch coordinate)
        (bulkHolonomicChartMap period hPeriod patch coordinate) :=
  bulkTangentFieldHolonomicSecondOrderJetAt_value period hPeriod _ _ _

@[simp]
theorem globalGaugeFixedBulkDiffeomorphismAntighostSecondOrderJetAt_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    (globalGaugeFixedBulkDiffeomorphismAntighostSecondOrderJetAt
      period hPeriod configuration patch coordinate).value =
      bulkTangentFieldCoordinates period hPeriod
        configuration.nonminimal.diffeomorphism.antighost.field
        (bulkHolonomicChartMap period hPeriod patch coordinate)
        (bulkHolonomicChartMap period hPeriod patch coordinate) :=
  bulkTangentFieldHolonomicSecondOrderJetAt_value period hPeriod _ _ _

@[simp]
theorem globalGaugeFixedBulkDiffeomorphismNakanishiLautrupSecondOrderJetAt_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    (globalGaugeFixedBulkDiffeomorphismNakanishiLautrupSecondOrderJetAt
      period hPeriod configuration patch coordinate).value =
      bulkTangentFieldCoordinates period hPeriod
        configuration.nonminimal.diffeomorphism.nakanishiLautrup.field
        (bulkHolonomicChartMap period hPeriod patch coordinate)
        (bulkHolonomicChartMap period hPeriod patch coordinate) :=
  bulkTangentFieldHolonomicSecondOrderJetAt_value period hPeriod _ _ _

/-- The exact three-field subsector of the bulk physical carrier. -/
structure ActualBulkDiffeomorphismNonminimalChartwiseSecondOrderJets
    (_configuration : GlobalGaugeFixedFieldConfiguration period hPeriod) where
  point : ProgramPBulkJetBase period hPeriod
  diffeomorphismGhost :
    FramedSecondOrderJet CoverCoordinates CoverCoordinates
  diffeomorphismAntighost :
    FramedSecondOrderJet CoverCoordinates CoverCoordinates
  diffeomorphismNakanishiLautrup :
    FramedSecondOrderJet CoverCoordinates CoverCoordinates

/-- Simultaneous extraction of the three actual diffeomorphism-nonminimal
fields at one bulk chart point. -/
def globalGaugeFixedActualBulkDiffeomorphismNonminimalSecondOrderJetsAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    ActualBulkDiffeomorphismNonminimalChartwiseSecondOrderJets
      period hPeriod configuration where
  point := bulkHolonomicChartMap period hPeriod patch coordinate
  diffeomorphismGhost :=
    globalGaugeFixedBulkDiffeomorphismGhostSecondOrderJetAt
      period hPeriod configuration patch coordinate
  diffeomorphismAntighost :=
    globalGaugeFixedBulkDiffeomorphismAntighostSecondOrderJetAt
      period hPeriod configuration patch coordinate
  diffeomorphismNakanishiLautrup :=
    globalGaugeFixedBulkDiffeomorphismNakanishiLautrupSecondOrderJetAt
      period hPeriod configuration patch coordinate

@[simp]
theorem globalGaugeFixedActualBulkDiffeomorphismNonminimalSecondOrderJetsAt_ghost_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    (globalGaugeFixedActualBulkDiffeomorphismNonminimalSecondOrderJetsAt
      period hPeriod configuration patch coordinate).diffeomorphismGhost.value =
      bulkTangentFieldCoordinates period hPeriod
        configuration.nonminimal.diffeomorphism.ghost.field
        (bulkHolonomicChartMap period hPeriod patch coordinate)
        (bulkHolonomicChartMap period hPeriod patch coordinate) :=
  globalGaugeFixedBulkDiffeomorphismGhostSecondOrderJetAt_value
    period hPeriod configuration patch coordinate

@[simp]
theorem globalGaugeFixedActualBulkDiffeomorphismNonminimalSecondOrderJetsAt_antighost_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    (globalGaugeFixedActualBulkDiffeomorphismNonminimalSecondOrderJetsAt
      period hPeriod configuration patch coordinate).diffeomorphismAntighost.value =
      bulkTangentFieldCoordinates period hPeriod
        configuration.nonminimal.diffeomorphism.antighost.field
        (bulkHolonomicChartMap period hPeriod patch coordinate)
        (bulkHolonomicChartMap period hPeriod patch coordinate) :=
  globalGaugeFixedBulkDiffeomorphismAntighostSecondOrderJetAt_value
    period hPeriod configuration patch coordinate

@[simp]
theorem globalGaugeFixedActualBulkDiffeomorphismNonminimalSecondOrderJetsAt_nakanishiLautrup_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (patch : SmoothHolonomicFrameChart4 period hPeriod)
    (coordinate : CoverCoordinates) :
    (globalGaugeFixedActualBulkDiffeomorphismNonminimalSecondOrderJetsAt
      period hPeriod configuration patch coordinate).diffeomorphismNakanishiLautrup.value =
      bulkTangentFieldCoordinates period hPeriod
        configuration.nonminimal.diffeomorphism.nakanishiLautrup.field
        (bulkHolonomicChartMap period hPeriod patch coordinate)
        (bulkHolonomicChartMap period hPeriod patch coordinate) :=
  globalGaugeFixedBulkDiffeomorphismNakanishiLautrupSecondOrderJetAt_value
    period hPeriod configuration patch coordinate

end
end P0EFTJanusProgramPActualBulkDiffeomorphismNonminimalChartwiseSecondOrderJetExtraction4D
end JanusFormal
