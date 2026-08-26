import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D

/-!
# Local chartwise jets of the global primitive SpinC matter field

At one throat point and one primitive SpinC trivialization containing that
point, this gate extracts the genuine global gauge-fixed matter sections in
source-chart coordinates and forms their second-order jets.

This is strictly a fixed-index local construction.  It does not assert an
overlap law or a global jet-bundle extraction.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalSpinCMatterChartwiseJetExtraction4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Manifold ContDiff
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusD9D10ExactFieldContentBridge4D
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCGeometricDiracDescent4D
open P0EFTJanusProgramPGlobalFieldSpace4D
open P0EFTJanusProgramPGlobalTypedNonminimalFieldSpace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPPhysicalSecondOrderJetChartwiseExtraction4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

local instance throatBaseChartedSpace :
    ChartedSpace ThroatCoverModel (ThroatBase period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance throatBaseIsManifold :
    IsManifold throatCoverModelWithCorners ω (ThroatBase period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- The genuine global matter section, expressed in one fixed primitive
SpinC fiber trivialization and the inverse source chart at `base`. -/
def globalGaugeFixedSpinCMatterChartGerm
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod) :
    ThroatCoverCoordinates → D9DoubledMatterFiber :=
  d9PrimitiveSpinCSmoothSectionLocalValue period hPeriod .positiveQuarter
      (configuration.physical.spinCMatter sector) index ∘
    (extChartAt throatCoverModelWithCorners base).symm

@[simp]
theorem globalGaugeFixedSpinCMatterChartGerm_anchor
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod) :
    globalGaugeFixedSpinCMatterChartGerm period hPeriod configuration sector
        index base (extChartAt throatCoverModelWithCorners base base) =
      d9PrimitiveSpinCSmoothSectionLocalValue period hPeriod .positiveQuarter
        (configuration.physical.spinCMatter sector) index base := by
  unfold globalGaugeFixedSpinCMatterChartGerm
  rw [Function.comp_apply, extChartAt_to_inv]

private theorem globalGaugeFixedSpinCMatterChartGerm_contDiffAt_infty
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    ContDiffAt Real ∞
      (globalGaugeFixedSpinCMatterChartGerm period hPeriod configuration sector
        index base)
      (extChartAt throatCoverModelWithCorners base base) := by
  have hLocal :
      ContMDiffAt throatCoverModelWithCorners
        𝓘(Real, D9DoubledMatterFiber) ∞
        (d9PrimitiveSpinCSmoothSectionLocalValue period hPeriod
          .positiveQuarter (configuration.physical.spinCMatter sector) index)
        base :=
    (d9PrimitiveSpinCSmoothSectionLocalValue_contMDiffOn period hPeriod
      .positiveQuarter (configuration.physical.spinCMatter sector) index)
      |>.contMDiffAt
        ((d9PrimitiveSpinCBaseSet_isOpen period hPeriod index).mem_nhds hBase)
  have hSource := (contMDiffAt_iff_source).mp hLocal
  have hRange : Set.range throatCoverModelWithCorners = Set.univ := by
    ext sourceCoordinate
    simp
  rw [hRange, contMDiffWithinAt_univ] at hSource
  have hFunction :
      d9PrimitiveSpinCSmoothSectionLocalValue period hPeriod .positiveQuarter
          (configuration.physical.spinCMatter sector) index ∘
          (extChartAt throatCoverModelWithCorners base).symm =
        globalGaugeFixedSpinCMatterChartGerm period hPeriod configuration
          sector index base := by
    rfl
  rw [hFunction] at hSource
  exact hSource.contDiffAt

/-- The fixed local representative of every physical SpinC sector is `C²`
at the source-chart anchor. -/
theorem globalGaugeFixedSpinCMatterChartGerm_contDiffAt_two
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (sector : Sector)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    ContDiffAt Real 2
      (globalGaugeFixedSpinCMatterChartGerm period hPeriod configuration sector
        index base)
      (extChartAt throatCoverModelWithCorners base base) :=
  (globalGaugeFixedSpinCMatterChartGerm_contDiffAt_infty period hPeriod
    configuration sector index base hBase).of_le (by
      change ((2 : ℕ∞) : ℕ∞ω) ≤ ((⊤ : ℕ∞) : ℕ∞ω)
      exact WithTop.coe_le_coe.mpr le_top)

/-- Second-order jets of both physical primitive SpinC matter sectors in one
fixed throat chart and one fixed primitive SpinC trivialization. -/
def globalGaugeFixedSpinCMatterSecondOrderJetsAt
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index) :
    Sector →
      FramedSecondOrderJet ThroatCoverCoordinates D9DoubledMatterFiber :=
  fun sector =>
    fixedTrivializationSpinCMatterJetAt
      (globalGaugeFixedSpinCMatterChartGerm period hPeriod configuration sector
        index base)
      (extChartAt throatCoverModelWithCorners base base)
      (globalGaugeFixedSpinCMatterChartGerm_contDiffAt_two period hPeriod
        configuration sector index base hBase)

@[simp]
theorem globalGaugeFixedSpinCMatterSecondOrderJetsAt_value
    (configuration : GlobalGaugeFixedFieldConfiguration period hPeriod)
    (index : D9PrimitiveSpinCIndex period hPeriod)
    (base : ThroatBase period hPeriod)
    (hBase : base ∈ d9PrimitiveSpinCBaseSet period hPeriod index)
    (sector : Sector) :
    (globalGaugeFixedSpinCMatterSecondOrderJetsAt period hPeriod configuration
        index base hBase sector).value =
      d9PrimitiveSpinCSmoothSectionLocalValue period hPeriod .positiveQuarter
        (configuration.physical.spinCMatter sector) index base := by
  change
    globalGaugeFixedSpinCMatterChartGerm period hPeriod configuration sector
        index base (extChartAt throatCoverModelWithCorners base base) = _
  exact globalGaugeFixedSpinCMatterChartGerm_anchor period hPeriod
    configuration sector index base

end
end P0EFTJanusProgramPGlobalSpinCMatterChartwiseJetExtraction4D
end JanusFormal
