import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatGaugeThirdOrderJetSemidirectTransportGroupoid4D

/-!
# Coordinate changes for the throat gauge third-jet atlas

The actual third-order gauge transport is installed on every double overlap
of the existing gauge-jet cover and totalized by the identity away from the
overlap.  Its algebraic groupoid laws and exact pointwise truncation to the
second-order coordinate change are recorded here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatGaugeThirdOrderJetBundleCoordChange4D

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 500000
set_option maxHeartbeats 600000

noncomputable section

open Set
open scoped Manifold ContDiff RealInnerProductSpace Topology
open Bundle
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusGeneralLorentzMetricThroatTrace4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetPresentationSetoid4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatGaugeSecondOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatGaugeThirdOrderJetSemidirectTransportGroupoid4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev GaugeThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates
    (FramedCovector ThroatCoverCoordinates)

private abbrev BundleIndex :=
  ThroatGaugeSecondOrderJetBundleIndex period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Points at which two frame/chart pairs are simultaneously valid. -/
abbrev ThroatGaugeThirdOrderJetBundleOverlap
    (first second : BundleIndex period hPeriod) :=
  {current : EffectiveThroat period hPeriod //
    current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod second}

/-- Actual real-linear third-jet transport on one double overlap. -/
def throatGaugeThirdOrderJetBundleTransportOnOverlap
    (first second : BundleIndex period hPeriod)
    (point : ThroatGaugeThirdOrderJetBundleOverlap period hPeriod
      first second) : GaugeThirdJet →ₗ[Real] GaugeThirdJet :=
  throatGaugeThirdOrderJetSemidirectTransportLinearMapAt period hPeriod
    (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod first
      point point.property.1)
    (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod second
      point point.property.2)

/-- Totalized algebraic coordinate change.  Only its values on the double
overlap are used. -/
def throatGaugeThirdOrderJetBundleCoordChange
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    GaugeThirdJet →ₗ[Real] GaugeThirdJet := by
  classical
  exact if hCurrent : current ∈
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
          throatGaugeSecondOrderJetBundleBaseSet period hPeriod second then
      throatGaugeThirdOrderJetBundleTransportOnOverlap period hPeriod
        first second ⟨current, hCurrent⟩
    else
      LinearMap.id

theorem throatGaugeThirdOrderJetBundleCoordChange_eq_of_mem
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod second) :
    throatGaugeThirdOrderJetBundleCoordChange period hPeriod
        first second current =
      throatGaugeThirdOrderJetSemidirectTransportLinearMapAt period hPeriod
        (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod first
          current hCurrent.1)
        (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod second
          current hCurrent.2) := by
  simp only [throatGaugeThirdOrderJetBundleCoordChange, dif_pos hCurrent,
    throatGaugeThirdOrderJetBundleTransportOnOverlap]

@[simp]
theorem throatGaugeThirdOrderJetBundleCoordChange_apply_of_mem
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod second)
    (jet : GaugeThirdJet) :
    throatGaugeThirdOrderJetBundleCoordChange period hPeriod
        first second current jet =
      throatGaugeThirdOrderJetSemidirectTransportAt period hPeriod
        (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod first
          current hCurrent.1)
        (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod second
          current hCurrent.2) jet := by
  rw [throatGaugeThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod first second current hCurrent]
  rfl

@[simp]
theorem throatGaugeThirdOrderJetBundleCoordChange_self
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod index) :
    throatGaugeThirdOrderJetBundleCoordChange period hPeriod
        index index current =
      LinearMap.id := by
  rw [throatGaugeThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod index index current ⟨hCurrent, hCurrent⟩]
  exact throatGaugeThirdOrderJetSemidirectTransportLinearMapAt_self
    period hPeriod _

theorem throatGaugeThirdOrderJetBundleCoordChange_comp
    (first middle last : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod middle ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod last) :
    (throatGaugeThirdOrderJetBundleCoordChange period hPeriod
        middle last current).comp
        (throatGaugeThirdOrderJetBundleCoordChange period hPeriod
          first middle current) =
      throatGaugeThirdOrderJetBundleCoordChange period hPeriod
        first last current := by
  rw [throatGaugeThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod middle last current ⟨hCurrent.1.2, hCurrent.2⟩]
  rw [throatGaugeThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod first middle current ⟨hCurrent.1.1, hCurrent.1.2⟩]
  rw [throatGaugeThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod first last current ⟨hCurrent.1.1, hCurrent.2⟩]
  exact
    (throatGaugeThirdOrderJetSemidirectTransportLinearMapAt_comp period
      hPeriod
      (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod first
        current hCurrent.1.1)
      (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod middle
        current hCurrent.1.2)
      (zeroThroatGaugeSecondOrderJetPresentationAt period hPeriod last
        current hCurrent.2)).symm

theorem throatGaugeThirdOrderJetBundleCoordChange_inverse_comp
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod second) :
    (throatGaugeThirdOrderJetBundleCoordChange period hPeriod
        second first current).comp
        (throatGaugeThirdOrderJetBundleCoordChange period hPeriod
          first second current) =
      LinearMap.id := by
  rw [throatGaugeThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod second first current ⟨hCurrent.2, hCurrent.1⟩]
  rw [throatGaugeThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod first second current hCurrent]
  exact throatGaugeThirdOrderJetSemidirectTransportLinearMapAt_inverse_comp
    period hPeriod _ _

theorem throatGaugeThirdOrderJetBundleCoordChange_comp_inverse
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod second) :
    (throatGaugeThirdOrderJetBundleCoordChange period hPeriod
        first second current).comp
        (throatGaugeThirdOrderJetBundleCoordChange period hPeriod
          second first current) =
      LinearMap.id := by
  rw [throatGaugeThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod first second current hCurrent]
  rw [throatGaugeThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod second first current ⟨hCurrent.2, hCurrent.1⟩]
  exact throatGaugeThirdOrderJetSemidirectTransportLinearMapAt_comp_inverse
    period hPeriod _ _

/-- On every double overlap, third-jet coordinate change truncates exactly to
the existing second-jet coordinate change. -/
@[simp]
theorem throatGaugeThirdOrderJetBundleCoordChange_truncate_apply_of_mem
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatGaugeSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatGaugeSecondOrderJetBundleBaseSet period hPeriod second)
    (jet : GaugeThirdJet) :
    (throatGaugeThirdOrderJetBundleCoordChange period hPeriod
      first second current jet).toFramedSecondOrderJet =
      throatGaugeSecondOrderJetBundleCoordChange period hPeriod
        first second current jet.toFramedSecondOrderJet := by
  rw [throatGaugeThirdOrderJetBundleCoordChange_apply_of_mem
    period hPeriod first second current hCurrent]
  rw [throatGaugeSecondOrderJetBundleCoordChange_apply_of_mem
    period hPeriod first second current hCurrent]
  exact throatGaugeThirdOrderJetSemidirectTransportAt_truncate period
    hPeriod _ _ jet

end
end P0EFTJanusProgramPActualThroatGaugeThirdOrderJetBundleCoordChange4D
end JanusFormal
