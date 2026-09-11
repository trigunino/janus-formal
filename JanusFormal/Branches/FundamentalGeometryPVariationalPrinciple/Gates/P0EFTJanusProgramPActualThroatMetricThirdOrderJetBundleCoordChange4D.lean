import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatMetricThirdOrderJetSemidirectTransportGroupoid4D

/-!
# Coordinate changes for the throat metric third-jet atlas

The actual third-order metric transport is installed on every double overlap
of the existing metric-jet cover and totalized by the identity away from the
overlap.  Its algebraic groupoid laws and exact pointwise truncation to the
second-order coordinate change are recorded here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatMetricThirdOrderJetBundleCoordChange4D

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
open P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatMetricSecondOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatMetricThirdOrderJetSemidirectTransportGroupoid4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev TensorModel :=
  FramedCovariantTwoTensor ThroatCoverCoordinates

attribute [local instance]
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorModelNormedAddCommGroup
  P0EFTJanusProgramPActualThroatCovariantTwoTensorSecondOrderFrameOverlap4D.tensorModelNormedSpace

private abbrev MetricThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates TensorModel

private abbrev BundleIndex :=
  ThroatMetricSecondOrderJetBundleIndex period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Points at which two frame/chart pairs are simultaneously valid. -/
abbrev ThroatMetricThirdOrderJetBundleOverlap
    (first second : BundleIndex period hPeriod) :=
  {current : EffectiveThroat period hPeriod //
    current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod second}

/-- Actual real-linear third-jet transport on one double overlap. -/
def throatMetricThirdOrderJetBundleTransportOnOverlap
    (first second : BundleIndex period hPeriod)
    (point : ThroatMetricThirdOrderJetBundleOverlap period hPeriod
      first second) : MetricThirdJet →ₗ[Real] MetricThirdJet :=
  throatMetricThirdOrderJetSemidirectTransportLinearMapAt period hPeriod
    (throatMetricSecondOrderJetFrameChartAt period hPeriod first
      point point.property.1)
    (throatMetricSecondOrderJetFrameChartAt period hPeriod second
      point point.property.2)

/-- Totalized algebraic coordinate change.  Only its values on the double
overlap are used. -/
def throatMetricThirdOrderJetBundleCoordChange
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    MetricThirdJet →ₗ[Real] MetricThirdJet := by
  classical
  exact if hCurrent : current ∈
        throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
          throatMetricSecondOrderJetBundleBaseSet period hPeriod second then
      throatMetricThirdOrderJetBundleTransportOnOverlap period hPeriod
        first second ⟨current, hCurrent⟩
    else
      LinearMap.id

theorem throatMetricThirdOrderJetBundleCoordChange_eq_of_mem
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod second) :
    throatMetricThirdOrderJetBundleCoordChange period hPeriod
        first second current =
      throatMetricThirdOrderJetSemidirectTransportLinearMapAt period hPeriod
        (throatMetricSecondOrderJetFrameChartAt period hPeriod first
          current hCurrent.1)
        (throatMetricSecondOrderJetFrameChartAt period hPeriod second
          current hCurrent.2) := by
  simp only [throatMetricThirdOrderJetBundleCoordChange, dif_pos hCurrent,
    throatMetricThirdOrderJetBundleTransportOnOverlap]

@[simp]
theorem throatMetricThirdOrderJetBundleCoordChange_apply_of_mem
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod second)
    (jet : MetricThirdJet) :
    throatMetricThirdOrderJetBundleCoordChange period hPeriod
        first second current jet =
      throatMetricThirdOrderJetSemidirectTransportAt period hPeriod
        (throatMetricSecondOrderJetFrameChartAt period hPeriod first
          current hCurrent.1)
        (throatMetricSecondOrderJetFrameChartAt period hPeriod second
          current hCurrent.2) jet := by
  rw [throatMetricThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod first second current hCurrent]
  rfl

@[simp]
theorem throatMetricThirdOrderJetBundleCoordChange_self
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod index) :
    throatMetricThirdOrderJetBundleCoordChange period hPeriod
        index index current =
      LinearMap.id := by
  rw [throatMetricThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod index index current ⟨hCurrent, hCurrent⟩]
  exact throatMetricThirdOrderJetSemidirectTransportLinearMapAt_self
    period hPeriod _

theorem throatMetricThirdOrderJetBundleCoordChange_comp
    (first middle last : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod middle ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod last) :
    (throatMetricThirdOrderJetBundleCoordChange period hPeriod
        middle last current).comp
        (throatMetricThirdOrderJetBundleCoordChange period hPeriod
          first middle current) =
      throatMetricThirdOrderJetBundleCoordChange period hPeriod
        first last current := by
  rw [throatMetricThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod middle last current ⟨hCurrent.1.2, hCurrent.2⟩]
  rw [throatMetricThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod first middle current ⟨hCurrent.1.1, hCurrent.1.2⟩]
  rw [throatMetricThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod first last current ⟨hCurrent.1.1, hCurrent.2⟩]
  exact
    (throatMetricThirdOrderJetSemidirectTransportLinearMapAt_comp period
      hPeriod
      (throatMetricSecondOrderJetFrameChartAt period hPeriod first
        current hCurrent.1.1)
      (throatMetricSecondOrderJetFrameChartAt period hPeriod middle
        current hCurrent.1.2)
      (throatMetricSecondOrderJetFrameChartAt period hPeriod last
        current hCurrent.2)).symm

theorem throatMetricThirdOrderJetBundleCoordChange_inverse_comp
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod second) :
    (throatMetricThirdOrderJetBundleCoordChange period hPeriod
        second first current).comp
        (throatMetricThirdOrderJetBundleCoordChange period hPeriod
          first second current) =
      LinearMap.id := by
  rw [throatMetricThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod second first current ⟨hCurrent.2, hCurrent.1⟩]
  rw [throatMetricThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod first second current hCurrent]
  exact throatMetricThirdOrderJetSemidirectTransportLinearMapAt_inverse_comp
    period hPeriod _ _

theorem throatMetricThirdOrderJetBundleCoordChange_comp_inverse
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod second) :
    (throatMetricThirdOrderJetBundleCoordChange period hPeriod
        first second current).comp
        (throatMetricThirdOrderJetBundleCoordChange period hPeriod
          second first current) =
      LinearMap.id := by
  rw [throatMetricThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod first second current hCurrent]
  rw [throatMetricThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod second first current ⟨hCurrent.2, hCurrent.1⟩]
  exact throatMetricThirdOrderJetSemidirectTransportLinearMapAt_comp_inverse
    period hPeriod _ _

/-- On every double overlap, third-jet coordinate change truncates exactly to
the existing second-jet coordinate change. -/
@[simp]
theorem throatMetricThirdOrderJetBundleCoordChange_truncate_apply_of_mem
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatMetricSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatMetricSecondOrderJetBundleBaseSet period hPeriod second)
    (jet : MetricThirdJet) :
    (throatMetricThirdOrderJetBundleCoordChange period hPeriod
      first second current jet).toFramedSecondOrderJet =
      throatMetricSecondOrderJetBundleCoordChange period hPeriod
        first second current jet.toFramedSecondOrderJet := by
  rw [throatMetricThirdOrderJetBundleCoordChange_apply_of_mem
    period hPeriod first second current hCurrent]
  rw [throatMetricSecondOrderJetBundleCoordChange_apply_of_mem
    period hPeriod first second current hCurrent]
  exact throatMetricThirdOrderJetSemidirectTransportAt_truncate period
    hPeriod _ _ jet

end
end P0EFTJanusProgramPActualThroatMetricThirdOrderJetBundleCoordChange4D
end JanusFormal
