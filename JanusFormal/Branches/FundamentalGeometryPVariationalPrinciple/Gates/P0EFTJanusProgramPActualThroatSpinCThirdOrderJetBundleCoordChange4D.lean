import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleCoordChange4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSemidirectTransportGroupoid4D

/-!
# Coordinate changes for the throat SpinC third-jet atlas

The actual third-order SpinC transport is installed on every double overlap
of the existing SpinC jet cover and totalized by the identity away from the
overlap.  Its algebraic groupoid laws and exact pointwise truncation to the
second-order coordinate change are recorded here.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPActualThroatSpinCThirdOrderJetBundleCoordChange4D

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
open P0EFTJanusNormalPinLiftBoundaryConditions
open P0EFTJanusProgramPD9MatterSpinorDoubledSmoothVectorBundle4D
open P0EFTJanusProgramPD9PrimitiveSpinCBundle4D
open P0EFTJanusProgramPPhysicalSecondOrderJetCarrier4D
open P0EFTJanusProgramPFramedThirdOrderJetConstantFiberBaseChange4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderTrivializationOverlap4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleAtlasData4D
open P0EFTJanusProgramPActualThroatSpinCSecondOrderJetBundleCoordChange4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSemidirectTransport4D
open P0EFTJanusProgramPActualThroatSpinCThirdOrderJetSemidirectTransportGroupoid4D

attribute [local instance 1001]
  NormedAddCommGroup.toAddCommGroup AddCommGroup.toAddCommMonoid

variable (period : Real) (hPeriod : period ≠ 0)
variable (choice : NormalRootChoice)

private abbrev EffectiveThroat :=
  MappingTorus (fixedEquatorData period hPeriod)

private abbrev SpinCThirdJet :=
  FramedThirdOrderJet ThroatCoverCoordinates D9DoubledMatterFiber

private abbrev BundleIndex :=
  ThroatSpinCSecondOrderJetBundleIndex period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω
      (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-- Points at which two SpinC frame/chart pairs are simultaneously valid. -/
abbrev ThroatSpinCThirdOrderJetBundleOverlap
    (first second : BundleIndex period hPeriod) :=
  {current : EffectiveThroat period hPeriod //
    current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod second}

/-- Actual real-linear SpinC third-jet transport on one double overlap. -/
def throatSpinCThirdOrderJetBundleTransportOnOverlap
    (first second : BundleIndex period hPeriod)
    (point : ThroatSpinCThirdOrderJetBundleOverlap period hPeriod
      first second) : SpinCThirdJet →ₗ[Real] SpinCThirdJet :=
  throatSpinCThirdOrderJetSemidirectTransportLinearMapAt period hPeriod choice
    (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod first
      point point.property.1)
    (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod second
      point point.property.2)

/-- Totalized algebraic coordinate change.  Only its values on the double
overlap are used. -/
def throatSpinCThirdOrderJetBundleCoordChange
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod) :
    SpinCThirdJet →ₗ[Real] SpinCThirdJet := by
  classical
  exact if hCurrent : current ∈
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
          throatSpinCSecondOrderJetBundleBaseSet period hPeriod second then
      throatSpinCThirdOrderJetBundleTransportOnOverlap period hPeriod choice
        first second ⟨current, hCurrent⟩
    else
      LinearMap.id

theorem throatSpinCThirdOrderJetBundleCoordChange_eq_of_mem
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod second) :
    throatSpinCThirdOrderJetBundleCoordChange period hPeriod choice
        first second current =
      throatSpinCThirdOrderJetSemidirectTransportLinearMapAt period hPeriod choice
        (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod first
          current hCurrent.1)
        (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod second
          current hCurrent.2) := by
  simp only [throatSpinCThirdOrderJetBundleCoordChange, dif_pos hCurrent,
    throatSpinCThirdOrderJetBundleTransportOnOverlap]

@[simp]
theorem throatSpinCThirdOrderJetBundleCoordChange_apply_of_mem
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod second)
    (jet : SpinCThirdJet) :
    throatSpinCThirdOrderJetBundleCoordChange period hPeriod choice
        first second current jet =
      throatSpinCThirdOrderJetSemidirectTransportAt period hPeriod choice
        (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod first
          current hCurrent.1)
        (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod second
          current hCurrent.2) jet := by
  rw [throatSpinCThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod choice first second current hCurrent]
  rfl

@[simp]
theorem throatSpinCThirdOrderJetBundleCoordChange_self
    (index : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod index) :
    throatSpinCThirdOrderJetBundleCoordChange period hPeriod choice
        index index current =
      LinearMap.id := by
  rw [throatSpinCThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod choice index index current ⟨hCurrent, hCurrent⟩]
  exact throatSpinCThirdOrderJetSemidirectTransportLinearMapAt_self
    period hPeriod choice _

theorem throatSpinCThirdOrderJetBundleCoordChange_comp
    (first middle last : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod middle ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod last) :
    (throatSpinCThirdOrderJetBundleCoordChange period hPeriod choice
        middle last current).comp
        (throatSpinCThirdOrderJetBundleCoordChange period hPeriod choice
          first middle current) =
      throatSpinCThirdOrderJetBundleCoordChange period hPeriod choice
        first last current := by
  rw [throatSpinCThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod choice middle last current ⟨hCurrent.1.2, hCurrent.2⟩]
  rw [throatSpinCThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod choice first middle current ⟨hCurrent.1.1, hCurrent.1.2⟩]
  rw [throatSpinCThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod choice first last current ⟨hCurrent.1.1, hCurrent.2⟩]
  exact
    (throatSpinCThirdOrderJetSemidirectTransportLinearMapAt_comp period
      hPeriod choice
      (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod first
        current hCurrent.1.1)
      (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod middle
        current hCurrent.1.2)
      (throatSpinCSecondOrderJetSemidirectTrivializationChartAt period hPeriod last
        current hCurrent.2)).symm

theorem throatSpinCThirdOrderJetBundleCoordChange_inverse_comp
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod second) :
    (throatSpinCThirdOrderJetBundleCoordChange period hPeriod choice
        second first current).comp
        (throatSpinCThirdOrderJetBundleCoordChange period hPeriod choice
          first second current) =
      LinearMap.id := by
  rw [throatSpinCThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod choice second first current ⟨hCurrent.2, hCurrent.1⟩]
  rw [throatSpinCThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod choice first second current hCurrent]
  exact throatSpinCThirdOrderJetSemidirectTransportLinearMapAt_inverse_comp
    period hPeriod choice _ _

theorem throatSpinCThirdOrderJetBundleCoordChange_comp_inverse
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod second) :
    (throatSpinCThirdOrderJetBundleCoordChange period hPeriod choice
        first second current).comp
        (throatSpinCThirdOrderJetBundleCoordChange period hPeriod choice
          second first current) =
      LinearMap.id := by
  rw [throatSpinCThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod choice first second current hCurrent]
  rw [throatSpinCThirdOrderJetBundleCoordChange_eq_of_mem
    period hPeriod choice second first current ⟨hCurrent.2, hCurrent.1⟩]
  exact throatSpinCThirdOrderJetSemidirectTransportLinearMapAt_comp_inverse
    period hPeriod choice _ _

/-- On every double overlap, third-jet coordinate change truncates exactly to
the existing second-jet coordinate change. -/
@[simp]
theorem throatSpinCThirdOrderJetBundleCoordChange_truncate_apply_of_mem
    (first second : BundleIndex period hPeriod)
    (current : EffectiveThroat period hPeriod)
    (hCurrent : current ∈
      throatSpinCSecondOrderJetBundleBaseSet period hPeriod first ∩
        throatSpinCSecondOrderJetBundleBaseSet period hPeriod second)
    (jet : SpinCThirdJet) :
    (throatSpinCThirdOrderJetBundleCoordChange period hPeriod choice
      first second current jet).toFramedSecondOrderJet =
      throatSpinCSecondOrderJetBundleCoordChange period hPeriod choice
        first second current jet.toFramedSecondOrderJet := by
  rw [throatSpinCThirdOrderJetBundleCoordChange_apply_of_mem
    period hPeriod choice first second current hCurrent]
  rw [throatSpinCSecondOrderJetBundleCoordChange_apply_of_mem
    period hPeriod choice first second current hCurrent]
  exact throatSpinCThirdOrderJetSemidirectTransportAt_truncate period
    hPeriod choice _ _ jet

end
end P0EFTJanusProgramPActualThroatSpinCThirdOrderJetBundleCoordChange4D
end JanusFormal
