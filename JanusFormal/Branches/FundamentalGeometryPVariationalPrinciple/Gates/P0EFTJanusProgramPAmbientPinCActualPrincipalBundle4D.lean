import Mathlib.Topology.Algebra.Group.Quotient
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPAmbientPinCCechExtension4D

/-! # Actual topological ambient PinC principal bundle

The quotient topology makes the ambient `PinC(4)` quotient a topological
group.  Pushing forward the canonical continuous `Pin⁻(4)` transitions yields
a genuine principal `FiberBundleCore`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPAmbientPinCActualPrincipalBundle4D

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusPrincipalBundle4D
open P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
open P0EFTJanusProgramPAmbientPinCCechExtension4D

variable (period : Real) (hPeriod : period ≠ 0)

theorem continuous_ambientPinMinusToPinC :
    Continuous ambientPinMinusToPinC := by
  change Continuous (fun pin : AmbientCoordinatePinMinusGroup =>
    QuotientGroup.mk ((pin, 1) : AmbientCoordinatePinMinusGroup × Circle))
  exact QuotientGroup.continuous_mk.comp (by fun_prop)

def canonicalAmbientPinCPrincipalCoordChange
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod) (pinC : AmbientPinC4) : AmbientPinC4 :=
  ambientPinMinusToPinC
      (canonicalAmbientPinMinusPrincipalCoordChange period hPeriod
        first second base 1) * pinC

private theorem canonicalAmbientPinCPrincipalCoordChange_continuousOn
    (first second : AmbientCover period hPeriod) :
    ContinuousOn
      (fun point : AmbientBase period hPeriod × AmbientPinC4 =>
        canonicalAmbientPinCPrincipalCoordChange period hPeriod first second
          point.1 point.2)
      ((ambientPinMinusBundleBaseSet period hPeriod first ∩
        ambientPinMinusBundleBaseSet period hPeriod second) ×ˢ Set.univ) := by
  have hTransition : ContinuousOn
      (fun point : AmbientBase period hPeriod × AmbientPinC4 =>
        canonicalAmbientPinMinusPrincipalCoordChange period hPeriod
          first second point.1 1)
      ((ambientPinMinusBundleBaseSet period hPeriod first ∩
        ambientPinMinusBundleBaseSet period hPeriod second) ×ˢ Set.univ) :=
    (canonicalAmbientPinMinusPrincipalTransition_continuousOn
      period hPeriod first second).comp continuousOn_fst (by
        intro point hPoint
        exact hPoint.1)
  change ContinuousOn
      (fun point : AmbientBase period hPeriod × AmbientPinC4 =>
        ambientPinMinusToPinC
            (canonicalAmbientPinMinusPrincipalCoordChange period hPeriod
              first second point.1 1) * point.2)
      ((ambientPinMinusBundleBaseSet period hPeriod first ∩
        ambientPinMinusBundleBaseSet period hPeriod second) ×ˢ Set.univ)
  refine ContinuousOn.mul
    (f := fun point : AmbientBase period hPeriod × AmbientPinC4 =>
      ambientPinMinusToPinC
        (canonicalAmbientPinMinusPrincipalCoordChange period hPeriod
          first second point.1 1))
    (g := fun point : AmbientBase period hPeriod × AmbientPinC4 => point.2) ?_
      continuousOn_snd
  exact continuous_ambientPinMinusToPinC.continuousOn.comp hTransition
    (fun _ _ => Set.mem_univ _)

/-- Genuine topological `PinC(4)` principal-bundle core over the ambient Janus
quotient. -/
def canonicalAmbientPinCPrincipalBundleCore :
    FiberBundleCore (AmbientCover period hPeriod) (AmbientBase period hPeriod)
      AmbientPinC4 where
  baseSet := ambientPinMinusBundleBaseSet period hPeriod
  isOpen_baseSet := ambientPinMinusBundleBaseSet_isOpen period hPeriod
  indexAt := ambientPinMinusBundleIndexAt period hPeriod
  mem_baseSet_at := mem_ambientPinMinusBundleBaseSet_indexAt period hPeriod
  coordChange := canonicalAmbientPinCPrincipalCoordChange period hPeriod
  coordChange_self anchor base hBase pinC := by
    unfold canonicalAmbientPinCPrincipalCoordChange
    have hSelf :=
      (canonicalAmbientPinMinusPrincipalBundleCore period hPeriod).coordChange_self
        anchor base hBase 1
    change canonicalAmbientPinMinusPrincipalCoordChange period hPeriod
      anchor anchor base 1 = 1 at hSelf
    rw [hSelf, map_one, one_mul]
  continuousOn_coordChange :=
    canonicalAmbientPinCPrincipalCoordChange_continuousOn period hPeriod
  coordChange_comp first second third base hBase pinC := by
    let core := canonicalAmbientPinMinusPrincipalBundleCore period hPeriod
    have hComp := core.coordChange_comp first second third base hBase 1
    have hTransition :
        canonicalAmbientPinMinusPrincipalCoordChange period hPeriod
              second third base 1 *
            canonicalAmbientPinMinusPrincipalCoordChange period hPeriod
              first second base 1 =
          canonicalAmbientPinMinusPrincipalCoordChange period hPeriod
            first third base 1 := by
      simpa [core, canonicalAmbientPinMinusPrincipalBundleCore,
        canonicalAmbientPinMinusPrincipalCoordChange] using hComp
    unfold canonicalAmbientPinCPrincipalCoordChange
    rw [← mul_assoc, ← map_mul, hTransition]

abbrev CanonicalAmbientPinCPrincipalFiber :=
  (canonicalAmbientPinCPrincipalBundleCore period hPeriod).Fiber

@[reducible] def canonicalAmbientPinCPrincipalFiber_isFiberBundle :
    FiberBundle AmbientPinC4
      (CanonicalAmbientPinCPrincipalFiber period hPeriod) :=
  inferInstance

def ambientPinCRightAction (pinC groupElement : AmbientPinC4) : AmbientPinC4 :=
  pinC * groupElement

theorem canonicalAmbientPinCPrincipalCoordChange_right_equivariant
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod) (pinC groupElement : AmbientPinC4) :
    canonicalAmbientPinCPrincipalCoordChange period hPeriod first second base
        (ambientPinCRightAction pinC groupElement) =
      ambientPinCRightAction
        (canonicalAmbientPinCPrincipalCoordChange period hPeriod first second
          base pinC) groupElement := by
  simp [canonicalAmbientPinCPrincipalCoordChange, ambientPinCRightAction,
    mul_assoc]

theorem ambientPinCRightAction_free
    (pinC groupElement : AmbientPinC4)
    (hFixed : ambientPinCRightAction pinC groupElement = pinC) :
    groupElement = 1 := by
  simpa [ambientPinCRightAction] using
    congrArg (fun value => pinC⁻¹ * value) hFixed

theorem ambientPinCRightAction_transitive (first second : AmbientPinC4) :
    ∃ groupElement, ambientPinCRightAction first groupElement = second :=
  ⟨first⁻¹ * second, by simp [ambientPinCRightAction]⟩

structure ProgramPAmbientPinCActualPrincipalBundleCertificate4D where
  core : FiberBundleCore (AmbientCover period hPeriod)
    (AmbientBase period hPeriod) AmbientPinC4
  coreCanonical : core = canonicalAmbientPinCPrincipalBundleCore period hPeriod
  coordChangeEquivariant : ∀ first second base pinC groupElement,
    core.coordChange first second base
        (ambientPinCRightAction pinC groupElement) =
      ambientPinCRightAction (core.coordChange first second base pinC)
        groupElement
  rightActionFree : ∀ pinC groupElement,
    ambientPinCRightAction pinC groupElement = pinC → groupElement = 1
  rightActionTransitive : ∀ first second,
    ∃ groupElement, ambientPinCRightAction first groupElement = second

def programPAmbientPinCActualPrincipalBundleCertificate4D :
    ProgramPAmbientPinCActualPrincipalBundleCertificate4D period hPeriod where
  core := canonicalAmbientPinCPrincipalBundleCore period hPeriod
  coreCanonical := rfl
  coordChangeEquivariant :=
    canonicalAmbientPinCPrincipalCoordChange_right_equivariant period hPeriod
  rightActionFree := ambientPinCRightAction_free
  rightActionTransitive := ambientPinCRightAction_transitive

theorem programPAmbientPinCActualPrincipalBundleCertificate4D_nonempty :
    Nonempty
      (ProgramPAmbientPinCActualPrincipalBundleCertificate4D period hPeriod) :=
  ⟨programPAmbientPinCActualPrincipalBundleCertificate4D period hPeriod⟩

end
end P0EFTJanusProgramPAmbientPinCActualPrincipalBundle4D
end JanusFormal
