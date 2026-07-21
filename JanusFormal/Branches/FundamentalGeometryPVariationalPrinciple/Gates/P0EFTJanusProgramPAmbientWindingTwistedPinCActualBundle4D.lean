import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPAmbientCircleWindingBundle4D

/-! # Actual ambient PinC bundle twisted by the winding circle bundle

The canonical ambient `Pin⁻(4)` transition and the continuous quarter-winding
circle transition are paired and sent through the diagonal quotient.  The
result is a genuine topological principal `PinC(4)` bundle core whose
determinant transition is the square of the winding phase.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPAmbientWindingTwistedPinCActualBundle4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusPrincipalBundle4D
open P0EFTJanusMappingTorusAmbientCanonicalReferenceWinding4D
open P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
open P0EFTJanusProgramPAmbientPinCCechExtension4D
open P0EFTJanusProgramPAmbientPinCDeterminantTriviality4D
open P0EFTJanusProgramPAmbientCircleWindingBundle4D
open P0EFTJanusProgramPNormalZ4RootPinMinusAssociation4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

/-- Product transition before multiplication on the principal fiber. -/
def canonicalAmbientWindingTwistedPinCTransition
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod) : AmbientPinC4 :=
  QuotientGroup.mk' ambientPinCDiagonalSubgroup
    (canonicalAmbientPinMinusPrincipalCoordChange period hPeriod
        first second base 1,
      canonicalAmbientCirclePrincipalCoordChange period hPeriod choice
        first second base 1)

theorem canonicalAmbientWindingTwistedPinCTransition_continuousOn
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod) :
    ContinuousOn
      (canonicalAmbientWindingTwistedPinCTransition period hPeriod choice
        first second)
      (ambientPinMinusBundleBaseSet period hPeriod first ∩
        ambientPinMinusBundleBaseSet period hPeriod second) := by
  have hPin := canonicalAmbientPinMinusPrincipalTransition_continuousOn
    period hPeriod first second
  have hCircle := canonicalAmbientCirclePrincipalTransition_continuousOn
    period hPeriod choice first second
  have hProduct : ContinuousOn
      (fun base : AmbientBase period hPeriod ↦
        (canonicalAmbientPinMinusPrincipalCoordChange period hPeriod
            first second base 1,
          canonicalAmbientCirclePrincipalCoordChange period hPeriod choice
            first second base 1))
      (ambientPinMinusBundleBaseSet period hPeriod first ∩
        ambientPinMinusBundleBaseSet period hPeriod second) :=
    hPin.prodMk hCircle
  change ContinuousOn
    (fun base : AmbientBase period hPeriod ↦
      QuotientGroup.mk
        (canonicalAmbientPinMinusPrincipalCoordChange period hPeriod
            first second base 1,
          canonicalAmbientCirclePrincipalCoordChange period hPeriod choice
            first second base 1))
    (ambientPinMinusBundleBaseSet period hPeriod first ∩
      ambientPinMinusBundleBaseSet period hPeriod second)
  exact QuotientGroup.continuous_mk.continuousOn.comp hProduct
    (fun _ _ ↦ Set.mem_univ _)

def canonicalAmbientWindingTwistedPinCPrincipalCoordChange
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod) (pinC : AmbientPinC4) : AmbientPinC4 :=
  canonicalAmbientWindingTwistedPinCTransition period hPeriod choice
    first second base * pinC

theorem canonicalAmbientWindingTwistedPinCPrincipalCoordChange_continuousOn
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod) :
    ContinuousOn
      (fun point : AmbientBase period hPeriod × AmbientPinC4 ↦
        canonicalAmbientWindingTwistedPinCPrincipalCoordChange
          period hPeriod choice first second point.1 point.2)
      ((ambientPinMinusBundleBaseSet period hPeriod first ∩
        ambientPinMinusBundleBaseSet period hPeriod second) ×ˢ Set.univ) := by
  change ContinuousOn
    (fun point : AmbientBase period hPeriod × AmbientPinC4 ↦
      canonicalAmbientWindingTwistedPinCTransition period hPeriod choice
        first second point.1 * point.2)
    ((ambientPinMinusBundleBaseSet period hPeriod first ∩
      ambientPinMinusBundleBaseSet period hPeriod second) ×ˢ Set.univ)
  refine ContinuousOn.mul
    (f := fun point : AmbientBase period hPeriod × AmbientPinC4 ↦
      canonicalAmbientWindingTwistedPinCTransition period hPeriod choice
        first second point.1)
    (g := fun point : AmbientBase period hPeriod × AmbientPinC4 ↦ point.2) ?_
      continuousOn_snd
  exact (canonicalAmbientWindingTwistedPinCTransition_continuousOn
    period hPeriod choice first second).comp continuousOn_fst (by
      intro point hPoint
      exact hPoint.1)

/-- Genuine winding-twisted principal `PinC(4)` bundle core. -/
def canonicalAmbientWindingTwistedPinCPrincipalBundleCore
    (choice : NormalRootChoice) :
    FiberBundleCore (AmbientCover period hPeriod) (AmbientBase period hPeriod)
      AmbientPinC4 where
  baseSet := ambientPinMinusBundleBaseSet period hPeriod
  isOpen_baseSet := ambientPinMinusBundleBaseSet_isOpen period hPeriod
  indexAt := ambientPinMinusBundleIndexAt period hPeriod
  mem_baseSet_at := mem_ambientPinMinusBundleBaseSet_indexAt period hPeriod
  coordChange :=
    canonicalAmbientWindingTwistedPinCPrincipalCoordChange
      period hPeriod choice
  coordChange_self anchor base hBase pinC := by
    have hPin :=
      (canonicalAmbientPinMinusPrincipalBundleCore period hPeriod).coordChange_self
        anchor base hBase 1
    have hCircle :=
      (canonicalAmbientCirclePrincipalBundleCore period hPeriod choice).coordChange_self
        anchor base hBase 1
    change canonicalAmbientPinMinusPrincipalCoordChange period hPeriod
      anchor anchor base 1 = 1 at hPin
    change canonicalAmbientCirclePrincipalCoordChange period hPeriod choice
      anchor anchor base 1 = 1 at hCircle
    unfold canonicalAmbientWindingTwistedPinCPrincipalCoordChange
      canonicalAmbientWindingTwistedPinCTransition
    rw [hPin, hCircle]
    rw [show QuotientGroup.mk' ambientPinCDiagonalSubgroup
      (1, 1) = 1 by
        exact map_one (QuotientGroup.mk' ambientPinCDiagonalSubgroup), one_mul]
  continuousOn_coordChange :=
    canonicalAmbientWindingTwistedPinCPrincipalCoordChange_continuousOn
      period hPeriod choice
  coordChange_comp first second third base hBase pinC := by
    let pinCore := canonicalAmbientPinMinusPrincipalBundleCore period hPeriod
    let circleCore :=
      canonicalAmbientCirclePrincipalBundleCore period hPeriod choice
    have hPinComp := pinCore.coordChange_comp first second third base hBase 1
    have hCircleComp := circleCore.coordChange_comp first second third base hBase 1
    have hPin :
        canonicalAmbientPinMinusPrincipalCoordChange period hPeriod
              second third base 1 *
            canonicalAmbientPinMinusPrincipalCoordChange period hPeriod
              first second base 1 =
          canonicalAmbientPinMinusPrincipalCoordChange period hPeriod
            first third base 1 := by
      simpa [pinCore, canonicalAmbientPinMinusPrincipalBundleCore,
        canonicalAmbientPinMinusPrincipalCoordChange] using hPinComp
    have hCircle :
        canonicalAmbientCirclePrincipalCoordChange period hPeriod choice
              second third base 1 *
            canonicalAmbientCirclePrincipalCoordChange period hPeriod choice
              first second base 1 =
          canonicalAmbientCirclePrincipalCoordChange period hPeriod choice
            first third base 1 := by
      simpa [circleCore, canonicalAmbientCirclePrincipalBundleCore,
        canonicalAmbientCirclePrincipalCoordChange] using hCircleComp
    unfold canonicalAmbientWindingTwistedPinCPrincipalCoordChange
      canonicalAmbientWindingTwistedPinCTransition
    rw [← mul_assoc, ← map_mul]
    change QuotientGroup.mk' ambientPinCDiagonalSubgroup
      (canonicalAmbientPinMinusPrincipalCoordChange period hPeriod
            second third base 1 *
          canonicalAmbientPinMinusPrincipalCoordChange period hPeriod
            first second base 1,
        canonicalAmbientCirclePrincipalCoordChange period hPeriod choice
            second third base 1 *
          canonicalAmbientCirclePrincipalCoordChange period hPeriod choice
            first second base 1) * pinC = _
    rw [hPin, hCircle]

theorem canonicalAmbientWindingTwistedPinC_determinantTransition
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod) :
    ambientPinCDeterminantCharacter
        (canonicalAmbientWindingTwistedPinCTransition period hPeriod choice
          first second base) =
      canonicalAmbientCirclePrincipalCoordChange period hPeriod choice
        first second base 1 ^ 2 := by
  apply ambientPinCDeterminantCharacter_mk

/-- The concrete one-loop transition of the twisted principal bundle has
determinant `-1`; the canonical unit-phase bundle had determinant `1`. -/
theorem canonicalAmbientWindingTwistedPinC_determinantTransition_one_loop
    (choice : NormalRootChoice)
    (anchor : AmbientCover period hPeriod) :
    let base := mappingTorusMk (reflectedSphereData period hPeriod) anchor
    ambientPinCDeterminantCharacter
        (canonicalAmbientWindingTwistedPinCTransition period hPeriod choice
          anchor ((1 : Int) +ᵥ anchor) base) = (-1 : Circle) := by
  let base := mappingTorusMk (reflectedSphereData period hPeriod) anchor
  change ambientPinCDeterminantCharacter
      (canonicalAmbientWindingTwistedPinCTransition period hPeriod choice
        anchor ((1 : Int) +ᵥ anchor) base) = (-1 : Circle)
  rw [canonicalAmbientWindingTwistedPinC_determinantTransition]
  simp only [canonicalAmbientCirclePrincipalCoordChange,
    ambientCircleReferenceTransitionLift, mul_one]
  rw [ambientTransitionWinding_one_loop period hPeriod anchor]
  exact ambientCircleWinding_generator_square choice

abbrev CanonicalAmbientWindingTwistedPinCPrincipalFiber
    (choice : NormalRootChoice) :=
  (canonicalAmbientWindingTwistedPinCPrincipalBundleCore
    period hPeriod choice).Fiber

@[reducible] def canonicalAmbientWindingTwistedPinCPrincipalFiber_isFiberBundle
    (choice : NormalRootChoice) :
    FiberBundle AmbientPinC4
      (CanonicalAmbientWindingTwistedPinCPrincipalFiber
        period hPeriod choice) :=
  inferInstance

structure ProgramPAmbientWindingTwistedPinCActualBundleCertificate4D where
  choice : NormalRootChoice
  circleBundle : ProgramPAmbientCircleWindingBundleCertificate4D period hPeriod
  core : FiberBundleCore (AmbientCover period hPeriod)
    (AmbientBase period hPeriod) AmbientPinC4
  coreCanonical : core =
    canonicalAmbientWindingTwistedPinCPrincipalBundleCore
      period hPeriod choice
  determinantLaw : ∀ first second base,
    ambientPinCDeterminantCharacter
        (canonicalAmbientWindingTwistedPinCTransition period hPeriod choice
          first second base) =
      canonicalAmbientCirclePrincipalCoordChange period hPeriod choice
        first second base 1 ^ 2
  oneLoopDeterminant : ∀ anchor,
    let base := mappingTorusMk (reflectedSphereData period hPeriod) anchor
    ambientPinCDeterminantCharacter
        (canonicalAmbientWindingTwistedPinCTransition period hPeriod choice
          anchor ((1 : Int) +ᵥ anchor) base) = (-1 : Circle)

def programPAmbientWindingTwistedPinCActualBundleCertificate4D
    (choice : NormalRootChoice) :
    ProgramPAmbientWindingTwistedPinCActualBundleCertificate4D
      period hPeriod where
  choice := choice
  circleBundle := programPAmbientCircleWindingBundleCertificate4D
    period hPeriod choice
  core := canonicalAmbientWindingTwistedPinCPrincipalBundleCore
    period hPeriod choice
  coreCanonical := rfl
  determinantLaw :=
    canonicalAmbientWindingTwistedPinC_determinantTransition
      period hPeriod choice
  oneLoopDeterminant :=
    canonicalAmbientWindingTwistedPinC_determinantTransition_one_loop
      period hPeriod choice

theorem programPAmbientWindingTwistedPinCActualBundleCertificate4D_nonempty :
    Nonempty (ProgramPAmbientWindingTwistedPinCActualBundleCertificate4D
      period hPeriod) :=
  ⟨programPAmbientWindingTwistedPinCActualBundleCertificate4D
    period hPeriod .positiveQuarter⟩

end
end P0EFTJanusProgramPAmbientWindingTwistedPinCActualBundle4D
end JanusFormal
