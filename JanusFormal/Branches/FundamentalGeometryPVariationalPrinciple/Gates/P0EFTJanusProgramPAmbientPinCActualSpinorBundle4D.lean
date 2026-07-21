import Mathlib.Topology.Instances.Matrix
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPAmbientPinCSpinorRepresentation4D

/-! # Actual four-component spinor bundle of the twisted ambient PinC bundle

The descended `PinC(4)` gamma representation is evaluated on the continuous
transitions of the winding-twisted principal bundle.  This gives a genuine
`FiberBundleCore` with fiber `ℂ⁴`.  Invariance of its Hermitian pairing is a
separate downstream card.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPAmbientPinCActualSpinorBundle4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Matrix
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusPrincipalBundle4D
open P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
open P0EFTJanusProgramPAmbientPinCCechExtension4D
open P0EFTJanusProgramPAmbientCircleWindingBundle4D
open P0EFTJanusProgramPAmbientWindingTwistedPinCActualBundle4D
open P0EFTJanusProgramPAmbientCliffordGammaRepresentation4D
open P0EFTJanusProgramPAmbientPinCSpinorRepresentation4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

def canonicalAmbientPinCSpinorTransitionMatrix
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod) : AmbientComplexMatrix4 :=
  ambientPinCSpinorMatrixRepresentation
    (canonicalAmbientWindingTwistedPinCTransition period hPeriod choice
      first second base)

theorem canonicalAmbientPinCSpinorTransitionMatrix_eq_product
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod) :
    canonicalAmbientPinCSpinorTransitionMatrix period hPeriod choice
        first second base =
      ambientCliffordGammaRepresentation
          (canonicalAmbientPinMinusPrincipalCoordChange period hPeriod
            first second base 1 : AmbientPinMinusCliffordAlgebra) *
        algebraMap Complex AmbientComplexMatrix4
          (canonicalAmbientCirclePrincipalCoordChange period hPeriod choice
            first second base 1 : Circle) := by
  unfold canonicalAmbientPinCSpinorTransitionMatrix
    canonicalAmbientWindingTwistedPinCTransition
  rw [ambientPinCSpinorMatrixRepresentation_mk]
  rfl

theorem canonicalAmbientPinCSpinorTransitionMatrix_continuousOn
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod) :
    ContinuousOn
      (canonicalAmbientPinCSpinorTransitionMatrix period hPeriod choice
        first second)
      (ambientPinMinusBundleBaseSet period hPeriod first ∩
        ambientPinMinusBundleBaseSet period hPeriod second) := by
  let overlap := ambientPinMinusBundleBaseSet period hPeriod first ∩
    ambientPinMinusBundleBaseSet period hPeriod second
  have hPin := canonicalAmbientPinMinusPrincipalTransition_continuousOn
    period hPeriod first second
  have hPinClifford : ContinuousOn
      (fun base : AmbientBase period hPeriod ↦
        (canonicalAmbientPinMinusPrincipalCoordChange period hPeriod
          first second base 1 : AmbientPinMinusCliffordAlgebra)) overlap :=
    continuous_subtype_val.continuousOn.comp hPin (fun _ _ ↦ Set.mem_univ _)
  have hGamma : ContinuousOn
      (fun base : AmbientBase period hPeriod ↦
        ambientCliffordGammaRepresentation
          (canonicalAmbientPinMinusPrincipalCoordChange period hPeriod
            first second base 1 : AmbientPinMinusCliffordAlgebra)) overlap :=
    continuous_ambientCliffordGammaRepresentation.continuousOn.comp
      hPinClifford (fun _ _ ↦ Set.mem_univ _)
  have hPhase := canonicalAmbientCirclePrincipalTransition_continuousOn
    period hPeriod choice first second
  have hPhaseComplex : ContinuousOn
      (fun base : AmbientBase period hPeriod ↦
        (canonicalAmbientCirclePrincipalCoordChange period hPeriod choice
          first second base 1 : Complex)) overlap :=
    continuous_subtype_val.continuousOn.comp hPhase (fun _ _ ↦ Set.mem_univ _)
  have hScalar : ContinuousOn
      (fun base : AmbientBase period hPeriod ↦
        algebraMap Complex AmbientComplexMatrix4
          (canonicalAmbientCirclePrincipalCoordChange period hPeriod choice
            first second base 1 : Circle)) overlap :=
    (continuous_algebraMap Complex AmbientComplexMatrix4).continuousOn.comp
      hPhaseComplex (fun _ _ ↦ Set.mem_univ _)
  rw [show canonicalAmbientPinCSpinorTransitionMatrix period hPeriod choice
      first second = fun base ↦
        ambientCliffordGammaRepresentation
            (canonicalAmbientPinMinusPrincipalCoordChange period hPeriod
              first second base 1 : AmbientPinMinusCliffordAlgebra) *
          algebraMap Complex AmbientComplexMatrix4
            (canonicalAmbientCirclePrincipalCoordChange period hPeriod choice
              first second base 1 : Circle) by
    funext base
    exact canonicalAmbientPinCSpinorTransitionMatrix_eq_product
      period hPeriod choice first second base]
  exact hGamma.mul hScalar

def canonicalAmbientPinCSpinorCoordChange
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod) (spinor : AmbientDiracSpinor4) :
    AmbientDiracSpinor4 :=
  canonicalAmbientPinCSpinorTransitionMatrix period hPeriod choice
    first second base *ᵥ spinor

set_option maxHeartbeats 800000 in
theorem canonicalAmbientPinCSpinorCoordChange_continuousOn
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod) :
    ContinuousOn
      (fun point : AmbientBase period hPeriod × AmbientDiracSpinor4 ↦
        canonicalAmbientPinCSpinorCoordChange period hPeriod choice
          first second point.1 point.2)
      ((ambientPinMinusBundleBaseSet period hPeriod first ∩
        ambientPinMinusBundleBaseSet period hPeriod second) ×ˢ Set.univ) := by
  have hPair : ContinuousOn
      (fun point : AmbientBase period hPeriod × AmbientDiracSpinor4 ↦
        (canonicalAmbientPinCSpinorTransitionMatrix period hPeriod choice
            first second point.1, point.2))
      ((ambientPinMinusBundleBaseSet period hPeriod first ∩
        ambientPinMinusBundleBaseSet period hPeriod second) ×ˢ Set.univ) :=
    ((canonicalAmbientPinCSpinorTransitionMatrix_continuousOn
      period hPeriod choice first second).comp continuousOn_fst (by
        intro point hPoint
        exact hPoint.1)).prodMk continuousOn_snd
  exact (continuous_fst.matrix_mulVec continuous_snd).continuousOn.comp
    hPair (fun _ _ ↦ Set.mem_univ _)

/-- Genuine associated `ℂ⁴` spinor bundle over the ambient Janus quotient. -/
def canonicalAmbientPinCSpinorBundleCore
    (choice : NormalRootChoice) :
    FiberBundleCore (AmbientCover period hPeriod) (AmbientBase period hPeriod)
      AmbientDiracSpinor4 where
  baseSet := ambientPinMinusBundleBaseSet period hPeriod
  isOpen_baseSet := ambientPinMinusBundleBaseSet_isOpen period hPeriod
  indexAt := ambientPinMinusBundleIndexAt period hPeriod
  mem_baseSet_at := mem_ambientPinMinusBundleBaseSet_indexAt period hPeriod
  coordChange := canonicalAmbientPinCSpinorCoordChange period hPeriod choice
  coordChange_self anchor base hBase spinor := by
    have hSelf :=
      (canonicalAmbientWindingTwistedPinCPrincipalBundleCore
        period hPeriod choice).coordChange_self anchor base hBase 1
    change canonicalAmbientWindingTwistedPinCTransition period hPeriod choice
      anchor anchor base * 1 = 1 at hSelf
    rw [mul_one] at hSelf
    unfold canonicalAmbientPinCSpinorCoordChange
      canonicalAmbientPinCSpinorTransitionMatrix
    rw [hSelf, map_one]
    exact Matrix.one_mulVec spinor
  continuousOn_coordChange :=
    canonicalAmbientPinCSpinorCoordChange_continuousOn
      period hPeriod choice
  coordChange_comp first second third base hBase spinor := by
    let core := canonicalAmbientWindingTwistedPinCPrincipalBundleCore
      period hPeriod choice
    have hComp := core.coordChange_comp first second third base hBase 1
    have hTransition :
        canonicalAmbientWindingTwistedPinCTransition period hPeriod choice
              second third base *
            canonicalAmbientWindingTwistedPinCTransition period hPeriod choice
              first second base =
          canonicalAmbientWindingTwistedPinCTransition period hPeriod choice
            first third base := by
      simpa [core, canonicalAmbientWindingTwistedPinCPrincipalBundleCore,
        canonicalAmbientWindingTwistedPinCPrincipalCoordChange] using hComp
    unfold canonicalAmbientPinCSpinorCoordChange
      canonicalAmbientPinCSpinorTransitionMatrix
    rw [Matrix.mulVec_mulVec]
    change ((↑(ambientPinCSpinorMatrixRepresentation
          (canonicalAmbientWindingTwistedPinCTransition period hPeriod choice
            second third base) *
        ambientPinCSpinorMatrixRepresentation
          (canonicalAmbientWindingTwistedPinCTransition period hPeriod choice
            first second base)) : AmbientComplexMatrix4) *ᵥ spinor) = _
    rw [← map_mul, hTransition]

abbrev CanonicalAmbientPinCSpinorFiber
    (choice : NormalRootChoice) :=
  (canonicalAmbientPinCSpinorBundleCore period hPeriod choice).Fiber

@[reducible] def canonicalAmbientPinCSpinorFiber_isFiberBundle
    (choice : NormalRootChoice) :
    FiberBundle AmbientDiracSpinor4
      (CanonicalAmbientPinCSpinorFiber period hPeriod choice) :=
  inferInstance

structure ProgramPAmbientPinCActualSpinorBundleCertificate4D where
  choice : NormalRootChoice
  principalBundle :
    ProgramPAmbientWindingTwistedPinCActualBundleCertificate4D period hPeriod
  spinorCore : FiberBundleCore (AmbientCover period hPeriod)
    (AmbientBase period hPeriod) AmbientDiracSpinor4
  spinorCoreCanonical : spinorCore =
    canonicalAmbientPinCSpinorBundleCore period hPeriod choice

def programPAmbientPinCActualSpinorBundleCertificate4D
    (choice : NormalRootChoice) :
    ProgramPAmbientPinCActualSpinorBundleCertificate4D period hPeriod where
  choice := choice
  principalBundle :=
    programPAmbientWindingTwistedPinCActualBundleCertificate4D
      period hPeriod choice
  spinorCore := canonicalAmbientPinCSpinorBundleCore period hPeriod choice
  spinorCoreCanonical := rfl

theorem programPAmbientPinCActualSpinorBundleCertificate4D_nonempty :
    Nonempty (ProgramPAmbientPinCActualSpinorBundleCertificate4D
      period hPeriod) :=
  ⟨programPAmbientPinCActualSpinorBundleCertificate4D
    period hPeriod .positiveQuarter⟩

end
end P0EFTJanusProgramPAmbientPinCActualSpinorBundle4D
end JanusFormal
