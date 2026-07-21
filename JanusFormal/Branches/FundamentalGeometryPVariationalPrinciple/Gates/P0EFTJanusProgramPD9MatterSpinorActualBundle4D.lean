import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D

/-! # Actual D9 matter-spinor bundle

The rank-two complex half-spinor bundle is transported through its canonical
real-linear equivalence with `MatterFiber`, producing the bundle object used by
the D9 field coefficients.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorActualBundle4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusAmbientPinMinusPrincipalBundle4D
open P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPAmbientHalfSpinorActualBundle4D
open P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

theorem continuous_matterFiberHalfSpinorLinearEquiv :
    Continuous matterFiberHalfSpinorLinearEquiv :=
  LinearMap.continuous_of_finiteDimensional
    matterFiberHalfSpinorLinearEquiv.toLinearMap

theorem continuous_matterFiberHalfSpinorLinearEquiv_symm :
    Continuous matterFiberHalfSpinorLinearEquiv.symm :=
  LinearMap.continuous_of_finiteDimensional
    matterFiberHalfSpinorLinearEquiv.symm.toLinearMap

theorem canonicalAmbientPinCMatterCoordChange_continuousOn
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod) :
    ContinuousOn
      (fun point : AmbientBase period hPeriod × MatterFiber ↦
        canonicalAmbientPinCMatterCoordChange period hPeriod choice
          first second point.1 point.2)
      ((ambientPinMinusBundleBaseSet period hPeriod first ∩
        ambientPinMinusBundleBaseSet period hPeriod second) ×ˢ Set.univ) := by
  have hInput : Continuous
      (fun point : AmbientBase period hPeriod × MatterFiber ↦
        (point.1, matterFiberHalfSpinorLinearEquiv point.2)) :=
    continuous_fst.prodMk
      (continuous_matterFiberHalfSpinorLinearEquiv.comp continuous_snd)
  have hAction :=
    (canonicalAmbientPinCHalfSpinorCoordChange_continuousOn
      period hPeriod choice first second).comp hInput.continuousOn (by
        intro (point : AmbientBase period hPeriod × MatterFiber)
          (hPoint : point ∈
            ((ambientPinMinusBundleBaseSet period hPeriod first ∩
              ambientPinMinusBundleBaseSet period hPeriod second) ×ˢ Set.univ))
        exact ⟨hPoint.1, Set.mem_univ _⟩)
  unfold canonicalAmbientPinCMatterCoordChange
  exact continuous_matterFiberHalfSpinorLinearEquiv_symm.continuousOn.comp
    hAction (fun _ _ ↦ Set.mem_univ _)

def canonicalAmbientPinCMatterBundleCore
    (choice : NormalRootChoice) :
    FiberBundleCore (AmbientCover period hPeriod) (AmbientBase period hPeriod)
      MatterFiber where
  baseSet := ambientPinMinusBundleBaseSet period hPeriod
  isOpen_baseSet := ambientPinMinusBundleBaseSet_isOpen period hPeriod
  indexAt := ambientPinMinusBundleIndexAt period hPeriod
  mem_baseSet_at := mem_ambientPinMinusBundleBaseSet_indexAt period hPeriod
  coordChange := canonicalAmbientPinCMatterCoordChange period hPeriod choice
  coordChange_self anchor base hBase matter := by
    have hSelf := (canonicalAmbientPinCHalfSpinorBundleCore
      period hPeriod choice).coordChange_self anchor base hBase
        (matterFiberHalfSpinorLinearEquiv matter)
    change canonicalAmbientPinCHalfSpinorCoordChange period hPeriod choice
      anchor anchor base (matterFiberHalfSpinorLinearEquiv matter) =
        matterFiberHalfSpinorLinearEquiv matter at hSelf
    unfold canonicalAmbientPinCMatterCoordChange
    rw [hSelf, LinearEquiv.symm_apply_apply]
  continuousOn_coordChange :=
    canonicalAmbientPinCMatterCoordChange_continuousOn
      period hPeriod choice
  coordChange_comp first second third base hBase matter := by
    have hHalf :=
      (canonicalAmbientPinCHalfSpinorBundleCore
        period hPeriod choice).coordChange_comp first second third base hBase
          (matterFiberHalfSpinorLinearEquiv matter)
    unfold canonicalAmbientPinCMatterCoordChange
    simp only [LinearEquiv.apply_symm_apply]
    exact congrArg matterFiberHalfSpinorLinearEquiv.symm hHalf

abbrev CanonicalAmbientPinCMatterFiber
    (choice : NormalRootChoice) :=
  (canonicalAmbientPinCMatterBundleCore period hPeriod choice).Fiber

@[reducible] def canonicalAmbientPinCMatterFiber_isFiberBundle
    (choice : NormalRootChoice) :
    FiberBundle MatterFiber
      (CanonicalAmbientPinCMatterFiber period hPeriod choice) :=
  inferInstance

structure ProgramPD9MatterSpinorActualBundleCertificate4D where
  choice : NormalRootChoice
  pairing : ProgramPD9MatterSpinorHermitianPairingCertificate4D
    period hPeriod
  core : FiberBundleCore (AmbientCover period hPeriod)
    (AmbientBase period hPeriod) MatterFiber
  coreCanonical : core =
    canonicalAmbientPinCMatterBundleCore period hPeriod choice
  pairingInvariant : ∀ first second base left right,
    d9MatterSpinorHermitianPairing
        (core.coordChange first second base left)
        (core.coordChange first second base right) =
      d9MatterSpinorHermitianPairing left right

def programPD9MatterSpinorActualBundleCertificate4D
    (choice : NormalRootChoice) :
    ProgramPD9MatterSpinorActualBundleCertificate4D period hPeriod where
  choice := choice
  pairing := programPD9MatterSpinorHermitianPairingCertificate4D
    period hPeriod choice
  core := canonicalAmbientPinCMatterBundleCore period hPeriod choice
  coreCanonical := rfl
  pairingInvariant :=
    canonicalAmbientPinCMatterCoordChange_preserves_pairing
      period hPeriod choice

theorem programPD9MatterSpinorActualBundleCertificate4D_nonempty :
    Nonempty (ProgramPD9MatterSpinorActualBundleCertificate4D
      period hPeriod) :=
  ⟨programPD9MatterSpinorActualBundleCertificate4D
    period hPeriod .positiveQuarter⟩

end
end P0EFTJanusProgramPD9MatterSpinorActualBundle4D
end JanusFormal
