import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorActualBundle4D

/-! # Pullback of the D9 matter-spinor bundle to the effective throat

The actual `MatterFiber` bundle on the ambient quotient is pulled back along
the canonical throat embedding.  No trivialization of its spinor monodromy is
assumed.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPThroatMatterSpinorPullbackBundle4D

set_option autoImplicit false
noncomputable section

open Set Topology
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothThroatEmbedding
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusAmbientPinMinusPrincipalBundle4D
open P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusProgramPD9MatterSpinorHermitianPairing4D
open P0EFTJanusProgramPD9MatterSpinorActualBundle4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev ThroatData := fixedEquatorData period hPeriod
private abbrev ThroatBase := MappingTorus (ThroatData period hPeriod)

def throatAmbientPinCMatterBaseSet
    (anchor : AmbientCover period hPeriod) : Set (ThroatBase period hPeriod) :=
  fixedThroatQuotientInclusion period hPeriod ⁻¹'
    ambientPinMinusBundleBaseSet period hPeriod anchor

theorem throatAmbientPinCMatterBaseSet_isOpen
    (anchor : AmbientCover period hPeriod) :
    IsOpen (throatAmbientPinCMatterBaseSet period hPeriod anchor) :=
  (ambientPinMinusBundleBaseSet_isOpen period hPeriod anchor).preimage
    (continuous_fixedThroatQuotientInclusion period hPeriod)

def throatAmbientPinCMatterIndexAt
    (base : ThroatBase period hPeriod) : AmbientCover period hPeriod :=
  ambientPinMinusBundleIndexAt period hPeriod
    (fixedThroatQuotientInclusion period hPeriod base)

theorem mem_throatAmbientPinCMatterBaseSet_indexAt
    (base : ThroatBase period hPeriod) :
    base ∈ throatAmbientPinCMatterBaseSet period hPeriod
      (throatAmbientPinCMatterIndexAt period hPeriod base) :=
  mem_ambientPinMinusBundleBaseSet_indexAt period hPeriod _

def throatAmbientPinCMatterCoordChange
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod)
    (base : ThroatBase period hPeriod) (matter : MatterFiber) : MatterFiber :=
  canonicalAmbientPinCMatterCoordChange period hPeriod choice first second
    (fixedThroatQuotientInclusion period hPeriod base) matter

set_option maxHeartbeats 800000 in
theorem throatAmbientPinCMatterCoordChange_continuousOn
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod) :
    ContinuousOn
      (fun point : ThroatBase period hPeriod × MatterFiber ↦
        throatAmbientPinCMatterCoordChange period hPeriod choice
          first second point.1 point.2)
      ((throatAmbientPinCMatterBaseSet period hPeriod first ∩
        throatAmbientPinCMatterBaseSet period hPeriod second) ×ˢ Set.univ) := by
  have hInput : Continuous
      (fun point : ThroatBase period hPeriod × MatterFiber ↦
        (fixedThroatQuotientInclusion period hPeriod point.1, point.2)) :=
    (continuous_fixedThroatQuotientInclusion period hPeriod).comp
      continuous_fst |>.prodMk continuous_snd
  unfold throatAmbientPinCMatterCoordChange
  apply (canonicalAmbientPinCMatterCoordChange_continuousOn
    period hPeriod choice first second).comp hInput.continuousOn
  rintro ⟨base, matter⟩ hPoint
  change fixedThroatQuotientInclusion period hPeriod base ∈
      ambientPinMinusBundleBaseSet period hPeriod first ∩
        ambientPinMinusBundleBaseSet period hPeriod second ∧ matter ∈ Set.univ
  simpa [throatAmbientPinCMatterBaseSet] using hPoint

def throatAmbientPinCMatterBundleCore
    (choice : NormalRootChoice) :
    FiberBundleCore (AmbientCover period hPeriod) (ThroatBase period hPeriod)
      MatterFiber where
  baseSet := throatAmbientPinCMatterBaseSet period hPeriod
  isOpen_baseSet := throatAmbientPinCMatterBaseSet_isOpen period hPeriod
  indexAt := throatAmbientPinCMatterIndexAt period hPeriod
  mem_baseSet_at := mem_throatAmbientPinCMatterBaseSet_indexAt period hPeriod
  coordChange := throatAmbientPinCMatterCoordChange period hPeriod choice
  coordChange_self anchor base hBase matter := by
    unfold throatAmbientPinCMatterCoordChange
    exact (canonicalAmbientPinCMatterBundleCore
      period hPeriod choice).coordChange_self anchor
        (fixedThroatQuotientInclusion period hPeriod base) hBase matter
  continuousOn_coordChange :=
    throatAmbientPinCMatterCoordChange_continuousOn period hPeriod choice
  coordChange_comp first second third base hBase matter := by
    unfold throatAmbientPinCMatterCoordChange
    exact (canonicalAmbientPinCMatterBundleCore
      period hPeriod choice).coordChange_comp first second third
        (fixedThroatQuotientInclusion period hPeriod base) hBase matter

theorem throatAmbientPinCMatterCoordChange_preserves_pairing
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod)
    (base : ThroatBase period hPeriod) (left right : MatterFiber) :
    d9MatterSpinorHermitianPairing
        (throatAmbientPinCMatterCoordChange period hPeriod choice
          first second base left)
        (throatAmbientPinCMatterCoordChange period hPeriod choice
          first second base right) =
      d9MatterSpinorHermitianPairing left right := by
  exact canonicalAmbientPinCMatterCoordChange_preserves_pairing
    period hPeriod choice first second
      (fixedThroatQuotientInclusion period hPeriod base) left right

abbrev ThroatAmbientPinCMatterFiber
    (choice : NormalRootChoice) :=
  (throatAmbientPinCMatterBundleCore period hPeriod choice).Fiber

@[reducible] def throatAmbientPinCMatterFiber_isFiberBundle
    (choice : NormalRootChoice) :
    FiberBundle MatterFiber
      (ThroatAmbientPinCMatterFiber period hPeriod choice) :=
  inferInstance

structure ProgramPThroatMatterSpinorPullbackBundleCertificate4D where
  choice : NormalRootChoice
  ambient : ProgramPD9MatterSpinorActualBundleCertificate4D period hPeriod
  core : FiberBundleCore (AmbientCover period hPeriod)
    (ThroatBase period hPeriod) MatterFiber
  coreCanonical : core =
    throatAmbientPinCMatterBundleCore period hPeriod choice
  pairingInvariant : ∀ first second base left right,
    d9MatterSpinorHermitianPairing
        (core.coordChange first second base left)
        (core.coordChange first second base right) =
      d9MatterSpinorHermitianPairing left right

def programPThroatMatterSpinorPullbackBundleCertificate4D
    (choice : NormalRootChoice) :
    ProgramPThroatMatterSpinorPullbackBundleCertificate4D period hPeriod where
  choice := choice
  ambient := programPD9MatterSpinorActualBundleCertificate4D
    period hPeriod choice
  core := throatAmbientPinCMatterBundleCore period hPeriod choice
  coreCanonical := rfl
  pairingInvariant :=
    throatAmbientPinCMatterCoordChange_preserves_pairing
      period hPeriod choice

theorem programPThroatMatterSpinorPullbackBundleCertificate4D_nonempty :
    Nonempty (ProgramPThroatMatterSpinorPullbackBundleCertificate4D
      period hPeriod) :=
  ⟨programPThroatMatterSpinorPullbackBundleCertificate4D
    period hPeriod .positiveQuarter⟩

end
end P0EFTJanusProgramPThroatMatterSpinorPullbackBundle4D
end JanusFormal
