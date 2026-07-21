import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D

/-! # Actual rank-two half-spinor bundle

The invariant upper block of the actual ambient Dirac bundle is extracted by
continuous linear inclusion and projection, yielding a genuine rank-two
complex `FiberBundleCore`.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPAmbientHalfSpinorActualBundle4D

set_option autoImplicit false
noncomputable section

open Set Topology
open scoped Matrix
open P0EFTJanusMappingTorusAmbientPinMinusPrincipalBundle4D
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientCanonicalReferencePinMinusCech4D
open P0EFTJanusMappingTorusAmbientCanonicalPinMinusActualPrincipalBundle4D
open P0EFTJanusMappingTorusAmbientCanonicalReferenceWinding4D
open P0EFTJanusProgramPNormalZ4RootPinMinusAssociation4D
open P0EFTJanusProgramPAmbientCircleWindingBundle4D
open P0EFTJanusProgramPAmbientCliffordGammaRepresentation4D
open P0EFTJanusProgramPAmbientPinCSpinorRepresentation4D
open P0EFTJanusProgramPAmbientPinCActualSpinorBundle4D
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
open P0EFTJanusNormalPinLiftBoundaryConditions

variable (period : Real) (hPeriod : period ≠ 0)

def ambientHalfSpinorProject (spinor : AmbientDiracSpinor4) :
    AmbientHalfSpinor2 :=
  fun index ↦ spinor ⟨index.val, index.isLt.trans (by decide)⟩

@[simp] theorem ambientHalfSpinorProject_embed
    (spinor : AmbientHalfSpinor2) :
    ambientHalfSpinorProject (ambientHalfSpinorEmbed spinor) = spinor := by
  funext index
  fin_cases index <;> simp [ambientHalfSpinorProject, ambientHalfSpinorEmbed]

def ambientHalfSpinorEmbedLinear :
    AmbientHalfSpinor2 →ₗ[Complex] AmbientDiracSpinor4 where
  toFun := ambientHalfSpinorEmbed
  map_add' first second := by
    funext index
    fin_cases index <;> simp [ambientHalfSpinorEmbed]
  map_smul' scalar spinor := by
    funext index
    fin_cases index <;> simp [ambientHalfSpinorEmbed]

def ambientHalfSpinorProjectLinear :
    AmbientDiracSpinor4 →ₗ[Complex] AmbientHalfSpinor2 where
  toFun := ambientHalfSpinorProject
  map_add' first second := by
    funext index
    fin_cases index <;> rfl
  map_smul' scalar spinor := by
    funext index
    fin_cases index <;> rfl

theorem continuous_ambientHalfSpinorEmbed :
    Continuous ambientHalfSpinorEmbed :=
  LinearMap.continuous_of_finiteDimensional ambientHalfSpinorEmbedLinear

theorem continuous_ambientHalfSpinorProject :
    Continuous ambientHalfSpinorProject :=
  LinearMap.continuous_of_finiteDimensional ambientHalfSpinorProjectLinear

@[simp] theorem ambientHalfSpinorEmbed_smul
    (scalar : Complex) (spinor : AmbientHalfSpinor2) :
    ambientHalfSpinorEmbed (scalar • spinor) =
      scalar • ambientHalfSpinorEmbed spinor := by
  funext index
  fin_cases index <;> simp [ambientHalfSpinorEmbed]

def canonicalAmbientPinCHalfSpinorCoordChange
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod) (spinor : AmbientHalfSpinor2) :
    AmbientHalfSpinor2 :=
  ambientHalfSpinorProject
    (canonicalAmbientPinCSpinorCoordChange period hPeriod choice
      first second base (ambientHalfSpinorEmbed spinor))

theorem canonicalAmbientPinCSpinorCoordChange_preserves_halfSpinor
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod)
    (base : AmbientBase period hPeriod) (spinor : AmbientHalfSpinor2) :
    canonicalAmbientPinCSpinorCoordChange period hPeriod choice
        first second base (ambientHalfSpinorEmbed spinor) =
      ambientHalfSpinorEmbed
        (canonicalAmbientPinCHalfSpinorCoordChange period hPeriod choice
          first second base spinor) := by
  let winding : ZMod 4 :=
    ambientTransitionWinding period hPeriod first second
      (P0EFTJanusMappingTorusAmbientTangentOrientationCocycle.ambientQuotientLocalChart
        period hPeriod first base)
  let phase : Circle := normalRootCircleCharacter choice winding
  have hImage :
      canonicalAmbientPinCSpinorCoordChange period hPeriod choice
          first second base (ambientHalfSpinorEmbed spinor) =
        ambientHalfSpinorEmbed
          ((ambientHalfGammaZ4Representation winding :
              AmbientComplexMatrix2) *ᵥ ((phase : Complex) • spinor)) := by
    unfold canonicalAmbientPinCSpinorCoordChange
    rw [canonicalAmbientPinCSpinorTransitionMatrix_eq_product,
      ← Matrix.mulVec_mulVec]
    unfold canonicalAmbientPinMinusPrincipalCoordChange
      canonicalAmbientCirclePrincipalCoordChange
      canonicalAmbientReferencePinMinusTransitionLift
      ambientCircleReferenceTransitionLift
    simp only [mul_one]
    change
      (ambientPinMinusGammaRepresentation
            (ambientPinMinusReferenceZ4Character winding) :
          AmbientComplexMatrix4) *ᵥ
          ((ambientCircleGammaScalarRepresentation phase :
              AmbientComplexMatrix4) *ᵥ ambientHalfSpinorEmbed spinor) = _
    rw [P0EFTJanusProgramPAmbientPinCSpinorHermitianBundle4D.ambientCircleGammaScalarRepresentation_mulVec]
    rw [← ambientHalfSpinorEmbed_smul]
    exact ambientReferenceZ4Action_preserves_halfSpinor winding _
  rw [hImage]
  unfold canonicalAmbientPinCHalfSpinorCoordChange
  rw [hImage, ambientHalfSpinorProject_embed]

theorem canonicalAmbientPinCHalfSpinorCoordChange_continuousOn
    (choice : NormalRootChoice)
    (first second : AmbientCover period hPeriod) :
    ContinuousOn
      (fun point : AmbientBase period hPeriod × AmbientHalfSpinor2 ↦
        canonicalAmbientPinCHalfSpinorCoordChange period hPeriod choice
          first second point.1 point.2)
      ((ambientPinMinusBundleBaseSet period hPeriod first ∩
        ambientPinMinusBundleBaseSet period hPeriod second) ×ˢ Set.univ) := by
  have hInput : Continuous
      (fun point : AmbientBase period hPeriod × AmbientHalfSpinor2 ↦
        (point.1, ambientHalfSpinorEmbed point.2)) :=
    continuous_fst.prodMk (continuous_ambientHalfSpinorEmbed.comp continuous_snd)
  have hAction :=
    (canonicalAmbientPinCSpinorCoordChange_continuousOn
      period hPeriod choice first second).comp hInput.continuousOn (by
        intro (point : AmbientBase period hPeriod × AmbientHalfSpinor2)
          (hPoint : point ∈
            ((ambientPinMinusBundleBaseSet period hPeriod first ∩
              ambientPinMinusBundleBaseSet period hPeriod second) ×ˢ Set.univ))
        exact ⟨hPoint.1, Set.mem_univ _⟩)
  unfold canonicalAmbientPinCHalfSpinorCoordChange
  exact continuous_ambientHalfSpinorProject.continuousOn.comp hAction
    (fun _ _ ↦ Set.mem_univ _)

def canonicalAmbientPinCHalfSpinorBundleCore
    (choice : NormalRootChoice) :
    FiberBundleCore (AmbientCover period hPeriod) (AmbientBase period hPeriod)
      AmbientHalfSpinor2 where
  baseSet := ambientPinMinusBundleBaseSet period hPeriod
  isOpen_baseSet := ambientPinMinusBundleBaseSet_isOpen period hPeriod
  indexAt := ambientPinMinusBundleIndexAt period hPeriod
  mem_baseSet_at := mem_ambientPinMinusBundleBaseSet_indexAt period hPeriod
  coordChange := canonicalAmbientPinCHalfSpinorCoordChange
    period hPeriod choice
  coordChange_self anchor base hBase spinor := by
    have hSelf :=
      (canonicalAmbientPinCSpinorBundleCore period hPeriod choice).coordChange_self
        anchor base hBase (ambientHalfSpinorEmbed spinor)
    change canonicalAmbientPinCSpinorCoordChange period hPeriod choice
      anchor anchor base (ambientHalfSpinorEmbed spinor) =
        ambientHalfSpinorEmbed spinor at hSelf
    unfold canonicalAmbientPinCHalfSpinorCoordChange
    rw [hSelf, ambientHalfSpinorProject_embed]
  continuousOn_coordChange :=
    canonicalAmbientPinCHalfSpinorCoordChange_continuousOn
      period hPeriod choice
  coordChange_comp first second third base hBase spinor := by
    have hFull :=
      (canonicalAmbientPinCSpinorBundleCore period hPeriod choice).coordChange_comp
        first second third base hBase (ambientHalfSpinorEmbed spinor)
    change canonicalAmbientPinCSpinorCoordChange period hPeriod choice
          second third base
          (canonicalAmbientPinCSpinorCoordChange period hPeriod choice
            first second base (ambientHalfSpinorEmbed spinor)) =
        canonicalAmbientPinCSpinorCoordChange period hPeriod choice
          first third base (ambientHalfSpinorEmbed spinor) at hFull
    have hPreserve :=
      canonicalAmbientPinCSpinorCoordChange_preserves_halfSpinor
        period hPeriod choice first second base spinor
    change canonicalAmbientPinCSpinorCoordChange period hPeriod choice
          first second base (ambientHalfSpinorEmbed spinor) =
        ambientHalfSpinorEmbed
          (ambientHalfSpinorProject
            (canonicalAmbientPinCSpinorCoordChange period hPeriod choice
              first second base (ambientHalfSpinorEmbed spinor))) at hPreserve
    unfold canonicalAmbientPinCHalfSpinorCoordChange
    rw [← hPreserve]
    exact congrArg ambientHalfSpinorProject hFull

abbrev CanonicalAmbientPinCHalfSpinorFiber
    (choice : NormalRootChoice) :=
  (canonicalAmbientPinCHalfSpinorBundleCore period hPeriod choice).Fiber

@[reducible] def canonicalAmbientPinCHalfSpinorFiber_isFiberBundle
    (choice : NormalRootChoice) :
    FiberBundle AmbientHalfSpinor2
      (CanonicalAmbientPinCHalfSpinorFiber period hPeriod choice) :=
  inferInstance

structure ProgramPAmbientHalfSpinorActualBundleCertificate4D where
  choice : NormalRootChoice
  bridge : ProgramPAmbientHalfSpinorD9BridgeCertificate4D
  core : FiberBundleCore (AmbientCover period hPeriod)
    (AmbientBase period hPeriod) AmbientHalfSpinor2
  coreCanonical : core =
    canonicalAmbientPinCHalfSpinorBundleCore period hPeriod choice
  invariantSubbundle : ∀ first second base spinor,
    canonicalAmbientPinCSpinorCoordChange period hPeriod choice
        first second base (ambientHalfSpinorEmbed spinor) =
      ambientHalfSpinorEmbed (core.coordChange first second base spinor)

def programPAmbientHalfSpinorActualBundleCertificate4D
    (choice : NormalRootChoice) :
    ProgramPAmbientHalfSpinorActualBundleCertificate4D period hPeriod where
  choice := choice
  bridge := programPAmbientHalfSpinorD9BridgeCertificate4D
  core := canonicalAmbientPinCHalfSpinorBundleCore period hPeriod choice
  coreCanonical := rfl
  invariantSubbundle :=
    canonicalAmbientPinCSpinorCoordChange_preserves_halfSpinor
      period hPeriod choice

theorem programPAmbientHalfSpinorActualBundleCertificate4D_nonempty :
    Nonempty (ProgramPAmbientHalfSpinorActualBundleCertificate4D
      period hPeriod) :=
  ⟨programPAmbientHalfSpinorActualBundleCertificate4D
    period hPeriod .positiveQuarter⟩

end
end P0EFTJanusProgramPAmbientHalfSpinorActualBundle4D
end JanusFormal
