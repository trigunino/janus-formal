namespace JanusFormal
namespace P0EFTJanusZ2SigmaCartanGHYDeltaKInputWriterGate

set_option autoImplicit false

structure CartanGHYDeltaKInputWriterGate where
  extrinsicCurvatureGridDeclared : Prop
  extrinsicCurvatureGridValid : Prop
  activeCoreZ2Sigma : Prop
  activeDerivedSource : Prop
  aGridDeclared : Prop
  plusMinusKsDeclared : Prop
  plusMinusKtauDeclared : Prop
  z2OrientationSignDeclared : Prop
  deltaKJumpComputed : Prop
  provenanceChecked : Prop
  compressedPlanckLCDMForbidden : Prop
  archivedZ4ReuseForbidden : Prop
  phenomenologicalHolstBAOScanForbidden : Prop
  deltaKInputWritten : Prop

def canWriteCartanDeltaKInputs
    (g : CartanGHYDeltaKInputWriterGate) : Prop :=
  g.extrinsicCurvatureGridDeclared /\
  g.extrinsicCurvatureGridValid /\
  g.activeCoreZ2Sigma /\
  g.activeDerivedSource /\
  g.aGridDeclared /\
  g.plusMinusKsDeclared /\
  g.plusMinusKtauDeclared /\
  g.z2OrientationSignDeclared /\
  g.deltaKJumpComputed /\
  g.provenanceChecked /\
  g.compressedPlanckLCDMForbidden /\
  g.archivedZ4ReuseForbidden /\
  g.phenomenologicalHolstBAOScanForbidden

theorem invalid_grid_blocks_deltaK_write
    (g : CartanGHYDeltaKInputWriterGate)
    (hInvalid : Not g.extrinsicCurvatureGridValid) :
    Not (canWriteCartanDeltaKInputs g) := by
  intro h
  exact hInvalid h.2.1

theorem deltaK_write_requires_jump_and_orientation
    (g : CartanGHYDeltaKInputWriterGate)
    (h : canWriteCartanDeltaKInputs g) :
    g.z2OrientationSignDeclared /\ g.deltaKJumpComputed := by
  rcases h with ⟨_, _, _, _, _, _, _, hOrient, hJump, _, _, _, _⟩
  exact ⟨hOrient, hJump⟩

end P0EFTJanusZ2SigmaCartanGHYDeltaKInputWriterGate
end JanusFormal
