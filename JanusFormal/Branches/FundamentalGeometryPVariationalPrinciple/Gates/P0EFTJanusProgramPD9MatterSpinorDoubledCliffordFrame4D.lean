import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPD9MatterSpinorCliffordActionNoGo4D

/-! # Doubled D9 matter-spinor Clifford frame -/

namespace JanusFormal
namespace P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D

set_option autoImplicit false
noncomputable section

open scoped Matrix
open P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D

abbrev D9DoubledMatterSpinor := AmbientHalfSpinor2 × AmbientHalfSpinor2

private def halfJ : AmbientHalfSpinor2 →ₗ[Complex] AmbientHalfSpinor2 where
  toFun spinor := ![spinor 1, -spinor 0]
  map_add' first second := by
    funext index
    fin_cases index <;> simp [add_comm]
  map_smul' scalar spinor := by
    funext index
    fin_cases index <;> simp

private def halfK : AmbientHalfSpinor2 →ₗ[Complex] AmbientHalfSpinor2 where
  toFun spinor := ![spinor 1, spinor 0]
  map_add' first second := by
    funext index
    fin_cases index <;> simp
  map_smul' scalar spinor := by
    funext index
    fin_cases index <;> simp

private def halfL : AmbientHalfSpinor2 →ₗ[Complex] AmbientHalfSpinor2 where
  toFun spinor := ![spinor 0, -spinor 1]
  map_add' first second := by
    funext index
    fin_cases index <;> simp [add_comm]
  map_smul' scalar spinor := by
    funext index
    fin_cases index <;> simp

@[simp] theorem halfJ_eq_ambientHalfGammaGenerator_mulVec
    (spinor : AmbientHalfSpinor2) :
    halfJ spinor = ambientHalfGammaGenerator *ᵥ spinor := by
  funext index
  fin_cases index <;>
    simp [halfJ, ambientHalfGammaGenerator, Matrix.mulVec,
      dotProduct, Fin.sum_univ_succ]

/-- Normalized one-loop transition: the original `J` block and its opposite. -/
def d9DoubledMatterSpinorDeckGenerator :
    D9DoubledMatterSpinor →ₗ[Complex] D9DoubledMatterSpinor where
  toFun spinor := (halfJ spinor.1, -halfJ spinor.2)
  map_add' first second := by
    ext index <;> fin_cases index <;> simp [halfJ, add_comm]
  map_smul' scalar spinor := by
    ext index <;> fin_cases index <;> simp [halfJ]

private def d9DoubledGammaZero :
    D9DoubledMatterSpinor →ₗ[Complex] D9DoubledMatterSpinor where
  toFun spinor := (halfJ spinor.1, halfJ spinor.2)
  map_add' first second := by
    ext index <;> fin_cases index <;> simp [halfJ, add_comm]
  map_smul' scalar spinor := by
    ext index <;> fin_cases index <;> simp [halfJ]

private def d9DoubledGammaOne :
    D9DoubledMatterSpinor →ₗ[Complex] D9DoubledMatterSpinor where
  toFun spinor := (halfK spinor.2, -halfK spinor.1)
  map_add' first second := by
    ext index <;> fin_cases index <;> simp [halfK, add_comm]
  map_smul' scalar spinor := by
    ext index <;> fin_cases index <;> simp [halfK]

private def d9DoubledGammaTwo :
    D9DoubledMatterSpinor →ₗ[Complex] D9DoubledMatterSpinor where
  toFun spinor := (halfL spinor.2, -halfL spinor.1)
  map_add' first second := by
    ext index <;> fin_cases index <;> simp [halfL, add_comm]
  map_smul' scalar spinor := by
    ext index <;> fin_cases index <;> simp [halfL]

def d9DoubledMatterSpinorCliffordGamma
    (direction : Fin 3) :
    D9DoubledMatterSpinor →ₗ[Complex] D9DoubledMatterSpinor :=
  ![d9DoubledGammaZero, d9DoubledGammaOne, d9DoubledGammaTwo] direction

theorem d9DoubledMatterSpinorCliffordGamma_sq
    (direction : Fin 3) (spinor : D9DoubledMatterSpinor) :
    d9DoubledMatterSpinorCliffordGamma direction
        (d9DoubledMatterSpinorCliffordGamma direction spinor) = -spinor := by
  fin_cases direction <;>
    apply Prod.ext <;> funext index <;> fin_cases index <;>
    simp [d9DoubledMatterSpinorCliffordGamma, d9DoubledGammaZero,
      d9DoubledGammaOne, d9DoubledGammaTwo, halfJ, halfK, halfL]

theorem d9DoubledMatterSpinorCliffordGamma_anticommute
    (first second : Fin 3) (hDistinct : first ≠ second)
    (spinor : D9DoubledMatterSpinor) :
    d9DoubledMatterSpinorCliffordGamma first
        (d9DoubledMatterSpinorCliffordGamma second spinor) =
      -d9DoubledMatterSpinorCliffordGamma second
        (d9DoubledMatterSpinorCliffordGamma first spinor) := by
  fin_cases first <;> fin_cases second <;> try { exact (hDistinct rfl).elim }
  all_goals
    apply Prod.ext <;> funext index <;> fin_cases index <;>
      simp [d9DoubledMatterSpinorCliffordGamma, d9DoubledGammaZero,
        d9DoubledGammaOne, d9DoubledGammaTwo, halfJ, halfK, halfL]

theorem d9DoubledMatterSpinorCliffordGamma_deck_compatible
    (direction : Fin 3) (spinor : D9DoubledMatterSpinor) :
    d9DoubledMatterSpinorDeckGenerator
        (d9DoubledMatterSpinorCliffordGamma direction spinor) =
      d9DoubledMatterSpinorCliffordGamma direction
        (d9DoubledMatterSpinorDeckGenerator spinor) := by
  fin_cases direction <;>
    apply Prod.ext <;> funext index <;> fin_cases index <;>
    simp [d9DoubledMatterSpinorDeckGenerator,
      d9DoubledMatterSpinorCliffordGamma, d9DoubledGammaZero,
      d9DoubledGammaOne, d9DoubledGammaTwo, halfJ, halfK, halfL]

structure ProgramPD9MatterSpinorDoubledCliffordFrameCertificate4D where
  spinor : Type
  spinor_eq : spinor = D9DoubledMatterSpinor
  deckGenerator : D9DoubledMatterSpinor →ₗ[Complex] D9DoubledMatterSpinor
  gamma : Fin 3 → D9DoubledMatterSpinor →ₗ[Complex] D9DoubledMatterSpinor
  square : ∀ direction spinor, gamma direction (gamma direction spinor) = -spinor
  anticommute : ∀ first second, first ≠ second → ∀ spinor,
    gamma first (gamma second spinor) = -gamma second (gamma first spinor)
  deckCompatible : ∀ direction spinor,
    deckGenerator (gamma direction spinor) =
      gamma direction (deckGenerator spinor)

def programPD9MatterSpinorDoubledCliffordFrameCertificate4D :
    ProgramPD9MatterSpinorDoubledCliffordFrameCertificate4D where
  spinor := D9DoubledMatterSpinor
  spinor_eq := rfl
  deckGenerator := d9DoubledMatterSpinorDeckGenerator
  gamma := d9DoubledMatterSpinorCliffordGamma
  square := d9DoubledMatterSpinorCliffordGamma_sq
  anticommute := d9DoubledMatterSpinorCliffordGamma_anticommute
  deckCompatible := d9DoubledMatterSpinorCliffordGamma_deck_compatible

theorem programPD9MatterSpinorDoubledCliffordFrameCertificate4D_nonempty :
    Nonempty ProgramPD9MatterSpinorDoubledCliffordFrameCertificate4D :=
  ⟨programPD9MatterSpinorDoubledCliffordFrameCertificate4D⟩

end
end P0EFTJanusProgramPD9MatterSpinorDoubledCliffordFrame4D
end JanusFormal
