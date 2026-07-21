import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPAmbientPinCSpinorHermitianBundle4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D

/-! # Rank-two complex half-spinor bridge to the D9 matter fiber

The reference `ZMod 4` transition preserves each two-component block of the
ambient Dirac representation.  One block has real rank four, exactly the D9
matter-coordinate rank.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D

set_option autoImplicit false
noncomputable section

open scoped Matrix
open P0EFTJanusMappingTorusSmoothGlobalFieldConfiguration4D
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusProgramPAmbientCliffordGammaRepresentation4D
open P0EFTJanusProgramPAmbientPinCSpinorRepresentation4D

abbrev AmbientHalfSpinor2 := Fin 2 → Complex
abbrev AmbientComplexMatrix2 := Matrix (Fin 2) (Fin 2) Complex

def ambientHalfGammaGenerator : AmbientComplexMatrix2 :=
  !![0, 1; -1, 0]

@[simp] theorem ambientHalfGammaGenerator_sq :
    ambientHalfGammaGenerator * ambientHalfGammaGenerator =
      -(1 : AmbientComplexMatrix2) := by
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [ambientHalfGammaGenerator, Matrix.mul_apply, Fin.sum_univ_succ]

def ambientHalfGammaGeneratorUnit : AmbientComplexMatrix2ˣ where
  val := ambientHalfGammaGenerator
  inv := -ambientHalfGammaGenerator
  val_inv := by rw [mul_neg, ambientHalfGammaGenerator_sq]; simp
  inv_val := by rw [neg_mul, ambientHalfGammaGenerator_sq]; simp

@[simp] theorem ambientHalfGammaGeneratorUnit_fourth :
    ambientHalfGammaGeneratorUnit ^ 4 = 1 := by
  apply Units.ext
  change ambientHalfGammaGenerator ^ 4 = 1
  rw [show (4 : Nat) = 2 + 2 by decide, pow_add, pow_two,
    ambientHalfGammaGenerator_sq]
  simp

private def ambientHalfGammaGeneratorIntHom :
    Int →+ Additive AmbientComplexMatrix2ˣ :=
  zmultiplesHom (Additive AmbientComplexMatrix2ˣ)
    (Additive.ofMul ambientHalfGammaGeneratorUnit)

private theorem ambientHalfGammaGeneratorIntHom_four :
    ambientHalfGammaGeneratorIntHom 4 = 0 := by
  apply Additive.toMul.injective
  simp only [ambientHalfGammaGeneratorIntHom, zmultiplesHom_apply,
    toMul_zsmul, toMul_ofMul, toMul_zero]
  rw [zpow_ofNat, ambientHalfGammaGeneratorUnit_fourth]

def ambientHalfGammaZ4AddHom :
    ZMod 4 →+ Additive AmbientComplexMatrix2ˣ :=
  ZMod.lift 4
    ⟨ambientHalfGammaGeneratorIntHom,
      ambientHalfGammaGeneratorIntHom_four⟩

def ambientHalfGammaZ4Representation :
    AddChar (ZMod 4) AmbientComplexMatrix2ˣ :=
  AddChar.toAddMonoidHomEquiv.symm ambientHalfGammaZ4AddHom

@[simp] theorem ambientHalfGammaZ4Representation_one :
    ambientHalfGammaZ4Representation 1 = ambientHalfGammaGeneratorUnit := by
  change (ambientHalfGammaZ4AddHom (1 : ZMod 4)).toMul = _
  have hOne : ambientHalfGammaZ4AddHom (1 : ZMod 4) =
      ambientHalfGammaGeneratorIntHom 1 := by
    exact ZMod.lift_coe 4
      ⟨ambientHalfGammaGeneratorIntHom,
        ambientHalfGammaGeneratorIntHom_four⟩ 1
  rw [hOne]
  simp [ambientHalfGammaGeneratorIntHom]

@[simp] theorem ambientHalfGammaZ4Representation_two :
    ambientHalfGammaZ4Representation 2 =
      ambientHalfGammaGeneratorUnit * ambientHalfGammaGeneratorUnit := by
  calc
    ambientHalfGammaZ4Representation 2 =
        ambientHalfGammaZ4Representation (1 + 1) := by
      congr 1
    _ = ambientHalfGammaZ4Representation 1 *
        ambientHalfGammaZ4Representation 1 :=
      ambientHalfGammaZ4Representation.map_add_eq_mul 1 1
    _ = _ := by rw [ambientHalfGammaZ4Representation_one]

@[simp] theorem ambientHalfGammaZ4Representation_three :
    ambientHalfGammaZ4Representation 3 =
      (ambientHalfGammaGeneratorUnit * ambientHalfGammaGeneratorUnit) *
        ambientHalfGammaGeneratorUnit := by
  calc
    ambientHalfGammaZ4Representation 3 =
        ambientHalfGammaZ4Representation (2 + 1) := by
      congr 1
    _ = ambientHalfGammaZ4Representation 2 *
        ambientHalfGammaZ4Representation 1 :=
      ambientHalfGammaZ4Representation.map_add_eq_mul 2 1
    _ = _ := by rw [ambientHalfGammaZ4Representation_two,
      ambientHalfGammaZ4Representation_one]

def ambientHalfSpinorEmbed (spinor : AmbientHalfSpinor2) :
    AmbientDiracSpinor4 :=
  fun index ↦ if index.val = 0 then spinor 0
    else if index.val = 1 then spinor 1 else 0

theorem ambientReferenceZ4Action_preserves_halfSpinor
    (winding : ZMod 4) (spinor : AmbientHalfSpinor2) :
    (ambientPinMinusGammaRepresentation
          (ambientPinMinusReferenceZ4Character winding) :
        AmbientComplexMatrix4) *ᵥ ambientHalfSpinorEmbed spinor =
      ambientHalfSpinorEmbed
        ((ambientHalfGammaZ4Representation winding :
            AmbientComplexMatrix2) *ᵥ spinor) := by
  rw [← ZMod.natCast_zmod_val winding]
  have hBound : winding.val < 4 := winding.val_lt
  interval_cases hValue : winding.val <;>
    ext index <;> fin_cases index <;>
    simp [ambientHalfSpinorEmbed,
      ambientHalfGammaGeneratorUnit, ambientHalfGammaGenerator,
      ambientHalfGammaZ4Representation_one,
      ambientHalfGammaZ4Representation_two,
      ambientHalfGammaZ4Representation_three,
      ambientPinMinusGammaRepresentation_coe,
      ambientPinMinusReferenceZ4Character_one,
      ambientPinMinusReferenceZ4Character_two,
      ambientPinMinusReferenceZ4Character_three,
      ambientPinMinusReferenceGenerator_coe,
      ambientPinMinusCentralSign_coe,
      ambientCliffordGammaRepresentation_iota,
      ambientGammaMatrix, ambientGammaBasis,
      ambientPinMinusReferenceVector, Matrix.mulVec, dotProduct,
      Matrix.one_apply, Fin.sum_univ_succ]

def realFourComplexTwoLinearEquiv :
    (Fin 4 → Real) ≃ₗ[Real] AmbientHalfSpinor2 where
  toFun coordinate index :=
    if index = 0 then ⟨coordinate 0, coordinate 1⟩
    else ⟨coordinate 2, coordinate 3⟩
  invFun spinor index :=
    Fin.cases (spinor 0).re
      (fun tail ↦ Fin.cases (spinor 0).im
        (fun tail' ↦ Fin.cases (spinor 1).re
          (fun _ ↦ (spinor 1).im) tail') tail) index
  left_inv coordinate := by
    funext index
    fin_cases index <;> rfl
  right_inv spinor := by
    funext index
    fin_cases index <;> simp <;> exact Complex.eta _
  map_add' first second := by
    funext index
    fin_cases index <;> apply Complex.ext <;> simp
  map_smul' scalar coordinate := by
    funext index
    fin_cases index <;> apply Complex.ext <;> simp

def matterFiberHalfSpinorLinearEquiv :
    MatterFiber ≃ₗ[Real] AmbientHalfSpinor2 :=
  (EuclideanSpace.equiv (Fin 4) Real).toLinearEquiv.trans
    realFourComplexTwoLinearEquiv

structure ProgramPAmbientHalfSpinorD9BridgeCertificate4D where
  halfSpinor : Type
  halfSpinor_eq : halfSpinor = AmbientHalfSpinor2
  representation : AddChar (ZMod 4) AmbientComplexMatrix2ˣ
  representationCanonical : representation = ambientHalfGammaZ4Representation
  matterIdentification : MatterFiber ≃ₗ[Real] AmbientHalfSpinor2
  matterIdentificationCanonical :
    matterIdentification = matterFiberHalfSpinorLinearEquiv
  ambientCompatibility : ∀ winding spinor,
    (ambientPinMinusGammaRepresentation
          (ambientPinMinusReferenceZ4Character winding) :
        AmbientComplexMatrix4) *ᵥ ambientHalfSpinorEmbed spinor =
      ambientHalfSpinorEmbed
        ((representation winding : AmbientComplexMatrix2) *ᵥ spinor)

def programPAmbientHalfSpinorD9BridgeCertificate4D :
    ProgramPAmbientHalfSpinorD9BridgeCertificate4D where
  halfSpinor := AmbientHalfSpinor2
  halfSpinor_eq := rfl
  representation := ambientHalfGammaZ4Representation
  representationCanonical := rfl
  matterIdentification := matterFiberHalfSpinorLinearEquiv
  matterIdentificationCanonical := rfl
  ambientCompatibility := ambientReferenceZ4Action_preserves_halfSpinor

theorem programPAmbientHalfSpinorD9BridgeCertificate4D_nonempty :
    Nonempty ProgramPAmbientHalfSpinorD9BridgeCertificate4D :=
  ⟨programPAmbientHalfSpinorD9BridgeCertificate4D⟩

end
end P0EFTJanusProgramPAmbientHalfSpinorD9Bridge4D
end JanusFormal
