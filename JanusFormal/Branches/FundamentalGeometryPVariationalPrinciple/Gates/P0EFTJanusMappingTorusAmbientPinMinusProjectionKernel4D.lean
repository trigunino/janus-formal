import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusTopologicalGroup4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusAmbientPinMinusOrthogonalProjection4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPAmbientCliffordGammaRepresentation4D

/-!
# Exact algebraic input for the ambient Pin-minus projection kernel

The sixteen ordered Clifford blades are sent to sixteen explicitly linearly
independent complex gamma matrices.  Consequently the concrete gamma
representation of the ambient real Clifford algebra is faithful.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientPinMinusProjectionKernel4D

set_option autoImplicit false
noncomputable section

open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientPinMinusProjection4D
open P0EFTJanusMappingTorusAmbientPinMinusTopologicalGroup4D
open P0EFTJanusMappingTorusAmbientPinMinusOrthogonalProjection4D
open P0EFTJanusProgramPAmbientCliffordGammaRepresentation4D
open Module

/-- The coordinate vectors used by the concrete gamma representation. -/
def ambientPinMinusCoordinateVector : Fin 4 → CoverCoordinates :=
  ![
    (EuclideanSpace.single 0 (1 : Real), 0),
    (EuclideanSpace.single 1 (1 : Real), 0),
    (EuclideanSpace.single 2 (1 : Real), 0),
    (0, (1 : Real))
  ]

/-- The four coordinate generators in the real Clifford algebra. -/
def ambientPinMinusCliffordGenerator
    (index : Fin 4) : AmbientPinMinusCliffordAlgebra :=
  CliffordAlgebra.ι ambientCoverPinMinusQuadraticForm
    (ambientPinMinusCoordinateVector index)

/-- The sixteen ordered real Clifford blades. -/
def ambientPinMinusCliffordBlade :
    Fin 16 → AmbientPinMinusCliffordAlgebra :=
  ![
    1,
    ambientPinMinusCliffordGenerator 0,
    ambientPinMinusCliffordGenerator 1,
    ambientPinMinusCliffordGenerator 2,
    ambientPinMinusCliffordGenerator 3,
    ambientPinMinusCliffordGenerator 0 *
      ambientPinMinusCliffordGenerator 1,
    ambientPinMinusCliffordGenerator 0 *
      ambientPinMinusCliffordGenerator 2,
    ambientPinMinusCliffordGenerator 0 *
      ambientPinMinusCliffordGenerator 3,
    ambientPinMinusCliffordGenerator 1 *
      ambientPinMinusCliffordGenerator 2,
    ambientPinMinusCliffordGenerator 1 *
      ambientPinMinusCliffordGenerator 3,
    ambientPinMinusCliffordGenerator 2 *
      ambientPinMinusCliffordGenerator 3,
    ambientPinMinusCliffordGenerator 0 *
      ambientPinMinusCliffordGenerator 1 *
      ambientPinMinusCliffordGenerator 2,
    ambientPinMinusCliffordGenerator 0 *
      ambientPinMinusCliffordGenerator 1 *
      ambientPinMinusCliffordGenerator 3,
    ambientPinMinusCliffordGenerator 0 *
      ambientPinMinusCliffordGenerator 2 *
      ambientPinMinusCliffordGenerator 3,
    ambientPinMinusCliffordGenerator 1 *
      ambientPinMinusCliffordGenerator 2 *
      ambientPinMinusCliffordGenerator 3,
    ambientPinMinusCliffordGenerator 0 *
      ambientPinMinusCliffordGenerator 1 *
      ambientPinMinusCliffordGenerator 2 *
      ambientPinMinusCliffordGenerator 3
  ]

/-- Images of the sixteen ordered Clifford blades. -/
def ambientPinMinusGammaBlade : Fin 16 → AmbientComplexMatrix4 :=
  ![
    1,
    ambientGammaBasis 0,
    ambientGammaBasis 1,
    ambientGammaBasis 2,
    ambientGammaBasis 3,
    ambientGammaBasis 0 * ambientGammaBasis 1,
    ambientGammaBasis 0 * ambientGammaBasis 2,
    ambientGammaBasis 0 * ambientGammaBasis 3,
    ambientGammaBasis 1 * ambientGammaBasis 2,
    ambientGammaBasis 1 * ambientGammaBasis 3,
    ambientGammaBasis 2 * ambientGammaBasis 3,
    ambientGammaBasis 0 * ambientGammaBasis 1 * ambientGammaBasis 2,
    ambientGammaBasis 0 * ambientGammaBasis 1 * ambientGammaBasis 3,
    ambientGammaBasis 0 * ambientGammaBasis 2 * ambientGammaBasis 3,
    ambientGammaBasis 1 * ambientGammaBasis 2 * ambientGammaBasis 3,
    ambientGammaBasis 0 * ambientGammaBasis 1 * ambientGammaBasis 2 *
      ambientGammaBasis 3
  ]

@[simp] theorem ambientGammaMatrix_coordinateVector
    (index : Fin 4) :
    ambientGammaMatrix (ambientPinMinusCoordinateVector index) =
      ambientGammaBasis index := by
  fin_cases index <;>
    ext row column <;>
    fin_cases row <;> fin_cases column <;>
    simp [ambientGammaMatrix, ambientPinMinusCoordinateVector]

@[simp] theorem ambientCliffordGammaRepresentation_blade
    (index : Fin 16) :
    ambientCliffordGammaRepresentation
        (ambientPinMinusCliffordBlade index) =
      ambientPinMinusGammaBlade index := by
  fin_cases index <;>
    simp [ambientPinMinusCliffordBlade, ambientPinMinusGammaBlade,
      ambientPinMinusCliffordGenerator]

/-- The sixteen concrete gamma blades are real-linearly independent. -/
theorem ambientPinMinusGammaBlade_linearIndependent :
    LinearIndependent Real ambientPinMinusGammaBlade := by
  rw [Fintype.linearIndependent_iff]
  intro coefficient hSum index
  have hEntry (row column : Fin 4) :
      ∑ blade : Fin 16,
          (coefficient blade : Complex) *
            ambientPinMinusGammaBlade blade row column = 0 := by
    have hAt := congrFun (congrFun hSum row) column
    simpa only [Matrix.sum_apply, Matrix.smul_apply, Complex.real_smul,
      Matrix.zero_apply] using hAt
  have h00Real := congrArg Complex.re (hEntry 0 0)
  have h00Imag := congrArg Complex.im (hEntry 0 0)
  have h01Real := congrArg Complex.re (hEntry 0 1)
  have h01Imag := congrArg Complex.im (hEntry 0 1)
  have h02Real := congrArg Complex.re (hEntry 0 2)
  have h02Imag := congrArg Complex.im (hEntry 0 2)
  have h03Real := congrArg Complex.re (hEntry 0 3)
  have h03Imag := congrArg Complex.im (hEntry 0 3)
  have h10Real := congrArg Complex.re (hEntry 1 0)
  have h10Imag := congrArg Complex.im (hEntry 1 0)
  have h11Real := congrArg Complex.re (hEntry 1 1)
  have h11Imag := congrArg Complex.im (hEntry 1 1)
  have h12Real := congrArg Complex.re (hEntry 1 2)
  have h12Imag := congrArg Complex.im (hEntry 1 2)
  have h13Real := congrArg Complex.re (hEntry 1 3)
  have h13Imag := congrArg Complex.im (hEntry 1 3)
  simp [ambientPinMinusGammaBlade, ambientGammaBasis,
    Fin.sum_univ_succ, Complex.I_mul_I] at h00Real h00Imag h01Real h01Imag h02Real h02Imag h03Real h03Imag
  simp [ambientPinMinusGammaBlade, ambientGammaBasis,
    Fin.sum_univ_succ, Complex.I_mul_I] at h10Real h10Imag h11Real h11Imag h12Real h12Imag h13Real h13Imag
  have hc0 : coefficient 0 = 0 := by linarith [h00Real, h11Real]
  have hc1 : coefficient 1 = 0 := by linarith [h02Imag, h13Imag]
  have hc2 : coefficient 2 = 0 := by linarith [h02Real, h13Real]
  have hc3 : coefficient 3 = 0 := by linarith [h01Imag, h10Imag]
  have hc4 : coefficient 4 = 0 := by linarith [h01Real, h10Real]
  have hc5 : coefficient 5 = 0 := by linarith [h00Imag, h11Imag]
  have hc6 : coefficient 6 = 0 := by linarith [h03Real, h12Real]
  have hc7 : coefficient 7 = 0 := by linarith [h03Imag, h12Imag]
  have hc8 : coefficient 8 = 0 := by linarith [h03Imag, h12Imag]
  have hc9 : coefficient 9 = 0 := by linarith [h03Real, h12Real]
  have hc10 : coefficient 10 = 0 := by linarith [h00Imag, h11Imag]
  have hc11 : coefficient 11 = 0 := by linarith [h01Real, h10Real]
  have hc12 : coefficient 12 = 0 := by linarith [h01Imag, h10Imag]
  have hc13 : coefficient 13 = 0 := by linarith [h02Real, h13Real]
  have hc14 : coefficient 14 = 0 := by linarith [h02Imag, h13Imag]
  have hc15 : coefficient 15 = 0 := by linarith [h00Real, h11Real]
  fin_cases index <;> simp_all

/-- The sixteen concrete real Clifford blades are linearly independent. -/
theorem ambientPinMinusCliffordBlade_linearIndependent :
    LinearIndependent Real ambientPinMinusCliffordBlade := by
  apply LinearIndependent.of_comp
    ambientCliffordGammaRepresentation.toLinearMap
  simpa [Function.comp_def] using
    ambientPinMinusGammaBlade_linearIndependent

private theorem ambientPinMinusClifford_finrank :
    Module.finrank Real AmbientPinMinusCliffordAlgebra = 16 := by
  rw [Module.finrank_eq_card_basis ambientPinMinusCliffordBasis]
  norm_num [Fintype.card_finset]

/-- The ordered blades form a basis of the real ambient Clifford algebra. -/
def ambientPinMinusCliffordBladeBasis :
    Basis (Fin 16) Real AmbientPinMinusCliffordAlgebra :=
  basisOfLinearIndependentOfCardEqFinrank
    ambientPinMinusCliffordBlade_linearIndependent (by
      simp [ambientPinMinusClifford_finrank])

@[simp] theorem ambientPinMinusCliffordBladeBasis_apply
    (index : Fin 16) :
    ambientPinMinusCliffordBladeBasis index =
      ambientPinMinusCliffordBlade index := by
  simp [ambientPinMinusCliffordBladeBasis]

/-- The explicit complex gamma representation is faithful over the reals. -/
theorem ambientCliffordGammaRepresentation_injective :
    Function.Injective ambientCliffordGammaRepresentation := by
  change Function.Injective ambientCliffordGammaRepresentation.toLinearMap
  apply LinearMap.injective_of_linearIndependent
    (f := ambientCliffordGammaRepresentation.toLinearMap)
    (v := ambientPinMinusCliffordBlade)
  · have hBlade :
        ambientPinMinusCliffordBlade =
          ambientPinMinusCliffordBladeBasis := by
      funext index
      exact (ambientPinMinusCliffordBladeBasis_apply index).symm
    rw [hBlade]
    exact ambientPinMinusCliffordBladeBasis.span_eq
  · simpa [Function.comp_def] using
      ambientPinMinusGammaBlade_linearIndependent

/-- A complex matrix commuting with all four gamma generators is scalar. -/
theorem ambientGammaBasis_commutant_eq_scalar
    (value : AmbientComplexMatrix4)
    (hCommute : ∀ index,
      value * ambientGammaBasis index =
        ambientGammaBasis index * value) :
    value = value 0 0 • (1 : AmbientComplexMatrix4) := by
  have hEntry (index row column : Fin 4) :
      (value * ambientGammaBasis index) row column =
        (ambientGammaBasis index * value) row column :=
    congrFun (congrFun (hCommute index) row) column
  have h0_00 := hEntry 0 0 0
  have h0_01 := hEntry 0 0 1
  have h0_10 := hEntry 0 1 0
  have h0_11 := hEntry 0 1 1
  have h0_02 := hEntry 0 0 2
  have h0_03 := hEntry 0 0 3
  have h0_12 := hEntry 0 1 2
  have h0_13 := hEntry 0 1 3
  have h1_00 := hEntry 1 0 0
  have h1_01 := hEntry 1 0 1
  have h1_10 := hEntry 1 1 0
  have h1_11 := hEntry 1 1 1
  have h2_00 := hEntry 2 0 0
  have h2_01 := hEntry 2 0 1
  have h3_00 := hEntry 3 0 0
  simp [ambientGammaBasis, Matrix.mul_apply, Fin.sum_univ_succ] at h0_00 h0_01 h0_10 h0_11 h0_02 h0_03 h0_12 h0_13
  simp [ambientGammaBasis, Matrix.mul_apply, Fin.sum_univ_succ] at h1_00 h1_01 h1_10 h1_11 h2_00 h2_01 h3_00
  have h02_20 : value 0 2 = value 2 0 := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    linear_combination h0_00
  have h02_neg : -value 0 2 = value 2 0 := by
    linear_combination h1_00
  have h02 : value 0 2 = 0 := by
    rw [← CharZero.neg_eq_self_iff]
    exact h02_neg.trans h02_20.symm
  have h20 : value 2 0 = 0 := by
    rw [← h02_20, h02]
  have h03_21 : value 0 3 = value 2 1 := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    linear_combination h0_01
  have h03_neg : -value 0 3 = value 2 1 := by
    linear_combination h1_01
  have h03 : value 0 3 = 0 := by
    rw [← CharZero.neg_eq_self_iff]
    exact h03_neg.trans h03_21.symm
  have h21 : value 2 1 = 0 := by
    rw [← h03_21, h03]
  have h12_30 : value 1 2 = value 3 0 := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    linear_combination h0_10
  have h12_neg : -value 1 2 = value 3 0 := by
    linear_combination h1_10
  have h12 : value 1 2 = 0 := by
    rw [← CharZero.neg_eq_self_iff]
    exact h12_neg.trans h12_30.symm
  have h30 : value 3 0 = 0 := by
    rw [← h12_30, h12]
  have h13_31 : value 1 3 = value 3 1 := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    linear_combination h0_11
  have h13_neg : -value 1 3 = value 3 1 := by
    linear_combination h1_11
  have h13 : value 1 3 = 0 := by
    rw [← CharZero.neg_eq_self_iff]
    exact h13_neg.trans h13_31.symm
  have h31 : value 3 1 = 0 := by
    rw [← h13_31, h13]
  have h00_22 : value 0 0 = value 2 2 := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    linear_combination h0_02
  have h01_23 : value 0 1 = value 2 3 := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    linear_combination h0_03
  have h10_32 : value 1 0 = value 3 2 := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    linear_combination h0_12
  have h11_33 : value 1 1 = value 3 3 := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    linear_combination h0_13
  have h01_10 : value 0 1 = value 1 0 := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    linear_combination h2_00
  have h01_neg : -value 0 1 = value 1 0 := by
    linear_combination h3_00
  have h01 : value 0 1 = 0 := by
    rw [← CharZero.neg_eq_self_iff]
    exact h01_neg.trans h01_10.symm
  have h10 : value 1 0 = 0 := by
    rw [← h01_10, h01]
  have h11 : value 1 1 = value 0 0 := by
    apply mul_left_cancel₀ Complex.I_ne_zero
    calc
      Complex.I * value 1 1 = value 0 0 * Complex.I := h2_01.symm
      _ = Complex.I * value 0 0 := mul_comm _ _
  have h22 : value 2 2 = value 0 0 := h00_22.symm
  have h23 : value 2 3 = 0 := by rw [← h01_23, h01]
  have h32 : value 3 2 = 0 := by rw [← h10_32, h10]
  have h33 : value 3 3 = value 0 0 := h11_33.symm.trans h11
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.smul_apply, h01, h02, h03, h10, h11, h12, h13,
      h20, h21, h22, h23, h30, h31, h32, h33]

/-- A complex scalar lying in the real gamma image is necessarily real. -/
theorem ambientCliffordGammaRepresentation_eq_complexScalar
    (value : AmbientPinMinusCliffordAlgebra) (scalar : Complex)
    (hScalar :
      ambientCliffordGammaRepresentation value =
        scalar • (1 : AmbientComplexMatrix4)) :
    ∃ realScalar : Real,
      value = algebraMap Real AmbientPinMinusCliffordAlgebra realScalar ∧
        scalar = (realScalar : Complex) := by
  let coefficient : Fin 16 → Real :=
    fun index => ambientPinMinusCliffordBladeBasis.repr value index
  have hExpansion :
      ∑ index : Fin 16,
          coefficient index • ambientPinMinusGammaBlade index =
        ambientCliffordGammaRepresentation value := by
    rw [← ambientPinMinusCliffordBladeBasis.sum_repr value]
    simp [coefficient]
  have hMatrix :
      ∑ index : Fin 16,
          coefficient index • ambientPinMinusGammaBlade index =
        scalar • (1 : AmbientComplexMatrix4) :=
    hExpansion.trans hScalar
  have hEntry (row column : Fin 4) :=
    congrFun (congrFun hMatrix row) column
  have h00Imag := congrArg Complex.im (hEntry 0 0)
  have h11Imag := congrArg Complex.im (hEntry 1 1)
  have h22Imag := congrArg Complex.im (hEntry 2 2)
  simp [coefficient, ambientPinMinusGammaBlade, ambientGammaBasis,
    Fin.sum_univ_succ, Complex.I_mul_I,
    Matrix.smul_apply] at h00Imag h11Imag h22Imag
  have hScalarImag : scalar.im = 0 := by
    linarith [h00Imag, h11Imag, h22Imag]
  have hScalarReal : scalar = (scalar.re : Complex) := by
    apply Complex.ext
    · simp
    · simpa using hScalarImag
  refine ⟨scalar.re, ?_, hScalarReal⟩
  apply ambientCliffordGammaRepresentation_injective
  rw [hScalar, hScalarReal]
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [Matrix.smul_apply, Matrix.algebraMap_matrix_apply]

/-- The commutant of the four real Clifford generators is the real center. -/
theorem ambientPinMinusClifford_commutant_eq_realScalar
    (value : AmbientPinMinusCliffordAlgebra)
    (hCommute : ∀ index,
      value * ambientPinMinusCliffordGenerator index =
        ambientPinMinusCliffordGenerator index * value) :
    ∃ scalar : Real,
      value = algebraMap Real AmbientPinMinusCliffordAlgebra scalar := by
  have hGammaCommute (index : Fin 4) :
      ambientCliffordGammaRepresentation value * ambientGammaBasis index =
        ambientGammaBasis index *
          ambientCliffordGammaRepresentation value := by
    have hMapped := congrArg ambientCliffordGammaRepresentation
      (hCommute index)
    simpa [ambientPinMinusCliffordGenerator] using hMapped
  have hScalar := ambientGammaBasis_commutant_eq_scalar
    (ambientCliffordGammaRepresentation value) hGammaCommute
  rcases ambientCliffordGammaRepresentation_eq_complexScalar value
      (ambientCliffordGammaRepresentation value 0 0) hScalar with
    ⟨scalar, hValue, -⟩
  exact ⟨scalar, hValue⟩

/-- The ordered four-generator volume element. -/
def ambientPinMinusCliffordVolume : AmbientPinMinusCliffordAlgebra :=
  ambientPinMinusCliffordGenerator 0 *
    ambientPinMinusCliffordGenerator 1 *
    ambientPinMinusCliffordGenerator 2 *
    ambientPinMinusCliffordGenerator 3

@[simp] theorem ambientPinMinusCliffordVolume_sq :
    ambientPinMinusCliffordVolume * ambientPinMinusCliffordVolume = 1 := by
  apply ambientCliffordGammaRepresentation_injective
  ext row column
  fin_cases row <;> fin_cases column <;>
    simp [ambientPinMinusCliffordVolume, ambientPinMinusCliffordGenerator,
      ambientGammaBasis, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.I_mul_I]

@[simp] theorem ambientPinMinusCliffordVolume_involute :
    CliffordAlgebra.involute ambientPinMinusCliffordVolume =
      ambientPinMinusCliffordVolume := by
  simp [ambientPinMinusCliffordVolume, ambientPinMinusCliffordGenerator]

/-- In even dimension four, the volume element anticommutes with generators. -/
theorem ambientPinMinusCliffordVolume_anticommute
    (index : Fin 4) :
    ambientPinMinusCliffordVolume *
        ambientPinMinusCliffordGenerator index =
      -(ambientPinMinusCliffordGenerator index *
        ambientPinMinusCliffordVolume) := by
  apply ambientCliffordGammaRepresentation_injective
  fin_cases index <;>
    ext row column <;>
    fin_cases row <;> fin_cases column <;>
    simp [ambientPinMinusCliffordVolume, ambientPinMinusCliffordGenerator,
      ambientGammaBasis, Matrix.mul_apply, Fin.sum_univ_succ,
      Complex.I_mul_I]

/-- The anticommutant of the generators is the real volume line. -/
theorem ambientPinMinusClifford_anticommutant_eq_volumeScalar
    (value : AmbientPinMinusCliffordAlgebra)
    (hAnticommute : ∀ index,
      value * ambientPinMinusCliffordGenerator index =
        -(ambientPinMinusCliffordGenerator index * value)) :
    ∃ scalar : Real,
      value =
        algebraMap Real AmbientPinMinusCliffordAlgebra scalar *
          ambientPinMinusCliffordVolume := by
  have hCommute (index : Fin 4) :
      (value * ambientPinMinusCliffordVolume) *
          ambientPinMinusCliffordGenerator index =
        ambientPinMinusCliffordGenerator index *
          (value * ambientPinMinusCliffordVolume) := by
    calc
      _ = value * (ambientPinMinusCliffordVolume *
          ambientPinMinusCliffordGenerator index) := by
            rw [mul_assoc]
      _ = value * (-(ambientPinMinusCliffordGenerator index *
          ambientPinMinusCliffordVolume)) := by
            rw [ambientPinMinusCliffordVolume_anticommute]
      _ = -(value * ambientPinMinusCliffordGenerator index) *
          ambientPinMinusCliffordVolume := by noncomm_ring
      _ = -(-(ambientPinMinusCliffordGenerator index * value)) *
          ambientPinMinusCliffordVolume := by
            rw [hAnticommute]
      _ = _ := by noncomm_ring
  rcases ambientPinMinusClifford_commutant_eq_realScalar
      (value * ambientPinMinusCliffordVolume) hCommute with
    ⟨scalar, hScalar⟩
  refine ⟨scalar, ?_⟩
  calc
    value = value * 1 := by rw [mul_one]
    _ = value *
        (ambientPinMinusCliffordVolume *
          ambientPinMinusCliffordVolume) := by
            rw [ambientPinMinusCliffordVolume_sq]
    _ = (value * ambientPinMinusCliffordVolume) *
        ambientPinMinusCliffordVolume := by rw [mul_assoc]
    _ = _ := by rw [hScalar]

/-- A projection-kernel element either commutes or anticommutes with vectors,
according to its genuine Clifford parity. -/
theorem ambientPinMinusProjection_kernel_parity
    (lift : AmbientCoordinatePinMinusGroup)
    (hKernel : ambientPinMinusProjection lift = 1) :
    (CliffordAlgebra.involute
          (lift : AmbientPinMinusCliffordAlgebra) = lift ∧
        ∀ index,
          (lift : AmbientPinMinusCliffordAlgebra) *
              ambientPinMinusCliffordGenerator index =
            ambientPinMinusCliffordGenerator index * lift) ∨
      (CliffordAlgebra.involute
          (lift : AmbientPinMinusCliffordAlgebra) = -lift ∧
        ∀ index,
          (lift : AmbientPinMinusCliffordAlgebra) *
              ambientPinMinusCliffordGenerator index =
            -(ambientPinMinusCliffordGenerator index * lift)) := by
  have hAction (index : Fin 4) :
      ambientPinMinusVectorAction lift
          (ambientPinMinusCoordinateVector index) =
        ambientPinMinusCoordinateVector index := by
    have hAt := congrArg
      (fun action : CoverCoordinates ≃ₗ[Real] CoverCoordinates =>
        action (ambientPinMinusCoordinateVector index)) hKernel
    simpa [ambientPinMinusProjection_apply] using hAt
  have hTwisted (index : Fin 4) :
      CliffordAlgebra.involute
            (lift : AmbientPinMinusCliffordAlgebra) *
          ambientPinMinusCliffordGenerator index *
          (↑(lift⁻¹) : AmbientPinMinusCliffordAlgebra) =
        ambientPinMinusCliffordGenerator index := by
    simpa [ambientPinMinusCliffordGenerator, hAction] using
      (ambientPinMinusVectorAction_spec lift
        (ambientPinMinusCoordinateVector index)).symm
  have hInverseMul :
      (↑(lift⁻¹) : AmbientPinMinusCliffordAlgebra) *
          (lift : AmbientPinMinusCliffordAlgebra) = 1 := by
    change star (lift : AmbientPinMinusCliffordAlgebra) *
      (lift : AmbientPinMinusCliffordAlgebra) = 1
    exact pinGroup.coe_star_mul_self lift
  rcases ambientPinMinus_involute_parity lift with hEven | hOdd
  · left
    refine ⟨hEven, fun index => ?_⟩
    have hTwistedEven := hTwisted index
    rw [hEven] at hTwistedEven
    calc
      (lift : AmbientPinMinusCliffordAlgebra) *
          ambientPinMinusCliffordGenerator index =
        (((lift : AmbientPinMinusCliffordAlgebra) *
            ambientPinMinusCliffordGenerator index) *
            (↑(lift⁻¹) : AmbientPinMinusCliffordAlgebra)) * lift := by
              rw [mul_assoc, hInverseMul, mul_one]
      _ = ambientPinMinusCliffordGenerator index * lift := by
        rw [hTwistedEven]
  · right
    refine ⟨hOdd, fun index => ?_⟩
    have hTwistedOdd := hTwisted index
    rw [hOdd] at hTwistedOdd
    have hNeg :
        -((lift : AmbientPinMinusCliffordAlgebra) *
            ambientPinMinusCliffordGenerator index) =
          ambientPinMinusCliffordGenerator index * lift := by
      have hRight := congrArg
        (fun value : AmbientPinMinusCliffordAlgebra =>
          value * (lift : AmbientPinMinusCliffordAlgebra)) hTwistedOdd
      simpa [mul_assoc, hInverseMul] using hRight
    simpa only [neg_neg] using congrArg Neg.neg hNeg

/-- Exact kernel of the concrete ambient Pin-minus vector projection. -/
theorem ambientPinMinusProjection_eq_one_iff
    (lift : AmbientCoordinatePinMinusGroup) :
    ambientPinMinusProjection lift = 1 ↔
      lift = 1 ∨ lift = ambientPinMinusCentralSign := by
  constructor
  · intro hKernel
    rcases ambientPinMinusProjection_kernel_parity lift hKernel with
      ⟨hEven, hCommute⟩ | ⟨hOdd, hAnticommute⟩
    · rcases ambientPinMinusClifford_commutant_eq_realScalar
          (lift : AmbientPinMinusCliffordAlgebra) hCommute with
        ⟨scalar, hScalar⟩
      have hNorm := pinGroup.coe_star_mul_self lift
      rw [hScalar] at hNorm
      have hScalarSquare :
          scalar * scalar = 1 := by
        apply (algebraMap Real AmbientPinMinusCliffordAlgebra).injective
        simpa using hNorm
      rcases mul_self_eq_one_iff.mp hScalarSquare with
        hScalarOne | hScalarNegOne
      · left
        apply Subtype.ext
        change (lift : AmbientPinMinusCliffordAlgebra) = 1
        rw [hScalar, hScalarOne]
        simp
      · right
        apply Subtype.ext
        rw [hScalar, hScalarNegOne, ambientPinMinusCentralSign_coe]
        simp
    · rcases ambientPinMinusClifford_anticommutant_eq_volumeScalar
          (lift : AmbientPinMinusCliffordAlgebra) hAnticommute with
        ⟨scalar, hVolume⟩
      have hNegSelf :
          -(lift : AmbientPinMinusCliffordAlgebra) =
            (lift : AmbientPinMinusCliffordAlgebra) := by
        calc
          -(lift : AmbientPinMinusCliffordAlgebra) =
              CliffordAlgebra.involute
                (lift : AmbientPinMinusCliffordAlgebra) := hOdd.symm
          _ = CliffordAlgebra.involute
              (algebraMap Real AmbientPinMinusCliffordAlgebra scalar *
                ambientPinMinusCliffordVolume) := by rw [hVolume]
          _ = algebraMap Real AmbientPinMinusCliffordAlgebra scalar *
              ambientPinMinusCliffordVolume := by simp
          _ = (lift : AmbientPinMinusCliffordAlgebra) := hVolume.symm
      have hZero :
          (lift : AmbientPinMinusCliffordAlgebra) = 0 := by
        apply ambientCliffordGammaRepresentation_injective
        have hMapped := congrArg ambientCliffordGammaRepresentation hNegSelf
        simp only [map_neg] at hMapped
        ext row column
        have hEntry := congrFun (congrFun hMapped row) column
        simpa only [map_zero, Matrix.zero_apply] using
          (CharZero.neg_eq_self_iff.mp hEntry)
      have hNorm := pinGroup.coe_star_mul_self lift
      rw [hZero] at hNorm
      simp at hNorm
  · rintro (rfl | rfl)
    · simp
    · exact ambientPinMinusProjection_centralSign

/-- The exact two-point kernel is finite. -/
theorem ambientPinMinusProjection_kernel_finite :
    Set.Finite
      {lift : AmbientCoordinatePinMinusGroup |
        ambientPinMinusProjection lift = 1} := by
  have hKernel :
      {lift : AmbientCoordinatePinMinusGroup |
          ambientPinMinusProjection lift = 1} =
        {1, ambientPinMinusCentralSign} := by
    ext lift
    simpa [ambientPinMinusProjection_eq_one_iff, or_comm]
  rw [hKernel]
  exact (Set.finite_singleton ambientPinMinusCentralSign).insert 1

/-- The bundled orthogonal projection has the same exact two-element
kernel as its underlying linear projection. -/
theorem ambientPinMinusOrthogonalProjection_eq_one_iff
    (lift : AmbientCoordinatePinMinusGroup) :
    ambientPinMinusOrthogonalProjection lift = 1 ↔
      lift = 1 ∨ lift = ambientPinMinusCentralSign := by
  rw [← ambientPinMinusProjection_eq_one_iff]
  constructor
  · intro hProjection
    apply DFunLike.coe_injective
    funext tangent
    exact DFunLike.congr_fun hProjection tangent
  · intro hProjection
    apply DFunLike.coe_injective
    funext tangent
    exact DFunLike.congr_fun hProjection tangent

/-- The kernel-finiteness hypothesis used by the covering-map reduction is
therefore discharged unconditionally. -/
theorem ambientPinMinusOrthogonalProjection_kernel_finite :
    ((ambientPinMinusOrthogonalProjection.ker :
        Subgroup AmbientCoordinatePinMinusGroup) :
      Set AmbientCoordinatePinMinusGroup).Finite := by
  have hKernel :
      ((ambientPinMinusOrthogonalProjection.ker :
          Subgroup AmbientCoordinatePinMinusGroup) :
        Set AmbientCoordinatePinMinusGroup) =
        {1, ambientPinMinusCentralSign} := by
    ext lift
    change ambientPinMinusOrthogonalProjection lift = 1 ↔
      lift = 1 ∨ lift = ambientPinMinusCentralSign
    exact ambientPinMinusOrthogonalProjection_eq_one_iff lift
  rw [hKernel]
  exact (Set.finite_singleton ambientPinMinusCentralSign).insert 1

end
end P0EFTJanusMappingTorusAmbientPinMinusProjectionKernel4D
end JanusFormal
