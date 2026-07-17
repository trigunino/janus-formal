import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusD8NonabelianGhostPositiveMetricThroatBV4D

/-!
# Finite BV master model for the positive throat metric sector

This gate extracts, for each of the eight positive metric logarithms, a
two-step real CE orbit.  Its parity-odd differential is nonzero and
square-zero.  The parity-shifted cotangent carries the explicit canonical odd
antibracket.  The nonzero cotangent Hamiltonian `S(q,p) = p(dq)` satisfies the
classical master equation and generates the finite BRST differential.

The finite model embeds as a subcomplex of the previously constructed throat
field/antifield doublet.  No global BV antibracket on the smooth field space is
claimed.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff TensorProduct BigOperators
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusExteriorDiffeomorphismGhostBRST4D
open P0EFTJanusMappingTorusThreeGeneratorGlobalKoszulBRST4D
open P0EFTJanusMappingTorusD8NonabelianGhostKoszul4D
open P0EFTJanusMappingTorusD8NonabelianGhostLinearFullFieldBRST4D
open P0EFTJanusMappingTorusD8NonabelianGhostThroatBRST4D
open P0EFTJanusMappingTorusD8NonabelianGhostPositiveMetricThroatBV4D

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev throatData := fixedEquatorData period hPeriod
private abbrev EffectiveThroat := MappingTorus (throatData period hPeriod)
private abbrev Coefficient := GhostCoefficientExterior
private abbrev ThroatScalar := CInfinityThroatScalarField period hPeriod
private abbrev ThroatTotal := LLThroatExteriorScalarAlgebra period hPeriod

local instance effectiveThroatChartedSpace :
    ChartedSpace ThroatCoverModel (EffectiveThroat period hPeriod) :=
  fixedThroatQuotientChartedSpace period hPeriod

local instance effectiveThroatIsManifold :
    IsManifold throatCoverModelWithCorners ω (EffectiveThroat period hPeriod) :=
  fixedThroatQuotient_isManifold period hPeriod

/-! ## Finite two-step CE field complex -/

abbrev FiniteMetricCEIndex := PositiveMetricCoordinate × Fin 2

/-- Sixteen real coordinates: two adjacent CE degrees for each of the eight
positive metric logarithms. -/
abbrev FiniteMetricCEField := FiniteMetricCEIndex → Real

theorem finiteMetricCEField_finrank :
    Module.finrank Real FiniteMetricCEField = 16 := by
  simp [FiniteMetricCEField, FiniteMetricCEIndex,
    PositiveMetricCoordinate]

/-- `d(q₀,q₁) = (0,q₀)` independently at every metric coordinate. -/
def finiteMetricCEDifferential :
    FiniteMetricCEField →ₗ[Real] FiniteMetricCEField where
  toFun field index :=
    if index.2 = 0 then 0 else field (index.1, 0)
  map_add' first second := by
    funext index
    split_ifs with hIndex <;> simp [hIndex]
  map_smul' scalar field := by
    funext index
    split_ifs with hIndex <;> simp [hIndex]

@[simp]
theorem finiteMetricCEDifferential_apply
    (field : FiniteMetricCEField) (index : FiniteMetricCEIndex) :
    finiteMetricCEDifferential field index =
      if index.2 = 0 then 0 else field (index.1, 0) :=
  rfl

/-- Euclidean transpose of the finite differential. -/
def finiteMetricCETranspose :
    FiniteMetricCEField →ₗ[Real] FiniteMetricCEField where
  toFun field index :=
    if index.2 = 0 then field (index.1, 1) else 0
  map_add' first second := by
    funext index
    split_ifs with hIndex <;> simp [hIndex]
  map_smul' scalar field := by
    funext index
    split_ifs with hIndex <;> simp [hIndex]

@[simp]
theorem finiteMetricCETranspose_apply
    (field : FiniteMetricCEField) (index : FiniteMetricCEIndex) :
    finiteMetricCETranspose field index =
      if index.2 = 0 then field (index.1, 1) else 0 :=
  rfl

theorem finiteMetricCEDifferential_square_zero
    (field : FiniteMetricCEField) :
    finiteMetricCEDifferential (finiteMetricCEDifferential field) = 0 := by
  funext index
  by_cases hIndex : index.2 = 0
  · simp [finiteMetricCEDifferential, hIndex]
  · simp [finiteMetricCEDifferential, hIndex]

theorem finiteMetricCETranspose_square_zero
    (field : FiniteMetricCEField) :
    finiteMetricCETranspose (finiteMetricCETranspose field) = 0 := by
  funext index
  by_cases hIndex : index.2 = 0
  · simp [finiteMetricCETranspose, hIndex]
  · simp [finiteMetricCETranspose, hIndex]

/-- Homogeneous coordinate vector. -/
def finiteMetricBasis (target : FiniteMetricCEIndex) : FiniteMetricCEField :=
  fun index => if index = target then 1 else 0

theorem finiteMetricCEDifferential_nonzero :
    finiteMetricCEDifferential ≠ 0 := by
  intro hZero
  have hApply := LinearMap.congr_fun hZero
    (finiteMetricBasis (((0, 0), 0) : FiniteMetricCEIndex))
  have hCoordinate := congrFun hApply (((0, 0), 1) : FiniteMetricCEIndex)
  norm_num [finiteMetricCEDifferential, finiteMetricBasis] at hCoordinate

/-- CE parity: the first slot is odd and the second slot is even. -/
def finiteMetricCEParity (field : FiniteMetricCEField) :
    FiniteMetricCEField :=
  fun index => if index.2 = 0 then -field index else field index

theorem finiteMetricCEParity_involutive (field : FiniteMetricCEField) :
    finiteMetricCEParity (finiteMetricCEParity field) = field := by
  funext index
  by_cases hIndex : index.2 = 0 <;>
    simp [finiteMetricCEParity, hIndex]

theorem finiteMetricCEDifferential_parity_odd
    (field : FiniteMetricCEField) :
    finiteMetricCEParity (finiteMetricCEDifferential field) =
      -finiteMetricCEDifferential (finiteMetricCEParity field) := by
  funext index
  by_cases hIndex : index.2 = 0
  · simp [finiteMetricCEParity, finiteMetricCEDifferential, hIndex]
  · simp [finiteMetricCEParity, finiteMetricCEDifferential, hIndex]

theorem finiteMetricCETranspose_parity_odd
    (field : FiniteMetricCEField) :
    finiteMetricCEParity (finiteMetricCETranspose field) =
      -finiteMetricCETranspose (finiteMetricCEParity field) := by
  funext index
  by_cases hIndex : index.2 = 0
  · simp [finiteMetricCEParity, finiteMetricCETranspose, hIndex]
  · simp [finiteMetricCEParity, finiteMetricCETranspose, hIndex]

/-! ## Finite shifted cotangent and canonical odd bracket -/

abbrev FiniteMetricBVPhase := FiniteMetricCEField × FiniteMetricCEField

theorem finiteMetricBVPhase_finrank :
    Module.finrank Real FiniteMetricBVPhase = 32 := by
  simp [FiniteMetricBVPhase]

def finiteMetricDot (first second : FiniteMetricCEField) : Real :=
  ∑ coordinate : PositiveMetricCoordinate, ∑ slot : Fin 2,
    first (coordinate, slot) * second (coordinate, slot)

theorem finiteMetricDot_comm (first second : FiniteMetricCEField) :
    finiteMetricDot first second = finiteMetricDot second first := by
  apply Finset.sum_congr rfl
  intro coordinate _
  apply Finset.sum_congr rfl
  intro slot _
  exact mul_comm _ _

@[simp]
theorem finiteMetricDot_zero_left (field : FiniteMetricCEField) :
    finiteMetricDot 0 field = 0 := by
  simp [finiteMetricDot]

@[simp]
theorem finiteMetricDot_zero_right (field : FiniteMetricCEField) :
    finiteMetricDot field 0 = 0 := by
  simp [finiteMetricDot]

theorem finiteMetricDot_basis_left
    (index : FiniteMetricCEIndex) (field : FiniteMetricCEField) :
    finiteMetricDot (finiteMetricBasis index) field = field index := by
  rcases index with ⟨coordinate, slot⟩
  fin_cases slot <;>
    simp [finiteMetricDot, finiteMetricBasis, Fin.sum_univ_two]

theorem finiteMetricDot_basis_right
    (field : FiniteMetricCEField) (index : FiniteMetricCEIndex) :
    finiteMetricDot field (finiteMetricBasis index) = field index := by
  rw [finiteMetricDot_comm]
  exact finiteMetricDot_basis_left index field

theorem finiteMetricCETranspose_adjoint
    (antifield field : FiniteMetricCEField) :
    finiteMetricDot (finiteMetricCETranspose antifield) field =
      finiteMetricDot antifield (finiteMetricCEDifferential field) := by
  rw [finiteMetricDot, finiteMetricDot]
  apply Finset.sum_congr rfl
  intro coordinate _
  simp [Fin.sum_univ_two, finiteMetricCETranspose,
    finiteMetricCEDifferential]

/-- Parity on the shifted cotangent: `P` on fields and `-P` on
antifields. -/
def finiteMetricBVParity (phase : FiniteMetricBVPhase) :
    FiniteMetricBVPhase :=
  (finiteMetricCEParity phase.1, -finiteMetricCEParity phase.2)

theorem finiteMetricBVParity_involutive (phase : FiniteMetricBVPhase) :
    finiteMetricBVParity (finiteMetricBVParity phase) = phase := by
  apply Prod.ext
  · exact finiteMetricCEParity_involutive phase.1
  · funext index
    by_cases hIndex : index.2 = 0 <;>
      simp [finiteMetricBVParity, finiteMetricCEParity, hIndex]

/-- Hamiltonian BRST vector field on the finite shifted cotangent. -/
def finiteMetricBVBRST :
    FiniteMetricBVPhase →ₗ[Real] FiniteMetricBVPhase :=
  finiteMetricCEDifferential.prodMap finiteMetricCETranspose

theorem finiteMetricBVBRST_square_zero (phase : FiniteMetricBVPhase) :
    finiteMetricBVBRST (finiteMetricBVBRST phase) = 0 := by
  apply Prod.ext
  · exact finiteMetricCEDifferential_square_zero phase.1
  · exact finiteMetricCETranspose_square_zero phase.2

theorem finiteMetricBVBRST_parity_odd (phase : FiniteMetricBVPhase) :
    finiteMetricBVParity (finiteMetricBVBRST phase) =
      -finiteMetricBVBRST (finiteMetricBVParity phase) := by
  apply Prod.ext
  · exact finiteMetricCEDifferential_parity_odd phase.1
  · change -finiteMetricCEParity (finiteMetricCETranspose phase.2) =
      -finiteMetricCETranspose (-finiteMetricCEParity phase.2)
    rw [map_neg, neg_neg]
    simpa using congrArg Neg.neg
      (finiteMetricCETranspose_parity_odd phase.2)

/-- Formal parity of a homogeneous finite observable. -/
inductive FiniteBVParity
  | even
  | odd
  deriving DecidableEq

/-- The Koszul sign `(-1)^((|F|+1)(|G|+1))`. -/
def finiteBVOddKoszulSign : FiniteBVParity → FiniteBVParity → Real
  | .even, .even => -1
  | _, _ => 1

/-- Available parity of the odd bracket output. -/
def finiteBVOddBracketParity : FiniteBVParity → FiniteBVParity →
    FiniteBVParity
  | .even, .even => .odd
  | .even, .odd => .even
  | .odd, .even => .even
  | .odd, .odd => .odd

/-- Homogeneous polynomial observable supplied with its two canonical first
gradients.  The concrete observables below have their first-variation laws
proved separately. -/
structure FiniteBVObservable where
  parity : FiniteBVParity
  value : FiniteMetricBVPhase → Real
  fieldGradient : FiniteMetricBVPhase → FiniteMetricCEField
  antifieldGradient : FiniteMetricBVPhase → FiniteMetricCEField

/-- Canonical odd antibracket in finite Darboux coordinates. -/
def finiteBVOddAntibracket
    (first second : FiniteBVObservable) (phase : FiniteMetricBVPhase) : Real :=
  finiteMetricDot (first.fieldGradient phase)
      (second.antifieldGradient phase) -
    finiteBVOddKoszulSign first.parity second.parity *
      finiteMetricDot (second.fieldGradient phase)
        (first.antifieldGradient phase)

theorem finiteBVOddAntibracket_graded_skew
    (first second : FiniteBVObservable) (phase : FiniteMetricBVPhase) :
    finiteBVOddAntibracket first second phase =
      -finiteBVOddKoszulSign first.parity second.parity *
        finiteBVOddAntibracket second first phase := by
  rcases first with ⟨firstParity, firstValue, firstField,
    firstAntifield⟩
  rcases second with ⟨secondParity, secondValue, secondField,
    secondAntifield⟩
  cases firstParity <;> cases secondParity <;>
    simp [finiteBVOddAntibracket, finiteBVOddKoszulSign] ; ring

/-- Even field coordinate observable. -/
def finiteBVFieldCoordinateObservable
    (index : FiniteMetricCEIndex) : FiniteBVObservable where
  parity := .even
  value := fun phase => phase.1 index
  fieldGradient := fun _ => finiteMetricBasis index
  antifieldGradient := fun _ => 0

/-- Odd antifield coordinate observable. -/
def finiteBVAntifieldCoordinateObservable
    (index : FiniteMetricCEIndex) : FiniteBVObservable where
  parity := .odd
  value := fun phase => phase.2 index
  fieldGradient := fun _ => 0
  antifieldGradient := fun _ => finiteMetricBasis index

theorem finiteBVFieldCoordinateObservable_first_variation
    (index : FiniteMetricCEIndex) (phase variation : FiniteMetricBVPhase) :
    (finiteBVFieldCoordinateObservable index).value (phase + variation) =
      (finiteBVFieldCoordinateObservable index).value phase +
        finiteMetricDot
          ((finiteBVFieldCoordinateObservable index).fieldGradient phase)
          variation.1 +
        finiteMetricDot
          ((finiteBVFieldCoordinateObservable index).antifieldGradient phase)
          variation.2 := by
  simp [finiteBVFieldCoordinateObservable, finiteMetricDot_basis_left]

theorem finiteBVAntifieldCoordinateObservable_first_variation
    (index : FiniteMetricCEIndex) (phase variation : FiniteMetricBVPhase) :
    (finiteBVAntifieldCoordinateObservable index).value (phase + variation) =
      (finiteBVAntifieldCoordinateObservable index).value phase +
        finiteMetricDot
          ((finiteBVAntifieldCoordinateObservable index).fieldGradient phase)
          variation.1 +
        finiteMetricDot
          ((finiteBVAntifieldCoordinateObservable index).antifieldGradient phase)
          variation.2 := by
  simp [finiteBVAntifieldCoordinateObservable, finiteMetricDot_basis_left]

theorem finiteBVOddAntibracket_field_antifield
    (first second : FiniteMetricCEIndex) (phase : FiniteMetricBVPhase) :
    finiteBVOddAntibracket
        (finiteBVFieldCoordinateObservable first)
        (finiteBVAntifieldCoordinateObservable second) phase =
      if first = second then 1 else 0 := by
  simp [finiteBVOddAntibracket, finiteBVFieldCoordinateObservable,
    finiteBVAntifieldCoordinateObservable, finiteMetricDot_basis_left,
    finiteMetricBasis]

theorem finiteBVOddAntibracket_antifield_field
    (first second : FiniteMetricCEIndex) (phase : FiniteMetricBVPhase) :
    finiteBVOddAntibracket
        (finiteBVAntifieldCoordinateObservable first)
        (finiteBVFieldCoordinateObservable second) phase =
      -(if first = second then 1 else 0) := by
  simp [finiteBVOddAntibracket, finiteBVFieldCoordinateObservable,
    finiteBVAntifieldCoordinateObservable, finiteMetricDot_basis_left,
    finiteMetricBasis, finiteBVOddKoszulSign, eq_comm]

/-! ## Nontrivial master action and CME -/

/-- Nontrivial cotangent Hamiltonian `S(q,p) = p(dq)`. -/
def finiteMetricBVMasterAction (phase : FiniteMetricBVPhase) : Real :=
  finiteMetricDot phase.2 (finiteMetricCEDifferential phase.1)

/-- The master action with its exact canonical first gradients. -/
def finiteMetricBVMasterObservable : FiniteBVObservable where
  parity := .even
  value := finiteMetricBVMasterAction
  fieldGradient := fun phase => finiteMetricCETranspose phase.2
  antifieldGradient := fun phase => finiteMetricCEDifferential phase.1

@[simp]
theorem finiteMetricBVMasterObservable_parity :
    finiteMetricBVMasterObservable.parity = .even :=
  rfl

@[simp]
theorem finiteMetricBVMasterSelfBracket_parity :
    finiteBVOddBracketParity finiteMetricBVMasterObservable.parity
      finiteMetricBVMasterObservable.parity = .odd :=
  rfl

theorem finiteMetricBVMasterAction_first_variation
    (phase variation : FiniteMetricBVPhase) :
    finiteMetricBVMasterAction (phase + variation) =
      finiteMetricBVMasterAction phase +
        finiteMetricDot (finiteMetricCETranspose phase.2) variation.1 +
        finiteMetricDot (finiteMetricCEDifferential phase.1) variation.2 +
        finiteMetricDot variation.2
          (finiteMetricCEDifferential variation.1) := by
  have hAdjoint :=
    finiteMetricCETranspose_adjoint phase.2 variation.1
  have hCommute := finiteMetricDot_comm variation.2
    (finiteMetricCEDifferential phase.1)
  rw [finiteMetricBVMasterAction, finiteMetricBVMasterAction]
  simp only [Prod.fst_add, Prod.snd_add, map_add]
  rw [show finiteMetricDot (phase.2 + variation.2)
      (finiteMetricCEDifferential phase.1 +
        finiteMetricCEDifferential variation.1) =
      finiteMetricDot phase.2 (finiteMetricCEDifferential phase.1) +
        finiteMetricDot phase.2
          (finiteMetricCEDifferential variation.1) +
        finiteMetricDot variation.2
          (finiteMetricCEDifferential phase.1) +
        finiteMetricDot variation.2
          (finiteMetricCEDifferential variation.1) by
    simp only [finiteMetricDot, Pi.add_apply, add_mul, mul_add,
      Finset.sum_add_distrib]
    ring]
  rw [← hAdjoint, hCommute]

private def finiteMetricBVWitnessCoordinate : PositiveMetricCoordinate :=
  (0, 0)

theorem finiteMetricBVMasterAction_witness :
    finiteMetricBVMasterAction
        (finiteMetricBasis (finiteMetricBVWitnessCoordinate, 0),
          finiteMetricBasis (finiteMetricBVWitnessCoordinate, 1)) = 1 := by
  simp [finiteMetricBVMasterAction, finiteMetricDot, finiteMetricBasis,
    finiteMetricCEDifferential, finiteMetricBVWitnessCoordinate]

theorem finiteMetricBVMasterAction_nonzero :
    finiteMetricBVMasterAction ≠ 0 := by
  intro hZero
  have hWitness := congrFun hZero
    (finiteMetricBasis (finiteMetricBVWitnessCoordinate, 0),
      finiteMetricBasis (finiteMetricBVWitnessCoordinate, 1))
  rw [finiteMetricBVMasterAction_witness] at hWitness
  norm_num at hWitness

/-- Classical master equation in the finite canonical odd bracket. -/
theorem finiteMetricBV_classical_master_equation
    (phase : FiniteMetricBVPhase) :
    finiteBVOddAntibracket finiteMetricBVMasterObservable
        finiteMetricBVMasterObservable phase = 0 := by
  change finiteMetricDot (finiteMetricCETranspose phase.2)
        (finiteMetricCEDifferential phase.1) -
      (-1 : Real) *
        finiteMetricDot (finiteMetricCETranspose phase.2)
          (finiteMetricCEDifferential phase.1) = 0
  rw [finiteMetricCETranspose_adjoint,
    finiteMetricCEDifferential_square_zero]
  simp

/-- The master Hamiltonian generates the field BRST coordinates. -/
theorem finiteMetricBVMaster_generates_field
    (phase : FiniteMetricBVPhase) (index : FiniteMetricCEIndex) :
    finiteBVOddAntibracket finiteMetricBVMasterObservable
        (finiteBVFieldCoordinateObservable index) phase =
      (finiteMetricBVBRST phase).1 index := by
  simp [finiteBVOddAntibracket, finiteMetricBVMasterObservable,
    finiteBVFieldCoordinateObservable, finiteMetricDot_basis_left,
    finiteMetricBVBRST,
    finiteBVOddKoszulSign]
  by_cases hIndex : index.2 = 0 <;> simp [hIndex]

/-- The master Hamiltonian generates the antifield BRST coordinates. -/
theorem finiteMetricBVMaster_generates_antifield
    (phase : FiniteMetricBVPhase) (index : FiniteMetricCEIndex) :
    finiteBVOddAntibracket finiteMetricBVMasterObservable
        (finiteBVAntifieldCoordinateObservable index) phase =
      (finiteMetricBVBRST phase).2 index := by
  simp [finiteBVOddAntibracket, finiteMetricBVMasterObservable,
    finiteBVAntifieldCoordinateObservable,
    finiteMetricDot_basis_right, finiteMetricBVBRST,
    finiteBVOddKoszulSign]

theorem finiteMetricBVMasterAction_parity_even
    (phase : FiniteMetricBVPhase) :
    finiteMetricBVMasterAction (finiteMetricBVParity phase) =
      finiteMetricBVMasterAction phase := by
  simp [finiteMetricBVMasterAction, finiteMetricBVParity,
    finiteMetricDot, finiteMetricCEParity,
    finiteMetricCEDifferential, Fin.sum_univ_two]

/-! ## Intertwining with the existing throat BV doublet -/

private def finiteThroatCoefficientEmbed (coefficient : Coefficient) :
    ThroatTotal period hPeriod :=
  coefficient ⊗ₜ[Real] (1 : ThroatScalar period hPeriod)

@[simp]
private theorem finiteThroatCoefficientEmbed_zero :
    finiteThroatCoefficientEmbed period hPeriod 0 = 0 := by
  simp [finiteThroatCoefficientEmbed]

private theorem finiteThroatCoefficientEmbed_differential
    (coefficient : Coefficient) :
    throatCorrectedCombinedLinear period hPeriod
        (finiteThroatCoefficientEmbed period hPeriod coefficient) =
      finiteThroatCoefficientEmbed period hPeriod
        (spatialRotationKoszulDifferential coefficient) := by
  rw [finiteThroatCoefficientEmbed,
    throatCorrectedCombinedLinear_coefficient_rule]
  rfl

/-- Field embedding along `c₀, d c₀`. -/
def finiteMetricCEFieldEmbed
    (field : FiniteMetricCEField) :
    PositiveMetricThroatBRSTSector period hPeriod :=
  fun coordinate =>
    field (coordinate, 0) •
        finiteThroatCoefficientEmbed period hPeriod (oddGenerator 0) +
      field (coordinate, 1) •
        finiteThroatCoefficientEmbed period hPeriod
          (spatialRotationKoszulDifferential (oddGenerator 0))

/-- Shifted dual embedding, chosen so that `dᵀ` intertwines the existing
negative antifield differential. -/
def finiteMetricCEAntifieldEmbed
    (antifield : FiniteMetricCEField) :
    PositiveMetricThroatBRSTSector period hPeriod :=
  fun coordinate =>
    -antifield (coordinate, 0) •
        finiteThroatCoefficientEmbed period hPeriod
          (spatialRotationKoszulDifferential (oddGenerator 0)) +
      antifield (coordinate, 1) •
        finiteThroatCoefficientEmbed period hPeriod (oddGenerator 0)

def finiteMetricBVPhaseEmbed
    (phase : FiniteMetricBVPhase) :
    PositiveMetricFirstBVDoublet period hPeriod :=
  (finiteMetricCEFieldEmbed period hPeriod phase.1,
    finiteMetricCEAntifieldEmbed period hPeriod phase.2)

theorem finiteMetricCEFieldEmbed_intertwines
    (field : FiniteMetricCEField) :
    positiveMetricThroatBRST period hPeriod
        (finiteMetricCEFieldEmbed period hPeriod field) =
      finiteMetricCEFieldEmbed period hPeriod
        (finiteMetricCEDifferential field) := by
  funext coordinate
  simp only [positiveMetricThroatBRST_apply,
    finiteMetricCEFieldEmbed, map_add, map_smul,
    finiteThroatCoefficientEmbed_differential,
    spatialRotationKoszulDifferential_square_zero,
    finiteMetricCEDifferential_apply]
  simp [finiteThroatCoefficientEmbed]

theorem finiteMetricCEAntifieldEmbed_intertwines
    (antifield : FiniteMetricCEField) :
    -positiveMetricThroatBRST period hPeriod
        (finiteMetricCEAntifieldEmbed period hPeriod antifield) =
      finiteMetricCEAntifieldEmbed period hPeriod
        (finiteMetricCETranspose antifield) := by
  funext coordinate
  simp only [Pi.neg_apply, positiveMetricThroatBRST_apply,
    finiteMetricCEAntifieldEmbed, map_add, map_smul,
    finiteThroatCoefficientEmbed_differential,
    spatialRotationKoszulDifferential_square_zero,
    finiteMetricCETranspose_apply]
  simp only [finiteThroatCoefficientEmbed_zero, smul_zero, zero_smul, zero_add,
    if_true, one_ne_zero, if_false, add_zero]
  exact (neg_smul (antifield (coordinate, 1))
    (finiteThroatCoefficientEmbed period hPeriod
      (spatialRotationKoszulDifferential (oddGenerator 0)))).symm

/-- Exact compatibility of the finite Hamiltonian BRST vector field with the
previous throat field/antifield BRST doublet. -/
theorem finiteMetricBVPhaseEmbed_intertwines
    (phase : FiniteMetricBVPhase) :
    positiveMetricFirstBVBRST period hPeriod
        (finiteMetricBVPhaseEmbed period hPeriod phase) =
      finiteMetricBVPhaseEmbed period hPeriod
        (finiteMetricBVBRST phase) := by
  apply Prod.ext
  · exact finiteMetricCEFieldEmbed_intertwines period hPeriod phase.1
  · exact finiteMetricCEAntifieldEmbed_intertwines period hPeriod phase.2

end

end P0EFTJanusMappingTorusD8NonabelianGhostFinitePositiveMetricBVMaster4D
end JanusFormal
