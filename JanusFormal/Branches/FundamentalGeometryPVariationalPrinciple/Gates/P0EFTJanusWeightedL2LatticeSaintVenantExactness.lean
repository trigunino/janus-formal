import Mathlib.Analysis.InnerProductSpace.l2Space
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusLatticeFourierSaintVenantExactness

/-!
# Weighted `ell^2` lattice Saint-Venant exactness

This gate realizes the coefficientwise `Z^4` reconstruction on completed
Hilbert spaces.  A positive Fourier weight is represented by storing the
scaled coefficients `sqrt(weight k) * a k`; because every symbol used below
acts mode by mode, the common scale commutes with the symbols.

The dominant-pivot reconstruction is a bounded operator from the sixteen
metric coefficients to the four potential coefficients.  The Lorentz-Gram
symbol itself has order one, so it is not claimed to be bounded on the same
weighted space: it is defined on its honest maximal domain.  Its range is
exactly the closed subspace of symmetric, compatible, zero-mode-free metric
coefficients.  The zero mode remains the explicit finite-dimensional
obstruction.
-/

namespace JanusFormal
namespace P0EFTJanusWeightedL2LatticeSaintVenantExactness

set_option autoImplicit false

noncomputable section

open scoped ENNReal lp
open P0EFTJanusArbitraryFrequencySaintVenantExactness
open P0EFTJanusFiniteFourierSaintVenantExactness
open P0EFTJanusLatticeFourierSaintVenantExactness

/-- Four potential coordinates with their Euclidean norm. -/
abbrev PotentialFiber := EuclideanSpace Real Index4

/-- Sixteen metric coordinates with their Euclidean norm. -/
abbrev MetricFiber := EuclideanSpace Real (Index4 × Index4)

/-- Completed weighted-coordinate potential space.  An element stores
`sqrt(weight mode)` times the physical coefficient. -/
abbrev WeightedPotentialHilbert (_weight : LatticeMode → Real) :=
  lp (fun _ : LatticeMode => PotentialFiber) 2

/-- Completed weighted-coordinate metric space. -/
abbrev WeightedMetricHilbert (_weight : LatticeMode → Real) :=
  lp (fun _ : LatticeMode => MetricFiber) 2

example (weight : LatticeMode → Real) :
    CompleteSpace (WeightedPotentialHilbert weight) := inferInstance

example (weight : LatticeMode → Real) :
    InnerProductSpace Real (WeightedPotentialHilbert weight) := inferInstance

example (weight : LatticeMode → Real) :
    CompleteSpace (WeightedMetricHilbert weight) := inferInstance

example (weight : LatticeMode → Real) :
    InnerProductSpace Real (WeightedMetricHilbert weight) := inferInstance

/-- Physical potential coefficients belong to weighted `ell^2` exactly when
their `sqrt(weight)`-scaled Euclidean fibers belong to ordinary `ell^2`. -/
def weightedPotentialCoordinates
    (weight : LatticeMode → Real) (potential : LatticePotential) :
    LatticeMode → PotentialFiber :=
  fun mode => WithLp.toLp 2 (fun index =>
    Real.sqrt (weight mode) * potential mode index)

def PotentialInWeightedL2
    (weight : LatticeMode → Real) (potential : LatticePotential) : Prop :=
  Memℓp (weightedPotentialCoordinates weight potential) 2

/-- Physical metric coefficients and their weighted Hilbert coordinates. -/
def weightedMetricCoordinates
    (weight : LatticeMode → Real) (tensor : LatticeMetricCoefficient) :
    LatticeMode → MetricFiber :=
  fun mode => WithLp.toLp 2 (fun pair =>
    Real.sqrt (weight mode) * tensor mode pair.1 pair.2)

def MetricInWeightedL2
    (weight : LatticeMode → Real)
    (tensor : LatticeMetricCoefficient) : Prop :=
  Memℓp (weightedMetricCoordinates weight tensor) 2

def encodeWeightedPotential
    (weight : LatticeMode → Real) (potential : LatticePotential)
    (hPotential : PotentialInWeightedL2 weight potential) :
    WeightedPotentialHilbert weight :=
  ⟨weightedPotentialCoordinates weight potential, hPotential⟩

def encodeWeightedMetric
    (weight : LatticeMode → Real) (tensor : LatticeMetricCoefficient)
    (hTensor : MetricInWeightedL2 weight tensor) :
    WeightedMetricHilbert weight :=
  ⟨weightedMetricCoordinates weight tensor, hTensor⟩

/-- Decode weighted coordinates when the Fourier weight is strictly
positive. -/
def decodeWeightedPotential
    (weight : LatticeMode → Real) (_hWeight : ∀ mode, 0 < weight mode)
    (potential : WeightedPotentialHilbert weight) : LatticePotential :=
  fun mode index => potential mode index / Real.sqrt (weight mode)

def decodeWeightedMetric
    (weight : LatticeMode → Real) (_hWeight : ∀ mode, 0 < weight mode)
    (tensor : WeightedMetricHilbert weight) : LatticeMetricCoefficient :=
  fun mode row column =>
    tensor mode (row, column) / Real.sqrt (weight mode)

theorem decode_encode_weightedPotential
    (weight : LatticeMode → Real) (hWeight : ∀ mode, 0 < weight mode)
    (potential : LatticePotential)
    (hPotential : PotentialInWeightedL2 weight potential) :
    decodeWeightedPotential weight hWeight
      (encodeWeightedPotential weight potential hPotential) = potential := by
  funext mode index
  change (Real.sqrt (weight mode) * potential mode index) /
      Real.sqrt (weight mode) = potential mode index
  exact mul_div_cancel_left₀ _ (Real.sqrt_ne_zero'.2 (hWeight mode))

theorem decode_encode_weightedMetric
    (weight : LatticeMode → Real) (hWeight : ∀ mode, 0 < weight mode)
    (tensor : LatticeMetricCoefficient)
    (hTensor : MetricInWeightedL2 weight tensor) :
    decodeWeightedMetric weight hWeight
      (encodeWeightedMetric weight tensor hTensor) = tensor := by
  funext mode row column
  change (Real.sqrt (weight mode) * tensor mode row column) /
      Real.sqrt (weight mode) = tensor mode row column
  exact mul_div_cancel_left₀ _ (Real.sqrt_ne_zero'.2 (hWeight mode))

theorem decodedPotential_mem_weightedL2
    (weight : LatticeMode → Real) (hWeight : ∀ mode, 0 < weight mode)
    (potential : WeightedPotentialHilbert weight) :
    PotentialInWeightedL2 weight
      (decodeWeightedPotential weight hWeight potential) := by
  have hCoordinates : weightedPotentialCoordinates weight
      (decodeWeightedPotential weight hWeight potential) = potential := by
    funext mode
    ext index
    change Real.sqrt (weight mode) *
        (potential mode index / Real.sqrt (weight mode)) =
      potential mode index
    exact mul_div_cancel₀ _ (Real.sqrt_ne_zero'.2 (hWeight mode))
  rw [PotentialInWeightedL2, hCoordinates]
  exact potential.2

theorem decodedMetric_mem_weightedL2
    (weight : LatticeMode → Real) (hWeight : ∀ mode, 0 < weight mode)
    (tensor : WeightedMetricHilbert weight) :
    MetricInWeightedL2 weight
      (decodeWeightedMetric weight hWeight tensor) := by
  have hCoordinates : weightedMetricCoordinates weight
      (decodeWeightedMetric weight hWeight tensor) = tensor := by
    funext mode
    ext pair
    change Real.sqrt (weight mode) *
        (tensor mode pair / Real.sqrt (weight mode)) = tensor mode pair
    exact mul_div_cancel₀ _ (Real.sqrt_ne_zero'.2 (hWeight mode))
  rw [MetricInWeightedL2, hCoordinates]
  exact tensor.2

theorem encode_decode_weightedPotential
    (weight : LatticeMode → Real) (hWeight : ∀ mode, 0 < weight mode)
    (potential : WeightedPotentialHilbert weight) :
    encodeWeightedPotential weight
      (decodeWeightedPotential weight hWeight potential)
      (decodedPotential_mem_weightedL2 weight hWeight potential) =
        potential := by
  apply Subtype.ext
  funext mode
  ext index
  change Real.sqrt (weight mode) *
      (potential mode index / Real.sqrt (weight mode)) =
    potential mode index
  exact mul_div_cancel₀ _ (Real.sqrt_ne_zero'.2 (hWeight mode))

theorem encode_decode_weightedMetric
    (weight : LatticeMode → Real) (hWeight : ∀ mode, 0 < weight mode)
    (tensor : WeightedMetricHilbert weight) :
    encodeWeightedMetric weight (decodeWeightedMetric weight hWeight tensor)
      (decodedMetric_mem_weightedL2 weight hWeight tensor) = tensor := by
  apply Subtype.ext
  funext mode
  ext pair
  change Real.sqrt (weight mode) *
      (tensor mode pair / Real.sqrt (weight mode)) = tensor mode pair
  exact mul_div_cancel₀ _ (Real.sqrt_ne_zero'.2 (hWeight mode))

/-- Forget the Hilbert packaging and expose the encoded potential
coefficients. -/
def encodedPotentialCoefficient
    {weight : LatticeMode → Real}
    (potential : WeightedPotentialHilbert weight) : LatticePotential :=
  fun mode index => potential mode index

/-- Forget the Hilbert packaging and expose the encoded metric coefficients. -/
def encodedMetricCoefficient
    {weight : LatticeMode → Real}
    (tensor : WeightedMetricHilbert weight) : LatticeMetricCoefficient :=
  fun mode row column => tensor mode (row, column)

@[simp]
theorem encodedPotentialCoefficient_add
    {weight : LatticeMode → Real}
    (first second : WeightedPotentialHilbert weight) :
    encodedPotentialCoefficient (first + second) =
      encodedPotentialCoefficient first + encodedPotentialCoefficient second := by
  funext mode index
  change (first + second) mode index = first mode index + second mode index
  simp

@[simp]
theorem encodedPotentialCoefficient_smul
    {weight : LatticeMode → Real}
    (scalar : Real) (potential : WeightedPotentialHilbert weight) :
    encodedPotentialCoefficient (scalar • potential) =
      scalar • encodedPotentialCoefficient potential := by
  funext mode index
  change (scalar • potential) mode index = scalar * potential mode index
  simp

@[simp]
theorem encodedMetricCoefficient_add
    {weight : LatticeMode → Real}
    (first second : WeightedMetricHilbert weight) :
    encodedMetricCoefficient (first + second) =
      encodedMetricCoefficient first + encodedMetricCoefficient second := by
  funext mode row column
  change (first + second) mode (row, column) =
    first mode (row, column) + second mode (row, column)
  simp

@[simp]
theorem encodedMetricCoefficient_smul
    {weight : LatticeMode → Real}
    (scalar : Real) (tensor : WeightedMetricHilbert weight) :
    encodedMetricCoefficient (scalar • tensor) =
      scalar • encodedMetricCoefficient tensor := by
  funext mode row column
  change (scalar • tensor) mode (row, column) =
    scalar * tensor mode (row, column)
  simp

theorem latticeReconstructedPotential_add
    (first second : LatticeMetricCoefficient) :
    latticeReconstructedPotential (first + second) =
      latticeReconstructedPotential first +
        latticeReconstructedPotential second := by
  funext mode index
  by_cases hMode : mode = 0
  · simp [latticeReconstructedPotential, hMode]
  · simp only [latticeReconstructedPotential, if_neg hMode, Pi.add_apply,
      Matrix.add_apply, lorentzLower, reconstructedVariation]
    ring

theorem latticeReconstructedPotential_smul
    (scalar : Real) (tensor : LatticeMetricCoefficient) :
    latticeReconstructedPotential (scalar • tensor) =
      scalar • latticeReconstructedPotential tensor := by
  funext mode index
  by_cases hMode : mode = 0
  · simp [latticeReconstructedPotential, hMode]
  · simp only [latticeReconstructedPotential, if_neg hMode, Pi.smul_apply,
      Matrix.smul_apply, lorentzLower, reconstructedVariation, smul_eq_mul]
    ring

/-- Modewise dominant-pivot reconstruction in Euclidean fibers. -/
def reconstructedFiber
    {weight : LatticeMode → Real}
    (tensor : WeightedMetricHilbert weight) (mode : LatticeMode) :
    PotentialFiber :=
  WithLp.toLp 2 (latticeReconstructedPotential
    (encodedMetricCoefficient tensor) mode)

theorem reconstructedFiber_sq_norm_le
    {weight : LatticeMode → Real}
    (tensor : WeightedMetricHilbert weight) (mode : LatticeMode) :
    ‖reconstructedFiber tensor mode‖ ^ 2 ≤ 4 * ‖tensor mode‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq]
  simp only [Real.norm_eq_abs, sq_abs, reconstructedFiber, PiLp.toLp_apply]
  calc
    (∑ index : Index4,
        (latticeReconstructedPotential
          (encodedMetricCoefficient tensor) mode index) ^ 2)
        ≤ ∑ index : Index4,
            (2 * (∑ row : Index4,
              (encodedMetricCoefficient tensor mode row index) ^ 2) +
            (1 / 2 : Real) * (∑ row : Index4,
              (encodedMetricCoefficient tensor mode row row) ^ 2)) := by
          exact Finset.sum_le_sum fun index _ =>
            latticeReconstructedPotential_sq_le_finiteSum
              (encodedMetricCoefficient tensor) mode index
    _ ≤ 4 * ∑ pair : Index4 × Index4,
          (tensor mode pair) ^ 2 := by
      simp only [encodedMetricCoefficient]
      rw [Finset.sum_add_distrib]
      have hColumn :
          (∑ index : Index4, 2 * ∑ row : Index4,
            (tensor mode (row, index)) ^ 2) ≤
            2 * ∑ pair : Index4 × Index4, (tensor mode pair) ^ 2 := by
        rw [← Finset.mul_sum]
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [Fintype.sum_prod_type, Finset.sum_comm]
      have hDiagonal :
          (∑ index : Index4, (1 / 2 : Real) * ∑ row : Index4,
            (tensor mode (row, row)) ^ 2) ≤
            2 * ∑ pair : Index4 × Index4, (tensor mode pair) ^ 2 := by
        simp only [Fin.sum_univ_four]
        have hDiag :
            (∑ row : Index4, (tensor mode (row, row)) ^ 2) ≤
              ∑ pair : Index4 × Index4, (tensor mode pair) ^ 2 := by
          rw [Fintype.sum_prod_type]
          apply Finset.sum_le_sum
          intro row _
          exact Finset.single_le_sum
            (fun column _ => sq_nonneg (tensor mode (row, column)))
            (Finset.mem_univ row)
        simp only [Fin.sum_univ_four] at hDiag
        nlinarith
      nlinarith

theorem reconstructedFiber_norm_le
    {weight : LatticeMode → Real}
    (tensor : WeightedMetricHilbert weight) (mode : LatticeMode) :
    ‖reconstructedFiber tensor mode‖ ≤ 2 * ‖tensor mode‖ := by
  have h := reconstructedFiber_sq_norm_le tensor mode
  nlinarith [norm_nonneg (reconstructedFiber tensor mode),
    norm_nonneg (tensor mode)]

/-- The reconstructed family is genuinely square summable in the completed
weighted-coordinate Hilbert space. -/
theorem reconstructedFiber_memℓp
    {weight : LatticeMode → Real}
    (tensor : WeightedMetricHilbert weight) :
    Memℓp (reconstructedFiber tensor) 2 := by
  refine ((2 : Real) • tensor).2.mono' ?_
  intro mode
  change ‖reconstructedFiber tensor mode‖ ≤ ‖(2 : Real) • tensor mode‖
  rw [norm_smul, Real.norm_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
  exact reconstructedFiber_norm_le tensor mode

/-- Bounded reconstruction on completed weighted `ell^2`; its operator norm
is at most two. -/
noncomputable def weightedReconstruction
    (weight : LatticeMode → Real) :
    WeightedMetricHilbert weight →L[Real] WeightedPotentialHilbert weight :=
  LinearMap.mkContinuous
    { toFun := fun tensor =>
        ⟨reconstructedFiber tensor, reconstructedFiber_memℓp tensor⟩
      map_add' := by
        intro first second
        ext mode index
        change latticeReconstructedPotential
            (encodedMetricCoefficient (first + second)) mode index =
          latticeReconstructedPotential
              (encodedMetricCoefficient first) mode index +
            latticeReconstructedPotential
              (encodedMetricCoefficient second) mode index
        rw [encodedMetricCoefficient_add]
        simpa only [Pi.add_apply] using congrFun
          (congrFun (latticeReconstructedPotential_add
            (encodedMetricCoefficient first)
            (encodedMetricCoefficient second)) mode) index
      map_smul' := by
        intro scalar tensor
        ext mode index
        change latticeReconstructedPotential
            (encodedMetricCoefficient (scalar • tensor)) mode index =
          scalar * latticeReconstructedPotential
            (encodedMetricCoefficient tensor) mode index
        rw [encodedMetricCoefficient_smul]
        simpa only [Pi.smul_apply, smul_eq_mul] using congrFun
          (congrFun (latticeReconstructedPotential_smul scalar
            (encodedMetricCoefficient tensor)) mode) index }
    2 (fun tensor => by
      calc
        ‖(⟨reconstructedFiber tensor,
            reconstructedFiber_memℓp tensor⟩ :
            WeightedPotentialHilbert weight)‖ ≤
            ‖((2 : Real) • tensor : WeightedMetricHilbert weight)‖ := by
              apply lp.norm_mono (by norm_num)
              intro mode
              change ‖reconstructedFiber tensor mode‖ ≤
                ‖(2 : Real) • tensor mode‖
              rw [norm_smul,
                Real.norm_of_nonneg (by norm_num : (0 : Real) ≤ 2)]
              exact reconstructedFiber_norm_le tensor mode
        _ = 2 * ‖tensor‖ := by
          rw [norm_smul, Real.norm_of_nonneg
            (by norm_num : (0 : Real) ≤ 2)])

theorem weightedReconstruction_opNorm_le
    (weight : LatticeMode → Real) :
    ‖weightedReconstruction weight‖ ≤ 2 := by
  unfold weightedReconstruction
  apply LinearMap.mkContinuous_norm_le
  norm_num

/-- The encoded Lorentz-Gram symbol.  This order-one family need not be in
the target `ell^2` space for an arbitrary potential. -/
def encodedLorentzGramFiber
    {weight : LatticeMode → Real}
    (potential : WeightedPotentialHilbert weight) (mode : LatticeMode) :
    MetricFiber :=
  WithLp.toLp 2 (fun pair : Index4 × Index4 =>
    latticeLorentzGram (encodedPotentialCoefficient potential)
      mode pair.1 pair.2)

theorem latticeLorentzGram_add
    (first second : LatticePotential) :
    latticeLorentzGram (first + second) =
      latticeLorentzGram first + latticeLorentzGram second := by
  funext mode row column
  simp only [latticeLorentzGram, finiteFourierLorentzGram,
    lorentzGramSymbol, strainSymbol, Pi.add_apply, Matrix.add_apply,
    lorentzLower]
  ring

theorem latticeLorentzGram_smul
    (scalar : Real) (potential : LatticePotential) :
    latticeLorentzGram (scalar • potential) =
      scalar • latticeLorentzGram potential := by
  funext mode row column
  simp only [latticeLorentzGram, finiteFourierLorentzGram,
    lorentzGramSymbol, strainSymbol, Pi.smul_apply, Matrix.smul_apply,
    lorentzLower, smul_eq_mul]
  ring

@[simp]
theorem encodedLorentzGramFiber_zero
    {weight : LatticeMode → Real} :
    encodedLorentzGramFiber (0 : WeightedPotentialHilbert weight) = 0 := by
  funext mode
  ext pair
  change latticeLorentzGram (encodedPotentialCoefficient
    (0 : WeightedPotentialHilbert weight)) mode pair.1 pair.2 = 0
  have hCoefficient : encodedPotentialCoefficient
      (0 : WeightedPotentialHilbert weight) = 0 := by
    funext latticeMode index
    change (0 : WeightedPotentialHilbert weight) latticeMode index = 0
    simp
  rw [hCoefficient]
  simp [latticeLorentzGram, finiteFourierLorentzGram,
    lorentzGramSymbol, strainSymbol, lorentzLower]

@[simp]
theorem encodedLorentzGramFiber_add
    {weight : LatticeMode → Real}
    (first second : WeightedPotentialHilbert weight) :
    encodedLorentzGramFiber (first + second) =
      encodedLorentzGramFiber first + encodedLorentzGramFiber second := by
  funext mode
  ext pair
  change latticeLorentzGram (encodedPotentialCoefficient (first + second))
      mode pair.1 pair.2 =
    latticeLorentzGram (encodedPotentialCoefficient first)
        mode pair.1 pair.2 +
      latticeLorentzGram (encodedPotentialCoefficient second)
        mode pair.1 pair.2
  rw [encodedPotentialCoefficient_add]
  simpa only [Pi.add_apply, Matrix.add_apply] using congrFun
    (congrFun (congrFun (latticeLorentzGram_add
      (encodedPotentialCoefficient first)
      (encodedPotentialCoefficient second)) mode) pair.1) pair.2

@[simp]
theorem encodedLorentzGramFiber_smul
    {weight : LatticeMode → Real}
    (scalar : Real) (potential : WeightedPotentialHilbert weight) :
    encodedLorentzGramFiber (scalar • potential) =
      scalar • encodedLorentzGramFiber potential := by
  funext mode
  ext pair
  change latticeLorentzGram
      (encodedPotentialCoefficient (scalar • potential))
        mode pair.1 pair.2 =
    scalar * latticeLorentzGram (encodedPotentialCoefficient potential)
      mode pair.1 pair.2
  rw [encodedPotentialCoefficient_smul]
  simpa only [Pi.smul_apply, Matrix.smul_apply, smul_eq_mul] using congrFun
    (congrFun (congrFun (latticeLorentzGram_smul scalar
      (encodedPotentialCoefficient potential)) mode) pair.1) pair.2

/-- Axial lattice modes used to expose the order-one growth of the symbol. -/
def axialMode (n : Nat) : LatticeMode :=
  fun index => if index = 0 then (n : Int) else 0

def axialUnitVector : Vector4 :=
  fun index => if index = 0 then 1 else 0

/-- The Lorentz-Gram symbol cannot have a mode-independent same-scale bound:
on unit axial vectors one coordinate grows beyond every prescribed constant.
This is the explicit obstruction requiring a maximal domain for the symbol. -/
theorem lorentzGram_orderOne_obstruction (constant : Real) :
    ∃ mode : LatticeMode, ∃ variation : Vector4,
      constant < |strainSymbol (latticeFrequency mode)
        (lorentzLower variation) 0 0| ∧
      (∑ index : Index4, (variation index) ^ 2) = 1 := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max constant 0)
  refine ⟨axialMode n, axialUnitVector, ?_, ?_⟩
  · have hConstant : constant < (n : Real) :=
      lt_of_le_of_lt (le_max_left constant 0) hn
    have hSymbol : strainSymbol (latticeFrequency (axialMode n))
        (lorentzLower axialUnitVector) 0 0 = -2 * (n : Real) := by
      simp [strainSymbol, latticeFrequency, axialMode, axialUnitVector,
        lorentzLower, lorentzSign]
      ring
    rw [hSymbol, abs_of_nonpos (by
      nlinarith [(Nat.cast_nonneg n : (0 : Real) ≤ (n : Real))])]
    nlinarith
  · simp [axialUnitVector]

/-- Maximal domain of the order-one symbol on a fixed weighted Hilbert
scale. -/
def weightedLorentzGramDomain (weight : LatticeMode → Real) :
    Submodule Real (WeightedPotentialHilbert weight) where
  carrier := {potential | Memℓp (encodedLorentzGramFiber potential) 2}
  zero_mem' := by
    change Memℓp (encodedLorentzGramFiber
      (0 : WeightedPotentialHilbert weight)) 2
    rw [encodedLorentzGramFiber_zero]
    exact zero_memℓp
  add_mem' := by
    intro first second hFirst hSecond
    change Memℓp (encodedLorentzGramFiber (first + second)) 2
    rw [encodedLorentzGramFiber_add]
    exact hFirst.add hSecond
  smul_mem' := by
    intro scalar potential hPotential
    change Memℓp (encodedLorentzGramFiber (scalar • potential)) 2
    rw [encodedLorentzGramFiber_smul]
    exact hPotential.const_smul scalar

/-- Lorentz-Gram on its maximal domain. -/
noncomputable def weightedLorentzGram
    (weight : LatticeMode → Real)
    (potential : weightedLorentzGramDomain weight) :
    WeightedMetricHilbert weight :=
  ⟨encodedLorentzGramFiber potential.1, potential.2⟩

/-- Linear realization of the order-one symbol on its maximal domain. -/
noncomputable def weightedLorentzGramLinearMap
    (weight : LatticeMode → Real) :
    weightedLorentzGramDomain weight →ₗ[Real] WeightedMetricHilbert weight where
  toFun := weightedLorentzGram weight
  map_add' := by
    intro first second
    apply Subtype.ext
    exact encodedLorentzGramFiber_add first.1 second.1
  map_smul' := by
    intro scalar potential
    apply Subtype.ext
    exact encodedLorentzGramFiber_smul scalar potential.1

theorem latticeSaintVenant_add
    (first second : LatticeMetricCoefficient) :
    latticeSaintVenant (first + second) =
      latticeSaintVenant first + latticeSaintVenant second := by
  funext mode a b c d
  simp only [latticeSaintVenant, finiteFourierSaintVenant,
    saintVenantSymbol, Pi.add_apply, Matrix.add_apply]
  ring

theorem latticeSaintVenant_smul
    (scalar : Real) (tensor : LatticeMetricCoefficient) :
    latticeSaintVenant (scalar • tensor) =
      scalar • latticeSaintVenant tensor := by
  funext mode a b c d
  simp only [latticeSaintVenant, finiteFourierSaintVenant,
    saintVenantSymbol, Pi.smul_apply, Matrix.smul_apply, smul_eq_mul]
  ring

theorem latticeZeroModeResidual_add
    (first second : LatticeMetricCoefficient) :
    latticeZeroModeResidual (first + second) =
      latticeZeroModeResidual first + latticeZeroModeResidual second := by
  funext mode row column
  by_cases hMode : mode = 0 <;>
    simp [latticeZeroModeResidual, hMode, Matrix.add_apply]

theorem latticeZeroModeResidual_smul
    (scalar : Real) (tensor : LatticeMetricCoefficient) :
    latticeZeroModeResidual (scalar • tensor) =
      scalar • latticeZeroModeResidual tensor := by
  funext mode row column
  by_cases hMode : mode = 0 <;>
    simp [latticeZeroModeResidual, hMode, Matrix.smul_apply]

theorem encodedMetricCoefficient_zero
    {weight : LatticeMode → Real} :
    encodedMetricCoefficient (0 : WeightedMetricHilbert weight) = 0 := by
  funext mode row column
  change (0 : WeightedMetricHilbert weight) mode (row, column) = 0
  simp

theorem symmetricCoefficients_zero :
    SymmetricLatticeCoefficients (0 : LatticeMetricCoefficient) := by
  intro mode
  rfl

theorem symmetricCoefficients_add
    {first second : LatticeMetricCoefficient}
    (hFirst : SymmetricLatticeCoefficients first)
    (hSecond : SymmetricLatticeCoefficients second) :
    SymmetricLatticeCoefficients (first + second) := by
  intro mode
  ext row column
  have hFirstEntry := congrArg (fun matrix => matrix row column) (hFirst mode)
  have hSecondEntry := congrArg (fun matrix => matrix row column) (hSecond mode)
  simpa [Matrix.transpose_apply, Matrix.add_apply] using
    congrArg₂ (· + ·) hFirstEntry hSecondEntry

theorem symmetricCoefficients_smul
    (scalar : Real) {tensor : LatticeMetricCoefficient}
    (hTensor : SymmetricLatticeCoefficients tensor) :
    SymmetricLatticeCoefficients (scalar • tensor) := by
  intro mode
  ext row column
  have hEntry := congrArg (fun matrix => matrix row column) (hTensor mode)
  simpa [Matrix.transpose_apply, Matrix.smul_apply] using
    congrArg (fun value : Real => scalar * value) hEntry

/-- Symmetric, Saint-Venant-compatible metric coefficients with their sole
zero-frequency obstruction removed. -/
def CompatibleZeroFreeMetricSubspace (weight : LatticeMode → Real) :
    Submodule Real (WeightedMetricHilbert weight) where
  carrier := {tensor |
    SymmetricLatticeCoefficients (encodedMetricCoefficient tensor) ∧
    latticeSaintVenant (encodedMetricCoefficient tensor) = 0 ∧
    latticeZeroModeResidual (encodedMetricCoefficient tensor) = 0}
  zero_mem' := by
    change SymmetricLatticeCoefficients
        (encodedMetricCoefficient (0 : WeightedMetricHilbert weight)) ∧
      latticeSaintVenant
        (encodedMetricCoefficient (0 : WeightedMetricHilbert weight)) = 0 ∧
      latticeZeroModeResidual
        (encodedMetricCoefficient (0 : WeightedMetricHilbert weight)) = 0
    rw [encodedMetricCoefficient_zero]
    refine ⟨symmetricCoefficients_zero, ?_, ?_⟩
    · funext mode a b c d
      simp [latticeSaintVenant, finiteFourierSaintVenant,
        saintVenantSymbol]
    · funext mode row column
      simp [latticeZeroModeResidual]
  add_mem' := by
    intro first second hFirst hSecond
    change SymmetricLatticeCoefficients (encodedMetricCoefficient first) ∧
      latticeSaintVenant (encodedMetricCoefficient first) = 0 ∧
      latticeZeroModeResidual (encodedMetricCoefficient first) = 0 at hFirst
    change SymmetricLatticeCoefficients (encodedMetricCoefficient second) ∧
      latticeSaintVenant (encodedMetricCoefficient second) = 0 ∧
      latticeZeroModeResidual (encodedMetricCoefficient second) = 0 at hSecond
    change SymmetricLatticeCoefficients
        (encodedMetricCoefficient (first + second)) ∧
      latticeSaintVenant (encodedMetricCoefficient (first + second)) = 0 ∧
      latticeZeroModeResidual
        (encodedMetricCoefficient (first + second)) = 0
    rw [encodedMetricCoefficient_add]
    exact ⟨symmetricCoefficients_add hFirst.1 hSecond.1,
      by rw [latticeSaintVenant_add, hFirst.2.1, hSecond.2.1, add_zero],
      by rw [latticeZeroModeResidual_add, hFirst.2.2,
        hSecond.2.2, add_zero]⟩
  smul_mem' := by
    intro scalar tensor hTensor
    change SymmetricLatticeCoefficients (encodedMetricCoefficient tensor) ∧
      latticeSaintVenant (encodedMetricCoefficient tensor) = 0 ∧
      latticeZeroModeResidual (encodedMetricCoefficient tensor) = 0 at hTensor
    change SymmetricLatticeCoefficients
        (encodedMetricCoefficient (scalar • tensor)) ∧
      latticeSaintVenant (encodedMetricCoefficient (scalar • tensor)) = 0 ∧
      latticeZeroModeResidual
        (encodedMetricCoefficient (scalar • tensor)) = 0
    rw [encodedMetricCoefficient_smul]
    exact ⟨symmetricCoefficients_smul scalar hTensor.1,
      by rw [latticeSaintVenant_smul, hTensor.2.1, smul_zero],
      by rw [latticeZeroModeResidual_smul, hTensor.2.2, smul_zero]⟩

theorem latticeLorentzGram_symmetric (potential : LatticePotential) :
    SymmetricLatticeCoefficients (latticeLorentzGram potential) := by
  intro mode
  change (strainSymbol (latticeFrequency mode)
      (lorentzLower (potential mode))).transpose =
    strainSymbol (latticeFrequency mode) (lorentzLower (potential mode))
  exact strainSymbol_symmetric _ _

theorem latticeZeroModeResidual_latticeLorentzGram_eq_zero
    (potential : LatticePotential) :
    latticeZeroModeResidual (latticeLorentzGram potential) = 0 := by
  funext mode row column
  by_cases hMode : mode = 0
  · subst mode
    simp [latticeZeroModeResidual, latticeLorentzGram,
      finiteFourierLorentzGram, lorentzGramSymbol, strainSymbol,
      latticeFrequency]
  · simp [latticeZeroModeResidual, hMode]

theorem encodedPotentialCoefficient_weightedReconstruction
    (weight : LatticeMode → Real)
    (tensor : WeightedMetricHilbert weight) :
    encodedPotentialCoefficient (weightedReconstruction weight tensor) =
      latticeReconstructedPotential (encodedMetricCoefficient tensor) := by
  funext mode index
  rfl

theorem encodedMetricCoefficient_weightedLorentzGram
    (weight : LatticeMode → Real)
    (potential : weightedLorentzGramDomain weight) :
    encodedMetricCoefficient (weightedLorentzGram weight potential) =
      latticeLorentzGram (encodedPotentialCoefficient potential.1) := by
  funext mode row column
  rfl

/-- Exactness on the completed Hilbert scale: the maximal-domain symbol has
precisely the compatible zero-free range. -/
theorem weightedLorentzGram_range_eq_compatibleZeroFree
    (weight : LatticeMode → Real) :
    (weightedLorentzGramLinearMap weight).range =
      CompatibleZeroFreeMetricSubspace weight := by
  ext tensor
  constructor
  · rintro ⟨potential, rfl⟩
    change SymmetricLatticeCoefficients
        (encodedMetricCoefficient (weightedLorentzGram weight potential)) ∧
      latticeSaintVenant
        (encodedMetricCoefficient (weightedLorentzGram weight potential)) = 0 ∧
      latticeZeroModeResidual
        (encodedMetricCoefficient (weightedLorentzGram weight potential)) = 0
    rw [encodedMetricCoefficient_weightedLorentzGram]
    exact ⟨latticeLorentzGram_symmetric _,
      latticeSaintVenant_latticeLorentzGram_eq_zero _,
      latticeZeroModeResidual_latticeLorentzGram_eq_zero _⟩
  · intro hTensor
    change SymmetricLatticeCoefficients (encodedMetricCoefficient tensor) ∧
      latticeSaintVenant (encodedMetricCoefficient tensor) = 0 ∧
      latticeZeroModeResidual (encodedMetricCoefficient tensor) = 0 at hTensor
    have hDecomposition := lattice_zeroMode_decomposition
      (encodedMetricCoefficient tensor) hTensor.1 hTensor.2.1
    have hExact : encodedMetricCoefficient tensor =
        latticeLorentzGram (latticeReconstructedPotential
          (encodedMetricCoefficient tensor)) := by
      simpa [hTensor.2.2] using hDecomposition
    let reconstructed : WeightedPotentialHilbert weight :=
      weightedReconstruction weight tensor
    have hReconstructedCoefficient :
        encodedPotentialCoefficient reconstructed =
          latticeReconstructedPotential
            (encodedMetricCoefficient tensor) := by
      exact encodedPotentialCoefficient_weightedReconstruction weight tensor
    have hFiber : encodedLorentzGramFiber reconstructed = tensor := by
      funext mode
      ext pair
      change latticeLorentzGram
          (encodedPotentialCoefficient reconstructed)
          mode pair.1 pair.2 = tensor mode pair
      rw [hReconstructedCoefficient]
      exact (congrFun (congrFun (congrFun hExact mode) pair.1) pair.2).symm
    have hDomain : Memℓp (encodedLorentzGramFiber reconstructed) 2 := by
      rw [hFiber]
      exact tensor.2
    let domainPotential : weightedLorentzGramDomain weight :=
      ⟨reconstructed, hDomain⟩
    refine ⟨domainPotential, ?_⟩
    apply Subtype.ext
    exact hFiber

/-- Continuous extraction of one metric coefficient at one lattice mode. -/
def metricCoordinateCLM
    (weight : LatticeMode → Real) (mode : LatticeMode)
    (row column : Index4) :
    WeightedMetricHilbert weight →L[Real] Real :=
  (EuclideanSpace.proj (𝕜 := Real) (row, column)).comp
    (lp.evalCLM Real (fun _ : LatticeMode => MetricFiber) 2 mode)

@[simp]
theorem metricCoordinateCLM_apply
    (weight : LatticeMode → Real) (mode : LatticeMode)
    (row column : Index4) (tensor : WeightedMetricHilbert weight) :
    metricCoordinateCLM weight mode row column tensor =
      tensor mode (row, column) := rfl

/-- One scalar coordinate of the Saint-Venant symbol as a continuous linear
functional.  Continuity is only asserted after fixing the lattice mode. -/
def saintVenantCoordinateCLM
    (weight : LatticeMode → Real) (mode : LatticeMode)
    (a b c d : Index4) :
    WeightedMetricHilbert weight →L[Real] Real :=
  (latticeFrequency mode a * latticeFrequency mode c) •
      metricCoordinateCLM weight mode b d +
    (latticeFrequency mode b * latticeFrequency mode d) •
      metricCoordinateCLM weight mode a c -
    (latticeFrequency mode a * latticeFrequency mode d) •
      metricCoordinateCLM weight mode b c -
    (latticeFrequency mode b * latticeFrequency mode c) •
      metricCoordinateCLM weight mode a d

@[simp]
theorem saintVenantCoordinateCLM_apply
    (weight : LatticeMode → Real) (mode : LatticeMode)
    (a b c d : Index4) (tensor : WeightedMetricHilbert weight) :
    saintVenantCoordinateCLM weight mode a b c d tensor =
      latticeSaintVenant (encodedMetricCoefficient tensor)
        mode a b c d := by
  simp [saintVenantCoordinateCLM, latticeSaintVenant,
    finiteFourierSaintVenant, saintVenantSymbol,
    encodedMetricCoefficient]

def SymmetricMetricSet (weight : LatticeMode → Real) :
    Set (WeightedMetricHilbert weight) :=
  {tensor | SymmetricLatticeCoefficients (encodedMetricCoefficient tensor)}

def CompatibleMetricSet (weight : LatticeMode → Real) :
    Set (WeightedMetricHilbert weight) :=
  {tensor | latticeSaintVenant (encodedMetricCoefficient tensor) = 0}

def ZeroFreeMetricSet (weight : LatticeMode → Real) :
    Set (WeightedMetricHilbert weight) :=
  {tensor | latticeZeroModeResidual (encodedMetricCoefficient tensor) = 0}

theorem symmetric_iff_coordinates
    (weight : LatticeMode → Real)
    (tensor : WeightedMetricHilbert weight) :
    SymmetricLatticeCoefficients (encodedMetricCoefficient tensor) ↔
      ∀ mode row column,
        metricCoordinateCLM weight mode column row tensor =
          metricCoordinateCLM weight mode row column tensor := by
  constructor
  · intro hSymmetric mode row column
    have hEntry := congrArg (fun matrix => matrix row column)
      (hSymmetric mode)
    simpa [Matrix.transpose_apply, encodedMetricCoefficient] using hEntry
  · intro hCoordinates mode
    ext row column
    simpa [Matrix.transpose_apply, encodedMetricCoefficient] using
      hCoordinates mode row column

theorem compatible_iff_coordinates
    (weight : LatticeMode → Real)
    (tensor : WeightedMetricHilbert weight) :
    latticeSaintVenant (encodedMetricCoefficient tensor) = 0 ↔
      ∀ mode a b c d,
        saintVenantCoordinateCLM weight mode a b c d tensor = 0 := by
  constructor
  · intro hCompatible mode a b c d
    rw [saintVenantCoordinateCLM_apply]
    exact congrFun (congrFun (congrFun (congrFun
      (congrFun hCompatible mode) a) b) c) d
  · intro hCoordinates
    funext mode a b c d
    rw [← saintVenantCoordinateCLM_apply]
    exact hCoordinates mode a b c d

theorem zeroFree_iff_coordinates
    (weight : LatticeMode → Real)
    (tensor : WeightedMetricHilbert weight) :
    latticeZeroModeResidual (encodedMetricCoefficient tensor) = 0 ↔
      ∀ row column, metricCoordinateCLM weight 0 row column tensor = 0 := by
  constructor
  · intro hZero row column
    have hEntry := congrFun (congrFun (congrFun hZero 0) row) column
    simpa [latticeZeroModeResidual, encodedMetricCoefficient] using hEntry
  · intro hCoordinates
    funext mode row column
    by_cases hMode : mode = 0
    · subst mode
      simpa [latticeZeroModeResidual, encodedMetricCoefficient] using
        hCoordinates row column
    · simp [latticeZeroModeResidual, hMode]

theorem symmetricMetricSet_isClosed (weight : LatticeMode → Real) :
    IsClosed (SymmetricMetricSet weight) := by
  rw [show SymmetricMetricSet weight =
      ⋂ mode, ⋂ row, ⋂ column,
        {tensor | metricCoordinateCLM weight mode column row tensor =
          metricCoordinateCLM weight mode row column tensor} by
    ext tensor
    simp only [SymmetricMetricSet, Set.mem_setOf_eq, Set.mem_iInter]
    exact symmetric_iff_coordinates weight tensor]
  apply isClosed_iInter
  intro mode
  apply isClosed_iInter
  intro row
  apply isClosed_iInter
  intro column
  exact isClosed_eq (metricCoordinateCLM weight mode column row).continuous
    (metricCoordinateCLM weight mode row column).continuous

theorem compatibleMetricSet_isClosed (weight : LatticeMode → Real) :
    IsClosed (CompatibleMetricSet weight) := by
  rw [show CompatibleMetricSet weight =
      ⋂ mode, ⋂ a, ⋂ b, ⋂ c, ⋂ d,
        {tensor | saintVenantCoordinateCLM weight mode a b c d tensor = 0} by
    ext tensor
    simp only [CompatibleMetricSet, Set.mem_setOf_eq, Set.mem_iInter]
    exact compatible_iff_coordinates weight tensor]
  apply isClosed_iInter
  intro mode
  apply isClosed_iInter
  intro a
  apply isClosed_iInter
  intro b
  apply isClosed_iInter
  intro c
  apply isClosed_iInter
  intro d
  exact isClosed_eq (saintVenantCoordinateCLM weight mode a b c d).continuous
    continuous_const

theorem zeroFreeMetricSet_isClosed (weight : LatticeMode → Real) :
    IsClosed (ZeroFreeMetricSet weight) := by
  rw [show ZeroFreeMetricSet weight =
      ⋂ row, ⋂ column,
        {tensor | metricCoordinateCLM weight 0 row column tensor = 0} by
    ext tensor
    simp only [ZeroFreeMetricSet, Set.mem_setOf_eq, Set.mem_iInter]
    exact zeroFree_iff_coordinates weight tensor]
  apply isClosed_iInter
  intro row
  apply isClosed_iInter
  intro column
  exact isClosed_eq (metricCoordinateCLM weight 0 row column).continuous
    continuous_const

theorem compatibleZeroFreeMetricSubspace_isClosed
    (weight : LatticeMode → Real) :
    IsClosed (CompatibleZeroFreeMetricSubspace weight :
      Set (WeightedMetricHilbert weight)) := by
  rw [show (CompatibleZeroFreeMetricSubspace weight :
      Set (WeightedMetricHilbert weight)) =
      SymmetricMetricSet weight ∩
        (CompatibleMetricSet weight ∩ ZeroFreeMetricSet weight) by rfl]
  exact (symmetricMetricSet_isClosed weight).inter
    ((compatibleMetricSet_isClosed weight).inter
      (zeroFreeMetricSet_isClosed weight))

/-- The exact symbol range is closed in the completed weighted metric
Hilbert space. -/
theorem weightedLorentzGram_range_isClosed
    (weight : LatticeMode → Real) :
    IsClosed ((weightedLorentzGramLinearMap weight).range :
      Set (WeightedMetricHilbert weight)) := by
  rw [weightedLorentzGram_range_eq_compatibleZeroFree]
  exact compatibleZeroFreeMetricSubspace_isClosed weight

/-- The bounded projection onto the sixteen-dimensional zero-mode fiber. -/
def zeroModeFiber
    {weight : LatticeMode → Real}
    (tensor : WeightedMetricHilbert weight) (mode : LatticeMode) :
    MetricFiber :=
  if mode = 0 then tensor mode else 0

theorem zeroModeFiber_norm_le
    {weight : LatticeMode → Real}
    (tensor : WeightedMetricHilbert weight) (mode : LatticeMode) :
    ‖zeroModeFiber tensor mode‖ ≤ ‖tensor mode‖ := by
  by_cases hMode : mode = 0
  · simp [zeroModeFiber, hMode]
  · simp [zeroModeFiber, hMode]

theorem zeroModeFiber_memℓp
    {weight : LatticeMode → Real}
    (tensor : WeightedMetricHilbert weight) :
    Memℓp (zeroModeFiber tensor) 2 :=
  tensor.2.mono' (zeroModeFiber_norm_le tensor)

noncomputable def zeroModeProjection
    (weight : LatticeMode → Real) :
    WeightedMetricHilbert weight →L[Real] WeightedMetricHilbert weight :=
  LinearMap.mkContinuous
    { toFun := fun tensor => ⟨zeroModeFiber tensor, zeroModeFiber_memℓp tensor⟩
      map_add' := by
        intro first second
        ext mode pair
        by_cases hMode : mode = 0
        · subst mode
          simp [zeroModeFiber]
        · simp [zeroModeFiber, hMode]
      map_smul' := by
        intro scalar tensor
        ext mode pair
        by_cases hMode : mode = 0
        · subst mode
          simp [zeroModeFiber]
        · simp [zeroModeFiber, hMode] }
    1 (fun tensor => by
      change ‖(⟨zeroModeFiber tensor, zeroModeFiber_memℓp tensor⟩ :
        WeightedMetricHilbert weight)‖ ≤ 1 * ‖tensor‖
      have hBound :
          ‖(⟨zeroModeFiber tensor, zeroModeFiber_memℓp tensor⟩ :
            WeightedMetricHilbert weight)‖ ≤ ‖tensor‖ := by
        apply lp.norm_mono (by norm_num)
        exact zeroModeFiber_norm_le tensor
      simpa only [one_mul] using hBound)

theorem zeroModeProjection_opNorm_le
    (weight : LatticeMode → Real) :
    ‖zeroModeProjection weight‖ ≤ 1 := by
  unfold zeroModeProjection
  apply LinearMap.mkContinuous_norm_le
  norm_num

theorem encodedMetricCoefficient_zeroModeProjection
    (weight : LatticeMode → Real)
    (tensor : WeightedMetricHilbert weight) :
    encodedMetricCoefficient (zeroModeProjection weight tensor) =
      latticeZeroModeResidual (encodedMetricCoefficient tensor) := by
  funext mode row column
  by_cases hMode : mode = 0 <;>
    simp [zeroModeProjection, zeroModeFiber, latticeZeroModeResidual,
      encodedMetricCoefficient, hMode]

theorem zeroModeProjection_idempotent
    (weight : LatticeMode → Real)
    (tensor : WeightedMetricHilbert weight) :
    zeroModeProjection weight (zeroModeProjection weight tensor) =
      zeroModeProjection weight tensor := by
  ext mode pair
  by_cases hMode : mode = 0 <;>
    simp [zeroModeProjection, zeroModeFiber, hMode]

/-- Every symmetric compatible Hilbert coefficient splits into a symbol
image plus its bounded zero-mode projection. -/
theorem compatible_metric_hilbert_decomposition
    (weight : LatticeMode → Real)
    (tensor : WeightedMetricHilbert weight)
    (hSymmetric : SymmetricLatticeCoefficients
      (encodedMetricCoefficient tensor))
    (hCompatible : latticeSaintVenant
      (encodedMetricCoefficient tensor) = 0) :
    ∃ potential : weightedLorentzGramDomain weight,
      tensor = weightedLorentzGram weight potential +
        zeroModeProjection weight tensor := by
  have hDecomposition := lattice_zeroMode_decomposition
    (encodedMetricCoefficient tensor) hSymmetric hCompatible
  let reconstructed : WeightedPotentialHilbert weight :=
    weightedReconstruction weight tensor
  have hReconstructedCoefficient :
      encodedPotentialCoefficient reconstructed =
        latticeReconstructedPotential (encodedMetricCoefficient tensor) :=
    encodedPotentialCoefficient_weightedReconstruction weight tensor
  have hGramEq : encodedLorentzGramFiber reconstructed =
      tensor - zeroModeProjection weight tensor := by
    funext mode
    ext pair
    change latticeLorentzGram (encodedPotentialCoefficient reconstructed)
        mode pair.1 pair.2 =
      tensor mode pair - zeroModeProjection weight tensor mode pair
    rw [hReconstructedCoefficient]
    have hEntry := congrFun (congrFun (congrFun hDecomposition mode)
      pair.1) pair.2
    simp only [Pi.add_apply, Matrix.add_apply] at hEntry
    have hZeroEntry := congrFun (congrFun (congrFun
      (encodedMetricCoefficient_zeroModeProjection weight tensor) mode)
      pair.1) pair.2
    change zeroModeProjection weight tensor mode pair =
      latticeZeroModeResidual (encodedMetricCoefficient tensor)
        mode pair.1 pair.2 at hZeroEntry
    change tensor mode pair =
      latticeLorentzGram
          (latticeReconstructedPotential (encodedMetricCoefficient tensor))
          mode pair.1 pair.2 +
        latticeZeroModeResidual (encodedMetricCoefficient tensor)
          mode pair.1 pair.2 at hEntry
    linarith
  have hDomain : Memℓp (encodedLorentzGramFiber reconstructed) 2 := by
    rw [hGramEq]
    exact tensor.2.sub (zeroModeProjection weight tensor).2
  let domainPotential : weightedLorentzGramDomain weight :=
    ⟨reconstructed, hDomain⟩
  refine ⟨domainPotential, ?_⟩
  apply Subtype.ext
  funext mode
  ext pair
  have hEntry := congrArg (fun fiber : MetricFiber => fiber pair)
    (congrFun hGramEq mode)
  change encodedLorentzGramFiber reconstructed mode pair =
    tensor mode pair - zeroModeProjection weight tensor mode pair at hEntry
  change tensor mode pair = encodedLorentzGramFiber domainPotential.1 mode pair +
    zeroModeProjection weight tensor mode pair
  change tensor mode pair = encodedLorentzGramFiber reconstructed mode pair +
    zeroModeProjection weight tensor mode pair
  linarith

/-- Completed weighted exactness, bounded reconstruction, closed image, and
the isolated zero-mode obstruction. -/
theorem weighted_l2_lattice_saintVenant_exactness_gate
    (weight : LatticeMode → Real) :
    ‖weightedReconstruction weight‖ ≤ 2 ∧
    ‖zeroModeProjection weight‖ ≤ 1 ∧
    (weightedLorentzGramLinearMap weight).range =
      CompatibleZeroFreeMetricSubspace weight ∧
    IsClosed ((weightedLorentzGramLinearMap weight).range :
      Set (WeightedMetricHilbert weight)) ∧
    (∀ tensor : WeightedMetricHilbert weight,
      SymmetricLatticeCoefficients (encodedMetricCoefficient tensor) →
      latticeSaintVenant (encodedMetricCoefficient tensor) = 0 →
      ∃ potential : weightedLorentzGramDomain weight,
        tensor = weightedLorentzGram weight potential +
          zeroModeProjection weight tensor) := by
  exact ⟨weightedReconstruction_opNorm_le weight,
    zeroModeProjection_opNorm_le weight,
    weightedLorentzGram_range_eq_compatibleZeroFree weight,
    weightedLorentzGram_range_isClosed weight,
    compatible_metric_hilbert_decomposition weight⟩

end

end P0EFTJanusWeightedL2LatticeSaintVenantExactness
end JanusFormal
