import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusWeightedL2LatticeSaintVenantExactness

/-!
# A bounded shifted lattice-Sobolev realization of the Lorentz--Gram symbol

The same-scale Lorentz--Gram multiplier is genuinely unbounded.  This gate
uses its exact finite-dimensional operator norm at every lattice mode to add
one graph-Sobolev weight to the potential coefficients.  After normalization,
the order-one symbol is a contraction from the shifted potential Hilbert space
to the metric Hilbert space.

This is a periodic `Z^4` coefficient model.  It is not yet an identification
with Sobolev sections of the global Janus bundles or with throat boundary
conditions.
-/

namespace JanusFormal
namespace P0EFTJanusShiftedSobolevLatticeLorentzGram

set_option autoImplicit false

noncomputable section

open scoped ENNReal lp
open P0EFTJanusArbitraryFrequencySaintVenantExactness
open P0EFTJanusLatticeFourierSaintVenantExactness
open P0EFTJanusWeightedL2LatticeSaintVenantExactness

/-- The raw order-one symbol on one Euclidean Fourier fiber. -/
def rawLorentzGramFiber
    (mode : LatticeMode) (potential : PotentialFiber) : MetricFiber :=
  WithLp.toLp 2 (fun pair : Index4 × Index4 =>
    strainSymbol (latticeFrequency mode)
      (lorentzLower (fun index => potential index)) pair.1 pair.2)

/-- Linear packaging of the raw fiber symbol. -/
def rawLorentzGramFiberLinearMap
    (mode : LatticeMode) : PotentialFiber →ₗ[Real] MetricFiber where
  toFun := rawLorentzGramFiber mode
  map_add' := by
    intro first second
    ext pair
    simp [rawLorentzGramFiber, strainSymbol, lorentzLower]
    ring
  map_smul' := by
    intro scalar potential
    ext pair
    simp [rawLorentzGramFiber, strainSymbol, lorentzLower]
    ring

/-- Every single-mode symbol is continuous because its source is finite
dimensional. -/
def rawLorentzGramFiberCLM
    (mode : LatticeMode) : PotentialFiber →L[Real] MetricFiber :=
  LinearMap.toContinuousLinearMap (rawLorentzGramFiberLinearMap mode)

@[simp]
theorem rawLorentzGramFiberCLM_apply
    (mode : LatticeMode) (potential : PotentialFiber) :
    rawLorentzGramFiberCLM mode potential =
      rawLorentzGramFiber mode potential := rfl

/-- Strictly positive graph-Sobolev multiplier. -/
def symbolGraphScale (mode : LatticeMode) : Real :=
  1 + ‖rawLorentzGramFiberCLM mode‖

theorem symbolGraphScale_pos (mode : LatticeMode) :
    0 < symbolGraphScale mode := by
  unfold symbolGraphScale
  positivity

theorem rawLorentzGramFiber_norm_le_scale
    (mode : LatticeMode) (potential : PotentialFiber) :
    ‖rawLorentzGramFiber mode potential‖ ≤
      symbolGraphScale mode * ‖potential‖ := by
  calc
    ‖rawLorentzGramFiber mode potential‖ ≤
        ‖rawLorentzGramFiberCLM mode‖ * ‖potential‖ :=
      (rawLorentzGramFiberCLM mode).le_opNorm potential
    _ ≤ symbolGraphScale mode * ‖potential‖ := by
      apply mul_le_mul_of_nonneg_right
      · simp [symbolGraphScale]
      · exact norm_nonneg _

/-- The normalized order-one fiber multiplier. -/
def normalizedLorentzGramFiberCLM
    (mode : LatticeMode) : PotentialFiber →L[Real] MetricFiber :=
  (symbolGraphScale mode)⁻¹ • rawLorentzGramFiberCLM mode

theorem normalizedLorentzGramFiber_norm_le
    (mode : LatticeMode) (potential : PotentialFiber) :
    ‖normalizedLorentzGramFiberCLM mode potential‖ ≤ ‖potential‖ := by
  have hScale := symbolGraphScale_pos mode
  have hRaw := rawLorentzGramFiber_norm_le_scale mode potential
  rw [normalizedLorentzGramFiberCLM, smul_apply,
    norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hScale]
  calc
    (symbolGraphScale mode)⁻¹ * ‖rawLorentzGramFiber mode potential‖ ≤
        (symbolGraphScale mode)⁻¹ *
          (symbolGraphScale mode * ‖potential‖) := by
      exact mul_le_mul_of_nonneg_left hRaw (inv_nonneg.mpr hScale.le)
    _ = ‖potential‖ := by
      rw [← mul_assoc, inv_mul_cancel₀ hScale.ne', one_mul]

theorem rawLorentzGramFiber_eq_zero_iff
    (mode : LatticeMode) (hMode : mode ≠ 0)
    (potential : PotentialFiber) :
    rawLorentzGramFiber mode potential = 0 ↔ potential = 0 := by
  constructor
  · intro hRaw
    have hSymbol :
        lorentzGramSymbol (latticeFrequency mode)
          (fun index => potential index) = 0 := by
      funext row column
      have hEntry := congrArg
        (fun fiber : MetricFiber => fiber (row, column)) hRaw
      simpa [rawLorentzGramFiber, lorentzGramSymbol] using hEntry
    have hEqual :
        lorentzGramSymbol (latticeFrequency mode)
            (fun index => potential index) =
          lorentzGramSymbol (latticeFrequency mode) 0 := by
      calc
        lorentzGramSymbol (latticeFrequency mode)
            (fun index => potential index) = 0 := hSymbol
        _ = lorentzGramSymbol (latticeFrequency mode) 0 := by
          funext row column
          simp [lorentzGramSymbol, strainSymbol, lorentzLower]
    have hPotential := lorentzGramSymbol_injective
      (latticeFrequency mode) (latticeFrequency_ne_zero hMode) hEqual
    ext index
    exact congrFun hPotential index
  · rintro rfl
    ext pair
    simp [rawLorentzGramFiber, strainSymbol, lorentzLower]

theorem normalizedLorentzGramFiber_eq_zero_iff
    (mode : LatticeMode) (hMode : mode ≠ 0)
    (potential : PotentialFiber) :
    normalizedLorentzGramFiberCLM mode potential = 0 ↔ potential = 0 := by
  rw [normalizedLorentzGramFiberCLM, smul_apply]
  constructor
  · intro hNormalized
    apply (rawLorentzGramFiber_eq_zero_iff mode hMode potential).mp
    exact (smul_eq_zero.mp hNormalized).resolve_left
      (inv_ne_zero (symbolGraphScale_pos mode).ne')
  · intro hPotential
    have hRaw : rawLorentzGramFiber mode potential = 0 :=
      (rawLorentzGramFiber_eq_zero_iff mode hMode potential).2 hPotential
    change (symbolGraphScale mode)⁻¹ •
      rawLorentzGramFiber mode potential = 0
    rw [hRaw, smul_zero]

/-- Target weight and its one-symbol-order source weight. -/
def symbolShiftedSourceWeight
    (targetWeight : LatticeMode → Real) (mode : LatticeMode) : Real :=
  (Real.sqrt (targetWeight mode) * symbolGraphScale mode) ^ 2

theorem symbolShiftedSourceWeight_pos
    (targetWeight : LatticeMode → Real)
    (hTargetWeight : ∀ mode, 0 < targetWeight mode)
    (mode : LatticeMode) :
    0 < symbolShiftedSourceWeight targetWeight mode := by
  unfold symbolShiftedSourceWeight
  exact sq_pos_of_pos (mul_pos
    (Real.sqrt_pos.2 (hTargetWeight mode)) (symbolGraphScale_pos mode))

theorem sqrt_symbolShiftedSourceWeight
    (targetWeight : LatticeMode → Real)
    (mode : LatticeMode) :
    Real.sqrt (symbolShiftedSourceWeight targetWeight mode) =
      Real.sqrt (targetWeight mode) * symbolGraphScale mode := by
  rw [symbolShiftedSourceWeight, Real.sqrt_sq]
  exact mul_nonneg (Real.sqrt_nonneg _) (symbolGraphScale_pos mode).le

abbrev ShiftedPotentialHilbert (targetWeight : LatticeMode → Real) :=
  WeightedPotentialHilbert (symbolShiftedSourceWeight targetWeight)

abbrev SobolevMetricHilbert (targetWeight : LatticeMode → Real) :=
  WeightedMetricHilbert targetWeight

/-- Pointwise normalized symbol on the completed coefficient space. -/
def normalizedLorentzGramFibers
    {targetWeight : LatticeMode → Real}
    (potential : ShiftedPotentialHilbert targetWeight) :
    LatticeMode → MetricFiber :=
  fun mode => normalizedLorentzGramFiberCLM mode (potential mode)

theorem normalizedLorentzGramFibers_memℓp
    {targetWeight : LatticeMode → Real}
    (potential : ShiftedPotentialHilbert targetWeight) :
    Memℓp (normalizedLorentzGramFibers potential) 2 :=
  potential.2.mono' (fun mode =>
    normalizedLorentzGramFiber_norm_le mode (potential mode))

/-- The order-one Lorentz--Gram symbol becomes a bounded contraction after
one graph-Sobolev shift. -/
def shiftedSobolevLorentzGram
    (targetWeight : LatticeMode → Real) :
    ShiftedPotentialHilbert targetWeight →L[Real]
      SobolevMetricHilbert targetWeight :=
  LinearMap.mkContinuous
    { toFun := fun potential =>
        ⟨normalizedLorentzGramFibers potential,
          normalizedLorentzGramFibers_memℓp potential⟩
      map_add' := by
        intro first second
        ext mode pair
        simp [normalizedLorentzGramFibers]
      map_smul' := by
        intro scalar potential
        ext mode pair
        simp [normalizedLorentzGramFibers] }
    1 (fun potential => by
      change ‖(⟨normalizedLorentzGramFibers potential,
          normalizedLorentzGramFibers_memℓp potential⟩ :
        SobolevMetricHilbert targetWeight)‖ ≤ 1 * ‖potential‖
      have hBound :
          ‖(⟨normalizedLorentzGramFibers potential,
              normalizedLorentzGramFibers_memℓp potential⟩ :
            SobolevMetricHilbert targetWeight)‖ ≤ ‖potential‖ := by
        apply lp.norm_mono (by norm_num)
        exact fun mode =>
          normalizedLorentzGramFiber_norm_le mode (potential mode)
      simpa only [one_mul] using hBound)

theorem shiftedSobolevLorentzGram_opNorm_le
    (targetWeight : LatticeMode → Real) :
    ‖shiftedSobolevLorentzGram targetWeight‖ ≤ 1 := by
  unfold shiftedSobolevLorentzGram
  apply LinearMap.mkContinuous_norm_le
  norm_num

/-- The only kernel of the shifted symbol is the finite-dimensional zero
Fourier mode. -/
theorem shiftedSobolevLorentzGram_eq_zero_iff
    (targetWeight : LatticeMode → Real)
    (potential : ShiftedPotentialHilbert targetWeight) :
    shiftedSobolevLorentzGram targetWeight potential = 0 ↔
      ∀ mode : LatticeMode, mode ≠ 0 → potential mode = 0 := by
  constructor
  · intro hSymbol mode hMode
    have hFiber := congrArg
      (fun tensor : SobolevMetricHilbert targetWeight => tensor mode) hSymbol
    change normalizedLorentzGramFiberCLM mode (potential mode) = 0 at hFiber
    exact (normalizedLorentzGramFiber_eq_zero_iff mode hMode
      (potential mode)).mp hFiber
  · intro hPotential
    apply Subtype.ext
    funext mode
    change normalizedLorentzGramFiberCLM mode (potential mode) = 0
    by_cases hMode : mode = 0
    · subst mode
      ext pair
      simp [normalizedLorentzGramFiberCLM, rawLorentzGramFiberCLM,
        rawLorentzGramFiberLinearMap, rawLorentzGramFiber, strainSymbol,
        lorentzLower, latticeFrequency]
    · rw [hPotential mode hMode]
      simp

/-- Exact coefficient bridge: the normalized shifted operator is the physical
Lorentz--Gram symbol written in source and target weighted coordinates. -/
theorem normalizedLorentzGramFibers_encode_eq_weightedMetricCoordinates
    (targetWeight : LatticeMode → Real)
    (potential : LatticePotential)
    (hPotential : PotentialInWeightedL2
      (symbolShiftedSourceWeight targetWeight) potential) :
    normalizedLorentzGramFibers
        (encodeWeightedPotential
          (symbolShiftedSourceWeight targetWeight) potential hPotential) =
      weightedMetricCoordinates targetWeight
        (latticeLorentzGram potential) := by
  funext mode
  ext pair
  have hScale := symbolGraphScale_pos mode
  change (symbolGraphScale mode)⁻¹ *
      (latticeFrequency mode pair.1 *
          (lorentzSign pair.2 *
            (Real.sqrt (symbolShiftedSourceWeight targetWeight mode) *
              potential mode pair.2)) +
        latticeFrequency mode pair.2 *
          (lorentzSign pair.1 *
            (Real.sqrt (symbolShiftedSourceWeight targetWeight mode) *
              potential mode pair.1))) =
    Real.sqrt (targetWeight mode) *
      (latticeFrequency mode pair.1 *
          (lorentzSign pair.2 * potential mode pair.2) +
        latticeFrequency mode pair.2 *
          (lorentzSign pair.1 * potential mode pair.1))
  rw [sqrt_symbolShiftedSourceWeight targetWeight mode]
  field_simp [hScale.ne']

theorem latticeLorentzGram_mem_targetWeightedL2
    (targetWeight : LatticeMode → Real)
    (potential : LatticePotential)
    (hPotential : PotentialInWeightedL2
      (symbolShiftedSourceWeight targetWeight) potential) :
    MetricInWeightedL2 targetWeight (latticeLorentzGram potential) := by
  rw [MetricInWeightedL2,
    ← normalizedLorentzGramFibers_encode_eq_weightedMetricCoordinates
      targetWeight potential hPotential]
  exact normalizedLorentzGramFibers_memℓp
    (encodeWeightedPotential
      (symbolShiftedSourceWeight targetWeight) potential hPotential)

theorem shiftedSobolevLorentzGram_encode_eq
    (targetWeight : LatticeMode → Real)
    (potential : LatticePotential)
    (hPotential : PotentialInWeightedL2
      (symbolShiftedSourceWeight targetWeight) potential) :
    shiftedSobolevLorentzGram targetWeight
        (encodeWeightedPotential
          (symbolShiftedSourceWeight targetWeight) potential hPotential) =
      encodeWeightedMetric targetWeight (latticeLorentzGram potential)
        (latticeLorentzGram_mem_targetWeightedL2 targetWeight potential
          hPotential) := by
  apply Subtype.ext
  exact normalizedLorentzGramFibers_encode_eq_weightedMetricCoordinates
    targetWeight potential hPotential

/-- The shifted coefficient model is a complete Hilbert-to-Hilbert bounded
realization of the order-one symbol. -/
theorem shifted_sobolev_lattice_lorentzGram_gate
    (targetWeight : LatticeMode → Real) :
    CompleteSpace (ShiftedPotentialHilbert targetWeight) ∧
    CompleteSpace (SobolevMetricHilbert targetWeight) ∧
    ‖shiftedSobolevLorentzGram targetWeight‖ ≤ 1 ∧
    (∀ (potential : LatticePotential)
      (hPotential : PotentialInWeightedL2
        (symbolShiftedSourceWeight targetWeight) potential),
      shiftedSobolevLorentzGram targetWeight
          (encodeWeightedPotential
            (symbolShiftedSourceWeight targetWeight) potential hPotential) =
        encodeWeightedMetric targetWeight (latticeLorentzGram potential)
          (latticeLorentzGram_mem_targetWeightedL2 targetWeight potential
            hPotential)) := by
  exact ⟨inferInstance, inferInstance,
    shiftedSobolevLorentzGram_opNorm_le targetWeight,
    shiftedSobolevLorentzGram_encode_eq targetWeight⟩

end

end P0EFTJanusShiftedSobolevLatticeLorentzGram
end JanusFormal
