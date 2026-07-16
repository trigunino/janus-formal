import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalDiagonalLorentzCausalFrontier4D

/-!
# Approach to the spectral frontier of the global diagonal root

For the fixed-frame diagonal Lorentz sector, this gate separates the two
one-sided boundary behaviours of an eigenvalue ratio `bᵢ / aᵢ`.

* If the minus magnitude `bᵢ` tends to zero while `aᵢ > 0`, the principal
  root extends continuously and its `i`-th eigenvalue tends to zero.
* If the plus magnitude `aᵢ` tends to zero while `bᵢ > 0`, that ratio and its
  square root diverge to `+∞` along the explicit positive-coordinate path.
* At a zero root eigenvalue the Sylvester linearization has a concrete
  nonzero kernel vector.

Inside the positive component, pointwise uniqueness of positive diagonal
roots prevents any branch switch.  No claim is made for general Lorentz
matrices or for simultaneous zero-over-zero boundary points.
-/

namespace JanusFormal
namespace P0EFTJanusGlobalDiagonalRootFrontierControl4D

set_option autoImplicit false

noncomputable section

open Filter
open scoped Matrix.Norms.Frobenius RightActions Topology
open P0EFTJanusMatrixSquareRootFrechetSylvester
open P0EFTJanusCoDiagonalLorentzRootChart
open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusGlobalDiagonalLorentzCausalFrontier4D

abbrev Matrix4 := P0EFTJanusGlobalDiagonalLorentzRoot4D.Matrix4
abbrev Coefficients4 :=
  P0EFTJanusGlobalDiagonalLorentzRoot4D.Coefficients4
abbrev CoefficientPair :=
  P0EFTJanusGlobalDiagonalLorentzRoot4D.CoefficientPair

/-- The part of the closed spectral domain on which the denominator metric
remains nondegenerate while the numerator metric may reach zero faces. -/
def minusClosedDiagonalDomain : Set CoefficientPair :=
  positiveMagnitudeDomain ×ˢ nonnegativeMagnitudeDomain

theorem minusClosedDiagonalDomain_subset_closure :
    minusClosedDiagonalDomain ⊆ closure globalDiagonalLorentzDomain := by
  rw [closure_globalDiagonalLorentzDomain]
  rintro point ⟨hPlus, hMinus⟩
  exact ⟨fun i => (hPlus i).le, hMinus⟩

theorem relativeRatio_nonnegative_on_minusClosed
    {point : CoefficientPair} (hPoint : point ∈ minusClosedDiagonalDomain)
    (i : Fin 4) :
    0 ≤ relativeRatio point i :=
  div_nonneg (hPoint.2 i) (hPoint.1 i).le

/-- Exact classification of the finite one-sided faces: a principal-root
eigenvalue vanishes precisely when its numerator magnitude vanishes. -/
theorem principalRootSpectrum_eq_zero_iff_on_minusClosed
    {point : CoefficientPair} (hPoint : point ∈ minusClosedDiagonalDomain)
    (i : Fin 4) :
    principalRootSpectrum point i = 0 ↔ point.2 i = 0 := by
  unfold principalRootSpectrum
  rw [Real.sqrt_eq_zero (relativeRatio_nonnegative_on_minusClosed hPoint i)]
  simp [relativeRatio, ne_of_gt (hPoint.1 i)]

/-- The ratio map remains continuous up to every numerator-zero face as long
as the denominator magnitudes stay positive. -/
theorem relativeRatio_continuousOn_minusClosed :
    ContinuousOn relativeRatio minusClosedDiagonalDomain := by
  rw [continuousOn_pi]
  intro i point hPoint
  apply ContinuousAt.continuousWithinAt
  unfold relativeRatio
  fun_prop (disch := exact ne_of_gt (hPoint.1 i))

/-- The square-root spectrum has a continuous extension to all such finite
faces, although differentiability can fail where an eigenvalue reaches zero.
-/
theorem principalRootSpectrum_continuousOn_minusClosed :
    ContinuousOn principalRootSpectrum minusClosedDiagonalDomain := by
  rw [continuousOn_pi]
  intro i point hPoint
  apply ContinuousAt.continuousWithinAt
  unfold principalRootSpectrum relativeRatio
  fun_prop (disch := exact ne_of_gt (hPoint.1 i))

/-- Matrix-valued continuity of the principal diagonal root up to the finite
numerator-zero faces. -/
theorem principalRoot_continuousOn_minusClosed :
    ContinuousOn principalRoot minusClosedDiagonalDomain := by
  change ContinuousOn
    (fun point => diagonalContinuousLinearMap (principalRootSpectrum point))
    minusClosedDiagonalDomain
  exact diagonalContinuousLinearMap.continuous.comp_continuousOn
    principalRootSpectrum_continuousOn_minusClosed

/-- Replace one magnitude coordinate while leaving all others fixed. -/
def replaceMagnitude
    (coefficients : Coefficients4) (i : Fin 4) (value : ℝ) : Coefficients4 :=
  Function.update coefficients i value

/-- Approach a plus-metric zero face through positive values. -/
def plusCoordinateApproach
    (point : CoefficientPair) (i : Fin 4) (t : ℝ) : CoefficientPair :=
  (replaceMagnitude point.1 i t, point.2)

/-- Approach a minus-metric zero face through positive values. -/
def minusCoordinateApproach
    (point : CoefficientPair) (i : Fin 4) (t : ℝ) : CoefficientPair :=
  (point.1, replaceMagnitude point.2 i t)

theorem plusCoordinateApproach_mem_globalDomain
    {point : CoefficientPair} (hPoint : point ∈ globalDiagonalLorentzDomain)
    (i : Fin 4) {t : ℝ} (ht : 0 < t) :
    plusCoordinateApproach point i t ∈ globalDiagonalLorentzDomain := by
  refine ⟨?_, hPoint.2⟩
  intro j
  by_cases hji : j = i
  · subst j
    simpa [plusCoordinateApproach, replaceMagnitude] using ht
  · simpa [plusCoordinateApproach, replaceMagnitude, hji] using hPoint.1 j

theorem minusCoordinateApproach_mem_globalDomain
    {point : CoefficientPair} (hPoint : point ∈ globalDiagonalLorentzDomain)
    (i : Fin 4) {t : ℝ} (ht : 0 < t) :
    minusCoordinateApproach point i t ∈ globalDiagonalLorentzDomain := by
  refine ⟨hPoint.1, ?_⟩
  intro j
  by_cases hji : j = i
  · subst j
    simpa [minusCoordinateApproach, replaceMagnitude] using ht
  · simpa [minusCoordinateApproach, replaceMagnitude, hji] using hPoint.2 j

theorem plusCoordinateApproach_continuous
    (point : CoefficientPair) (i : Fin 4) :
    Continuous (plusCoordinateApproach point i) := by
  have hFirst : Continuous (fun t : ℝ => replaceMagnitude point.1 i t) := by
    apply continuous_pi
    intro j
    by_cases hji : j = i
    · subst j
      simpa [replaceMagnitude] using (continuous_id' : Continuous fun t : ℝ => t)
    · simpa [replaceMagnitude, hji] using
        (continuous_const : Continuous fun _ : ℝ => point.1 j)
  exact hFirst.prodMk continuous_const

theorem minusCoordinateApproach_continuous
    (point : CoefficientPair) (i : Fin 4) :
    Continuous (minusCoordinateApproach point i) := by
  have hSecond : Continuous (fun t : ℝ => replaceMagnitude point.2 i t) := by
    apply continuous_pi
    intro j
    by_cases hji : j = i
    · subst j
      simpa [replaceMagnitude] using (continuous_id' : Continuous fun t : ℝ => t)
    · simpa [replaceMagnitude, hji] using
        (continuous_const : Continuous fun _ : ℝ => point.2 j)
  exact continuous_const.prodMk hSecond

/-- Both explicit paths genuinely converge to their zero-coordinate boundary
points. -/
theorem plusCoordinateApproach_tendsto_boundary
    (point : CoefficientPair) (i : Fin 4) :
    Tendsto (plusCoordinateApproach point i) (𝓝[>] (0 : ℝ))
      (𝓝 (plusCoordinateApproach point i 0)) :=
  (plusCoordinateApproach_continuous point i).continuousAt.mono_left
    nhdsWithin_le_nhds

theorem minusCoordinateApproach_tendsto_boundary
    (point : CoefficientPair) (i : Fin 4) :
    Tendsto (minusCoordinateApproach point i) (𝓝[>] (0 : ℝ))
      (𝓝 (minusCoordinateApproach point i 0)) :=
  (minusCoordinateApproach_continuous point i).continuousAt.mono_left
    nhdsWithin_le_nhds

theorem plusCoordinateBoundary_mem_spectralBoundary
    {point : CoefficientPair} (hPoint : point ∈ globalDiagonalLorentzDomain)
    (i : Fin 4) :
    plusCoordinateApproach point i 0 ∈ globalDiagonalSpectralBoundary := by
  apply Or.inl
  constructor
  · constructor
    · intro j
      by_cases hji : j = i
      · subst j
        simp [plusCoordinateApproach, replaceMagnitude]
      · simpa [plusCoordinateApproach, replaceMagnitude, hji] using
          (hPoint.1 j).le
    · exact ⟨i, by simp [plusCoordinateApproach, replaceMagnitude]⟩
  · exact fun j => (hPoint.2 j).le

theorem minusCoordinateBoundary_mem_spectralBoundary
    {point : CoefficientPair} (hPoint : point ∈ globalDiagonalLorentzDomain)
    (i : Fin 4) :
    minusCoordinateApproach point i 0 ∈ globalDiagonalSpectralBoundary := by
  apply Or.inr
  constructor
  · exact fun j => (hPoint.1 j).le
  · constructor
    · intro j
      by_cases hji : j = i
      · subst j
        simp [minusCoordinateApproach, replaceMagnitude]
      · simpa [minusCoordinateApproach, replaceMagnitude, hji] using
          (hPoint.2 j).le
    · exact ⟨i, by simp [minusCoordinateApproach, replaceMagnitude]⟩

/-- If the numerator magnitude tends to zero with a fixed positive
denominator, the corresponding ratio tends to zero. -/
theorem minusCoordinateApproach_relativeRatio_tendsto_zero
    {point : CoefficientPair} (_hPoint : point ∈ globalDiagonalLorentzDomain)
    (i : Fin 4) :
    Tendsto
      (fun t => relativeRatio (minusCoordinateApproach point i t) i)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  have hLimit := (continuousAt_id.div_const (point.1 i)).tendsto.mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  simpa [relativeRatio, minusCoordinateApproach, replaceMagnitude] using hLimit

/-- Consequently the corresponding principal-root eigenvalue tends to zero.
-/
theorem minusCoordinateApproach_root_tendsto_zero
    {point : CoefficientPair} (hPoint : point ∈ globalDiagonalLorentzDomain)
    (i : Fin 4) :
    Tendsto
      (fun t => principalRootSpectrum (minusCoordinateApproach point i t) i)
      (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  change Tendsto
    ((fun x : ℝ => Real.sqrt x) ∘
      fun t => relativeRatio (minusCoordinateApproach point i t) i)
    (𝓝[>] (0 : ℝ)) (𝓝 0)
  simpa only [Real.sqrt_zero] using
    Real.continuous_sqrt.continuousAt.tendsto.comp
      (minusCoordinateApproach_relativeRatio_tendsto_zero hPoint i)

/-- If the denominator magnitude tends to zero with a fixed positive
numerator, the ratio diverges to `+∞`. -/
theorem plusCoordinateApproach_relativeRatio_tendsto_atTop
    {point : CoefficientPair} (hPoint : point ∈ globalDiagonalLorentzDomain)
    (i : Fin 4) :
    Tendsto
      (fun t => relativeRatio (plusCoordinateApproach point i t) i)
      (𝓝[>] (0 : ℝ)) atTop := by
  have hLimit := tendsto_inv_nhdsGT_zero.const_mul_atTop (hPoint.2 i)
  simpa [relativeRatio, plusCoordinateApproach, replaceMagnitude,
    div_eq_mul_inv] using hLimit

/-- The principal-root eigenvalue diverges with the ratio on that face. -/
theorem plusCoordinateApproach_root_tendsto_atTop
    {point : CoefficientPair} (hPoint : point ∈ globalDiagonalLorentzDomain)
    (i : Fin 4) :
    Tendsto
      (fun t => principalRootSpectrum (plusCoordinateApproach point i t) i)
      (𝓝[>] (0 : ℝ)) atTop := by
  change Tendsto
    ((fun x : ℝ => Real.sqrt x) ∘
      fun t => relativeRatio (plusCoordinateApproach point i t) i)
    (𝓝[>] (0 : ℝ)) atTop
  exact Real.tendsto_sqrt_atTop.comp
    (plusCoordinateApproach_relativeRatio_tendsto_atTop hPoint i)

/-- Concrete diagonal variation supported on a single spectral coordinate. -/
def spectralKernelVariation (i : Fin 4) : Matrix4 :=
  Matrix.single i i 1

theorem spectralKernelVariation_ne_zero (i : Fin 4) :
    spectralKernelVariation i ≠ 0 := by
  intro hZero
  have hEntry := congrArg (fun matrix : Matrix4 => matrix i i) hZero
  simp [spectralKernelVariation, Matrix.single] at hEntry

/-- A vanished root eigenvalue produces an explicit nonzero kernel vector for
the Sylvester linearization. -/
theorem sylvesterOperator_spectralKernelVariation_eq_zero
    {point : CoefficientPair} {i : Fin 4}
    (hRootZero : principalRootSpectrum point i = 0) :
    sylvesterOperator (principalRoot point) (spectralKernelVariation i) = 0 := by
  ext j k
  by_cases hji : j = i
  · subst j
    by_cases hki : k = i
    · subst k
      simp [sylvesterOperator_apply, principalRoot, spectralKernelVariation,
        Matrix.mul_apply, Matrix.single, hRootZero]
    · have hik : i ≠ k := Ne.symm hki
      simp [sylvesterOperator_apply, principalRoot, spectralKernelVariation,
        Matrix.mul_apply, Matrix.single, hik]
  · have hij : i ≠ j := Ne.symm hji
    by_cases hki : k = i
    · subst k
      simp [sylvesterOperator_apply, principalRoot, spectralKernelVariation,
        Matrix.mul_apply, Matrix.single, hji, hij]
    · have hik : i ≠ k := Ne.symm hki
      simp [sylvesterOperator_apply, principalRoot, spectralKernelVariation,
        Matrix.mul_apply, Matrix.single, hij, hik]

theorem sylvesterOperator_not_injective_at_zero_spectrum
    {point : CoefficientPair} {i : Fin 4}
    (hRootZero : principalRootSpectrum point i = 0) :
    ¬Function.Injective (sylvesterOperator (principalRoot point)) := by
  intro hInjective
  apply spectralKernelVariation_ne_zero i
  apply hInjective
  rw [sylvesterOperator_spectralKernelVariation_eq_zero hRootZero]
  exact (map_zero (sylvesterOperator (principalRoot point))).symm

/-- A zero numerator face therefore loses the Sylvester inverse used in the
interior derivative theorem. -/
theorem no_sylvesterInverseWitness_on_zero_numerator_face
    {point : CoefficientPair} (hPoint : point ∈ minusClosedDiagonalDomain)
    {i : Fin 4} (hMinusZero : point.2 i = 0) :
    ¬Nonempty (SylvesterInverseWitness (principalRoot point)) := by
  intro hWitness
  rcases hWitness with ⟨witness⟩
  apply sylvesterOperator_not_injective_at_zero_spectrum
    ((principalRootSpectrum_eq_zero_iff_on_minusClosed hPoint i).2 hMinusZero)
  intro first second hEqual
  calc
    first = witness.inverse (sylvesterOperator (principalRoot point) first) :=
      (witness.leftInverse first).symm
    _ = witness.inverse (sylvesterOperator (principalRoot point) second) := by
      rw [hEqual]
    _ = second := witness.leftInverse second

/-- No positive diagonal selector can change to another square-root branch
inside the connected positive domain: pointwise positive-branch uniqueness
identifies it globally with `principalRoot`. -/
theorem no_positive_diagonal_branch_switch
    {Parameter : Type*}
    (points : Parameter → CoefficientPair)
    (selectedRoot : Parameter → Matrix4)
    (hPoints : ∀ parameter,
      points parameter ∈ globalDiagonalLorentzDomain)
    (hPositive : ∀ parameter,
      IsPositiveDiagonalRoot (selectedRoot parameter))
    (hSquare : ∀ parameter,
      selectedRoot parameter * selectedRoot parameter =
        lorentzMetricInverse (points parameter).1 *
          lorentzMetric (points parameter).2) :
    selectedRoot = fun parameter => principalRoot (points parameter) := by
  funext parameter
  exact positiveDiagonalRoot_unique
    (hPositive parameter)
    (principalRoot_isPositiveDiagonal
      (points parameter) (hPoints parameter))
    (hSquare parameter)
    (principalRoot_square (points parameter) (hPoints parameter))

/-- Compact closure statement for facade and audit integration. -/
theorem global_diagonal_root_frontier_control_closure :
    ContinuousOn principalRoot minusClosedDiagonalDomain ∧
      (∀ point ∈ minusClosedDiagonalDomain, ∀ i,
        principalRootSpectrum point i = 0 ↔ point.2 i = 0) ∧
      (∀ point ∈ globalDiagonalLorentzDomain, ∀ i,
        Tendsto
          (fun t => principalRootSpectrum
            (minusCoordinateApproach point i t) i)
          (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
        Tendsto
          (fun t => principalRootSpectrum
            (plusCoordinateApproach point i t) i)
          (𝓝[>] (0 : ℝ)) atTop) ∧
      (∀ point ∈ minusClosedDiagonalDomain, ∀ i,
        point.2 i = 0 →
          ¬Nonempty (SylvesterInverseWitness (principalRoot point))) ∧
      (∀ point ∈ globalDiagonalLorentzDomain,
        ∃! root : Matrix4,
          IsPositiveDiagonalRoot root ∧
            root * root = lorentzMetricInverse point.1 *
              lorentzMetric point.2) := by
  refine ⟨principalRoot_continuousOn_minusClosed,
    fun point hPoint i =>
      principalRootSpectrum_eq_zero_iff_on_minusClosed hPoint i,
    ?_, ?_, ?_⟩
  · intro point hPoint i
    exact ⟨minusCoordinateApproach_root_tendsto_zero hPoint i,
      plusCoordinateApproach_root_tendsto_atTop hPoint i⟩
  · intro point hPoint i hZero
    exact no_sylvesterInverseWitness_on_zero_numerator_face
      hPoint hZero
  · intro point hPoint
    exact principalRoot_exists_unique point hPoint

end

end P0EFTJanusGlobalDiagonalRootFrontierControl4D
end JanusFormal
