import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusGlobalDiagonalRootFrontierControl4D

/-!
# Path dependence at a diagonal zero-over-zero face

Two positive diagonal paths reach the same simultaneous zero-over-zero
boundary point.  Along the equal-rate path the selected root eigenvalue stays
one; along the quadratic-numerator path it tends to zero.  Hence the positive
principal-root spectrum has no continuous single-valued extension at that
boundary point.  This rules out a branch atlas based on a path-independent
value there; it does not classify general matrix or Jordan paths.
-/

namespace JanusFormal
namespace P0EFTJanusGlobalDiagonalZeroOverZeroPathDependence4D

set_option autoImplicit false

noncomputable section

open Filter Set
open scoped Topology
open P0EFTJanusGlobalDiagonalLorentzRoot4D
open P0EFTJanusGlobalDiagonalRootFrontierControl4D

abbrev Coefficients4 :=
  P0EFTJanusGlobalDiagonalLorentzRoot4D.Coefficients4
abbrev CoefficientPair :=
  P0EFTJanusGlobalDiagonalLorentzRoot4D.CoefficientPair

/-- Both metric magnitudes vanish at the same linear rate in coordinate `i`.
-/
def equalRateZeroOverZeroPath
    (point : CoefficientPair) (i : Fin 4) (t : Real) : CoefficientPair :=
  (replaceMagnitude point.1 i t, replaceMagnitude point.2 i t)

/-- The numerator magnitude vanishes quadratically while the denominator
vanishes linearly in coordinate `i`. -/
def quadraticNumeratorZeroOverZeroPath
    (point : CoefficientPair) (i : Fin 4) (t : Real) : CoefficientPair :=
  (replaceMagnitude point.1 i t, replaceMagnitude point.2 i (t ^ 2))

@[simp] theorem zeroOverZero_paths_same_boundary
    (point : CoefficientPair) (i : Fin 4) :
    quadraticNumeratorZeroOverZeroPath point i 0 =
      equalRateZeroOverZeroPath point i 0 := by
  simp [quadraticNumeratorZeroOverZeroPath, equalRateZeroOverZeroPath]

theorem equalRateZeroOverZeroPath_mem_globalDomain
    {point : CoefficientPair} (hPoint : point ∈ globalDiagonalLorentzDomain)
    (i : Fin 4) {t : Real} (ht : 0 < t) :
    equalRateZeroOverZeroPath point i t ∈ globalDiagonalLorentzDomain := by
  constructor <;> intro j
  · by_cases hji : j = i
    · subst j
      simpa [equalRateZeroOverZeroPath, replaceMagnitude] using ht
    · simpa [equalRateZeroOverZeroPath, replaceMagnitude, hji] using hPoint.1 j
  · by_cases hji : j = i
    · subst j
      simpa [equalRateZeroOverZeroPath, replaceMagnitude] using ht
    · simpa [equalRateZeroOverZeroPath, replaceMagnitude, hji] using hPoint.2 j

theorem quadraticNumeratorZeroOverZeroPath_mem_globalDomain
    {point : CoefficientPair} (hPoint : point ∈ globalDiagonalLorentzDomain)
    (i : Fin 4) {t : Real} (ht : 0 < t) :
    quadraticNumeratorZeroOverZeroPath point i t ∈
      globalDiagonalLorentzDomain := by
  constructor <;> intro j
  · by_cases hji : j = i
    · subst j
      simpa [quadraticNumeratorZeroOverZeroPath, replaceMagnitude] using ht
    · simpa [quadraticNumeratorZeroOverZeroPath, replaceMagnitude, hji] using
        hPoint.1 j
  · by_cases hji : j = i
    · subst j
      simpa [quadraticNumeratorZeroOverZeroPath, replaceMagnitude] using
        (sq_pos_of_pos ht)
    · simpa [quadraticNumeratorZeroOverZeroPath, replaceMagnitude, hji] using
        hPoint.2 j

theorem equalRateZeroOverZeroPath_continuous
    (point : CoefficientPair) (i : Fin 4) :
    Continuous (equalRateZeroOverZeroPath point i) := by
  have hFirst := (plusCoordinateApproach_continuous point i).fst
  have hSecond := (minusCoordinateApproach_continuous point i).snd
  change Continuous (fun t =>
    (replaceMagnitude point.1 i t, replaceMagnitude point.2 i t))
  exact hFirst.prodMk hSecond

theorem quadraticNumeratorZeroOverZeroPath_continuous
    (point : CoefficientPair) (i : Fin 4) :
    Continuous (quadraticNumeratorZeroOverZeroPath point i) := by
  have hFirst := (plusCoordinateApproach_continuous point i).fst
  have hSecondLinear := (minusCoordinateApproach_continuous point i).snd
  have hSquare : Continuous (fun t : Real => t ^ 2) := continuous_id'.pow 2
  have hSecond := hSecondLinear.comp hSquare
  change Continuous (fun t =>
    (replaceMagnitude point.1 i t, replaceMagnitude point.2 i (t ^ 2)))
  exact hFirst.prodMk hSecond

theorem equalRateZeroOverZeroPath_tendsto_boundary
    (point : CoefficientPair) (i : Fin 4) :
    Tendsto (equalRateZeroOverZeroPath point i) (𝓝[>] (0 : Real))
      (𝓝 (equalRateZeroOverZeroPath point i 0)) :=
  (equalRateZeroOverZeroPath_continuous point i).continuousAt.tendsto.mono_left
    nhdsWithin_le_nhds

theorem quadraticNumeratorZeroOverZeroPath_tendsto_boundary
    (point : CoefficientPair) (i : Fin 4) :
    Tendsto (quadraticNumeratorZeroOverZeroPath point i) (𝓝[>] (0 : Real))
      (𝓝 (equalRateZeroOverZeroPath point i 0)) := by
  rw [← zeroOverZero_paths_same_boundary point i]
  exact
    (quadraticNumeratorZeroOverZeroPath_continuous point i).continuousAt.tendsto.mono_left
      nhdsWithin_le_nhds

theorem equalRateZeroOverZeroPath_root_eq_one
    (point : CoefficientPair) (i : Fin 4) {t : Real} (ht : 0 < t) :
    principalRootSpectrum (equalRateZeroOverZeroPath point i t) i = 1 := by
  rw [principalRootSpectrum, relativeRatio]
  simp [equalRateZeroOverZeroPath, replaceMagnitude, ht.ne']

theorem quadraticNumeratorZeroOverZeroPath_root_eq_sqrt
    (point : CoefficientPair) (i : Fin 4) {t : Real} (ht : 0 < t) :
    principalRootSpectrum
        (quadraticNumeratorZeroOverZeroPath point i t) i = Real.sqrt t := by
  rw [principalRootSpectrum, relativeRatio]
  have ht0 : t ≠ 0 := ht.ne'
  simp only [quadraticNumeratorZeroOverZeroPath, replaceMagnitude,
    Function.update_self]
  apply congrArg Real.sqrt
  field_simp [ht0]

theorem equalRateZeroOverZeroPath_root_tendsto_one
    (point : CoefficientPair) (i : Fin 4) :
    Tendsto
      (fun t => principalRootSpectrum (equalRateZeroOverZeroPath point i t) i)
      (𝓝[>] (0 : Real)) (𝓝 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (equalRateZeroOverZeroPath_root_eq_one point i ht).symm

theorem quadraticNumeratorZeroOverZeroPath_root_tendsto_zero
    (point : CoefficientPair) (i : Fin 4) :
    Tendsto
      (fun t => principalRootSpectrum
        (quadraticNumeratorZeroOverZeroPath point i t) i)
      (𝓝[>] (0 : Real)) (𝓝 0) := by
  have hSqrt : Tendsto (fun t : Real => Real.sqrt t) (𝓝[>] 0) (𝓝 0) := by
    have hAt : Tendsto (fun t : Real => Real.sqrt t) (𝓝 0)
        (𝓝 (Real.sqrt 0)) := Real.continuous_sqrt.continuousAt
    simpa using hAt.mono_left nhdsWithin_le_nhds
  apply hSqrt.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (quadraticNumeratorZeroOverZeroPath_root_eq_sqrt point i ht).symm

/-- The selected positive spectrum cannot be continuously and single-valuedly
extended to this simultaneous diagonal zero-over-zero boundary point. -/
theorem no_continuous_principalRootSpectrum_extension_at_zeroOverZero
    {point : CoefficientPair} (hPoint : point ∈ globalDiagonalLorentzDomain)
    (i : Fin 4) :
    ¬ ∃ extension : CoefficientPair → Coefficients4,
      ContinuousAt extension (equalRateZeroOverZeroPath point i 0) ∧
      ∀ interior, interior ∈ globalDiagonalLorentzDomain →
        extension interior = principalRootSpectrum interior := by
  rintro ⟨extension, hContinuous, hAgrees⟩
  let boundary := equalRateZeroOverZeroPath point i 0
  have hEqualPath : Tendsto
      (fun t => extension (equalRateZeroOverZeroPath point i t) i)
      (𝓝[>] (0 : Real)) (𝓝 (extension boundary i)) := by
    simpa only [boundary, Function.comp_def] using
      (continuous_apply i).continuousAt.tendsto.comp
        (hContinuous.tendsto.comp
          (equalRateZeroOverZeroPath_tendsto_boundary point i))
  have hEqualEventually :
      (fun t => extension (equalRateZeroOverZeroPath point i t) i) =ᶠ[𝓝[>] 0]
        fun _ => (1 : Real) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hAgrees _ (equalRateZeroOverZeroPath_mem_globalDomain hPoint i ht)]
    exact equalRateZeroOverZeroPath_root_eq_one point i ht
  have hEqualLimit : Tendsto
      (fun t => extension (equalRateZeroOverZeroPath point i t) i)
      (𝓝[>] (0 : Real)) (𝓝 1) :=
    tendsto_const_nhds.congr' hEqualEventually.symm
  have hBoundaryOne : extension boundary i = 1 :=
    tendsto_nhds_unique hEqualPath hEqualLimit
  have hQuadraticPath : Tendsto
      (fun t => extension (quadraticNumeratorZeroOverZeroPath point i t) i)
      (𝓝[>] (0 : Real)) (𝓝 (extension boundary i)) := by
    simpa only [boundary, Function.comp_def] using
      (continuous_apply i).continuousAt.tendsto.comp
        (hContinuous.tendsto.comp
          (quadraticNumeratorZeroOverZeroPath_tendsto_boundary point i))
  have hQuadraticEventually :
      (fun t => extension (quadraticNumeratorZeroOverZeroPath point i t) i) =ᶠ[𝓝[>] 0]
        (fun t => principalRootSpectrum
          (quadraticNumeratorZeroOverZeroPath point i t) i) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    rw [hAgrees _
      (quadraticNumeratorZeroOverZeroPath_mem_globalDomain hPoint i ht)]
  have hQuadraticLimit : Tendsto
      (fun t => extension (quadraticNumeratorZeroOverZeroPath point i t) i)
      (𝓝[>] (0 : Real)) (𝓝 0) :=
    (quadraticNumeratorZeroOverZeroPath_root_tendsto_zero point i).congr'
      hQuadraticEventually.symm
  have hBoundaryZero : extension boundary i = 0 :=
    tendsto_nhds_unique hQuadraticPath hQuadraticLimit
  exact zero_ne_one (hBoundaryZero.symm.trans hBoundaryOne)

end
end P0EFTJanusGlobalDiagonalZeroOverZeroPathDependence4D
end JanusFormal
