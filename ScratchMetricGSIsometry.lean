import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusAmbientSmoothOrthonormalReduction4D

/-!
Static scratch package for the metric Gram--Schmidt change of frame.

No regularity claim is made here: the final application formula isolates the
only varying pieces which a later `ContMDiff` proof has to control.
-/

namespace JanusFormal
namespace ScratchMetricGSIsometry

set_option autoImplicit false

noncomputable section

open Set Finset Module
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusAmbientSmoothOrthonormalReduction4D

/-- Positive symmetric continuous bilinear form on the ambient coordinate
space. -/
structure PositiveCoverMetric where
  form : CoverCoordinates →L[Real] CoverCoordinates →L[Real] Real
  symmetric : ∀ first second, form first second = form second first
  positive : ∀ vector, vector ≠ 0 → 0 < form vector vector

/-- Raw metric Gram--Schmidt family, kept in the original normed structure. -/
def rawMetricGramSchmidtFamily
    (metric : PositiveCoverMetric)
    (seed : Basis (Fin 4) Real CoverCoordinates) (index : Fin 4) :
    CoverCoordinates :=
  metricGramSchmidt (fun _ : Real => metric.form) seed 0 index

/-- Purely algebraic triangular-span lemma.  No temporary inner-product or
normed-space instance is introduced. -/
theorem rawMetricGramSchmidtFamily_mem_span_Iic
    (metric : PositiveCoverMetric)
    (seed : Basis (Fin 4) Real CoverCoordinates) :
    ∀ {upper index : Fin 4}, index ≤ upper →
      rawMetricGramSchmidtFamily metric seed index ∈
        Submodule.span Real (seed '' Set.Iic upper) := by
  intro upper index hIndex
  change metricGramSchmidt (fun _ : Real => metric.form) seed 0 index ∈
    Submodule.span Real (seed '' Set.Iic upper)
  rw [metricGramSchmidt_def]
  refine Submodule.sub_mem _
    (Submodule.subset_span (Set.mem_image_of_mem seed hIndex))
    (Submodule.sum_mem _ fun lower hLower => ?_)
  let hLowerUpper : lower < upper :=
    (Finset.mem_Iio.1 hLower).trans_le hIndex
  exact Submodule.smul_mem _ _
    ((Submodule.span_mono
      (Set.image_mono (Set.Iic_subset_Iic.2 hLowerUpper.le)))
      (rawMetricGramSchmidtFamily_mem_span_Iic metric seed le_rfl))
termination_by upper => upper

/-- Nonvanishing of every raw pivot by triangularity and independence of the
seed.  This replaces the inner-product-instance proof. -/
theorem rawMetricGramSchmidtFamily_ne_zero
    (metric : PositiveCoverMetric)
    (seed : Basis (Fin 4) Real CoverCoordinates) (index : Fin 4) :
    rawMetricGramSchmidtFamily metric seed index ≠ 0 := by
  change metricGramSchmidt (fun _ : Real => metric.form) seed 0 index ≠ 0
  intro hZero
  rw [metricGramSchmidt_def] at hZero
  have hSeedEq : seed index =
      ∑ lower ∈ Finset.Iio index,
        (metric.form
            (metricGramSchmidt (fun _ : Real => metric.form) seed 0 lower)
            (seed index) /
          metric.form
            (metricGramSchmidt (fun _ : Real => metric.form) seed 0 lower)
            (metricGramSchmidt (fun _ : Real => metric.form) seed 0 lower)) •
          metricGramSchmidt (fun _ : Real => metric.form) seed 0 lower :=
    sub_eq_zero.mp hZero
  have hSeedMem : seed index ∈
      Submodule.span Real (seed '' Set.Iio index) := by
    rw [hSeedEq]
    exact Submodule.sum_mem _ fun lower hLower =>
      Submodule.smul_mem _ _
        ((Submodule.span_mono
          (Set.image_mono
            (Set.Iic_subset_Iio.2 (Finset.mem_Iio.1 hLower))))
          (rawMetricGramSchmidtFamily_mem_span_Iic metric seed le_rfl))
  exact (seed.linearIndependent.notMem_span_image
    (Set.self_notMem_Iio : index ∉ Set.Iio index)) hSeedMem

/-- Orthogonality by the recurrence itself and strong induction.  Positivity
is used only to cancel the nonzero pivot square. -/
theorem rawMetricGramSchmidtFamily_orthogonal
    (metric : PositiveCoverMetric)
    (seed : Basis (Fin 4) Real CoverCoordinates)
    {first second : Fin 4} (hIndices : first ≠ second) :
    metric.form (rawMetricGramSchmidtFamily metric seed first)
        (rawMetricGramSchmidtFamily metric seed second) = 0 := by
  suffices hOrdered : ∀ first second : Fin 4, first < second →
      metric.form (rawMetricGramSchmidtFamily metric seed first)
        (rawMetricGramSchmidtFamily metric seed second) = 0 by
    rcases hIndices.lt_or_gt with hFirst | hSecond
    · exact hOrdered first second hFirst
    · rw [metric.symmetric]
      exact hOrdered second first hSecond
  clear hIndices first second
  intro first second hFirstSecond
  revert first
  apply wellFounded_lt.induction second
  intro second ih first hFirstSecond
  change metric.form
      (rawMetricGramSchmidtFamily metric seed first)
      (metricGramSchmidt (fun _ : Real => metric.form) seed 0 second) = 0
  rw [metricGramSchmidt_def]
  simp only [map_sub, map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single_of_mem first
    (Finset.mem_Iio.mpr hFirstSecond)]
  · have hPivotNe : metric.form
        (rawMetricGramSchmidtFamily metric seed first)
        (rawMetricGramSchmidtFamily metric seed first) ≠ 0 :=
      ne_of_gt (metric.positive _
        (rawMetricGramSchmidtFamily_ne_zero metric seed first))
    rw [div_mul_cancel₀ _ hPivotNe, sub_self]
  · intro other hOther hOtherFirst
    apply mul_eq_zero_of_right
    rcases hOtherFirst.lt_or_gt with hOtherLt | hFirstLt
    · rw [metric.symmetric]
      exact ih first hFirstSecond other hOtherLt
    · exact ih other (Finset.mem_Iio.1 hOther) first hFirstLt

/-- The same seed basis normalized by metric Gram--Schmidt for one positive
form. -/
def normalizedMetricFamily
    (metric : PositiveCoverMetric)
    (seed : Basis (Fin 4) Real CoverCoordinates) (index : Fin 4) :
    CoverCoordinates :=
  metricGramSchmidtNormed (fun _ : Real => metric.form) seed 0 index

theorem normalizedMetricFamily_gram
    (metric : PositiveCoverMetric)
    (seed : Basis (Fin 4) Real CoverCoordinates)
    (first second : Fin 4) :
    metric.form (normalizedMetricFamily metric seed first)
        (normalizedMetricFamily metric seed second) =
      if first = second then 1 else 0 := by
  by_cases hIndices : first = second
  · subst second
    rw [if_pos rfl]
    change metric.form
        ((Real.sqrt (metric.form
          (rawMetricGramSchmidtFamily metric seed first)
          (rawMetricGramSchmidtFamily metric seed first)))⁻¹ •
            rawMetricGramSchmidtFamily metric seed first)
        ((Real.sqrt (metric.form
          (rawMetricGramSchmidtFamily metric seed first)
          (rawMetricGramSchmidtFamily metric seed first)))⁻¹ •
            rawMetricGramSchmidtFamily metric seed first) = 1
    simp only [map_smul, smul_apply, smul_eq_mul]
    have hPivotPos : 0 < metric.form
        (rawMetricGramSchmidtFamily metric seed first)
        (rawMetricGramSchmidtFamily metric seed first) :=
      metric.positive _
        (rawMetricGramSchmidtFamily_ne_zero metric seed first)
    have hSqrtNe : Real.sqrt (metric.form
        (rawMetricGramSchmidtFamily metric seed first)
        (rawMetricGramSchmidtFamily metric seed first)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hPivotPos)
    rw [← Real.sq_sqrt hPivotPos.le]
    field_simp
  · rw [if_neg hIndices]
    change metric.form
        ((Real.sqrt (metric.form
          (rawMetricGramSchmidtFamily metric seed first)
          (rawMetricGramSchmidtFamily metric seed first)))⁻¹ •
            rawMetricGramSchmidtFamily metric seed first)
        ((Real.sqrt (metric.form
          (rawMetricGramSchmidtFamily metric seed second)
          (rawMetricGramSchmidtFamily metric seed second)))⁻¹ •
            rawMetricGramSchmidtFamily metric seed second) = 0
    simp only [map_smul, smul_apply, smul_eq_mul,
      rawMetricGramSchmidtFamily_orthogonal metric seed hIndices, mul_zero]

theorem normalizedMetricFamily_linearIndependent
    (metric : PositiveCoverMetric)
    (seed : Basis (Fin 4) Real CoverCoordinates) :
    LinearIndependent Real (normalizedMetricFamily metric seed) := by
  apply Fintype.linearIndependent_iff.mpr
  intro coefficients hCombination index
  have hEvaluated := congrArg
    (fun vector => metric.form
      (normalizedMetricFamily metric seed index) vector)
    hCombination
  simp only [map_sum, map_smul, map_zero, smul_eq_mul] at hEvaluated
  rw [Finset.sum_eq_single index] at hEvaluated
  · rw [normalizedMetricFamily_gram metric seed index index,
      if_pos rfl, mul_one] at hEvaluated
    exact hEvaluated
  · intro other _ hOther
    rw [normalizedMetricFamily_gram metric seed index other,
      if_neg hOther.symm, mul_zero]
  · exact fun hMissing => (hMissing (Finset.mem_univ index)).elim

/-- Basis supplied by the normalized family. -/
def normalizedMetricBasis
    (metric : PositiveCoverMetric)
    (seed : Basis (Fin 4) Real CoverCoordinates) :
    Basis (Fin 4) Real CoverCoordinates :=
  basisOfLinearIndependentOfCardEqFinrank
    (normalizedMetricFamily_linearIndependent metric seed)
    (by norm_num [CoverCoordinates])

@[simp] theorem normalizedMetricBasis_apply
    (metric : PositiveCoverMetric)
    (seed : Basis (Fin 4) Real CoverCoordinates) (index : Fin 4) :
    normalizedMetricBasis metric seed index =
      normalizedMetricFamily metric seed index := by
  simp [normalizedMetricBasis]

/-- Change of basis from the source metric normalization to the target metric
normalization of the same seed basis. -/
def normalizedMetricLinearEquiv
    (source target : PositiveCoverMetric)
    (seed : Basis (Fin 4) Real CoverCoordinates) :
    CoverCoordinates ≃ₗ[Real] CoverCoordinates :=
  (normalizedMetricBasis source seed).equiv
    (normalizedMetricBasis target seed) (Equiv.refl (Fin 4))

@[simp] theorem normalizedMetricLinearEquiv_basis
    (source target : PositiveCoverMetric)
    (seed : Basis (Fin 4) Real CoverCoordinates) (index : Fin 4) :
    normalizedMetricLinearEquiv source target seed
        (normalizedMetricFamily source seed index) =
      normalizedMetricFamily target seed index := by
  rw [← normalizedMetricBasis_apply source seed index,
    ← normalizedMetricBasis_apply target seed index]
  exact Basis.equiv_apply _ _ _ _

/-- Application formula exposing the source coordinates and target normalized
vectors separately.  This is the useful normal form for later regularity
proofs. -/
theorem normalizedMetricLinearEquiv_apply
    (source target : PositiveCoverMetric)
    (seed : Basis (Fin 4) Real CoverCoordinates)
    (vector : CoverCoordinates) :
    normalizedMetricLinearEquiv source target seed vector =
      ∑ index : Fin 4,
        ((normalizedMetricBasis source seed).repr vector index) •
          normalizedMetricFamily target seed index := by
  calc
    normalizedMetricLinearEquiv source target seed vector =
        normalizedMetricLinearEquiv source target seed
          (∑ index : Fin 4,
            ((normalizedMetricBasis source seed).repr vector index) •
              normalizedMetricBasis source seed index) :=
      congrArg
        (fun value => normalizedMetricLinearEquiv source target seed value)
        ((normalizedMetricBasis source seed).sum_repr vector).symm
    _ = ∑ index : Fin 4,
          ((normalizedMetricBasis source seed).repr vector index) •
            normalizedMetricLinearEquiv source target seed
              (normalizedMetricBasis source seed index) := by
      simp only [map_sum, map_smul]
    _ = ∑ index : Fin 4,
          ((normalizedMetricBasis source seed).repr vector index) •
            normalizedMetricFamily target seed index := by
      simp only [normalizedMetricBasis_apply,
        normalizedMetricLinearEquiv_basis]

theorem normalizedMetricLinearEquiv_bilinear_isometry
    (source target : PositiveCoverMetric)
    (seed : Basis (Fin 4) Real CoverCoordinates) :
    target.form.toBilinForm.compl₁₂
        (normalizedMetricLinearEquiv source target seed).toLinearMap
        (normalizedMetricLinearEquiv source target seed).toLinearMap =
      source.form.toBilinForm := by
  apply (LinearMap.BilinForm.ext_iff_basis
    (normalizedMetricBasis source seed)).2
  intro first second
  simp only [LinearMap.compl₁₂_apply, LinearEquiv.coe_coe,
    normalizedMetricBasis_apply, normalizedMetricLinearEquiv_basis]
  rw [normalizedMetricFamily_gram target seed first second,
    normalizedMetricFamily_gram source seed first second]

/-- Quadratic form induced by a positive cover metric. -/
def positiveMetricQuadraticForm
    (metric : PositiveCoverMetric) : QuadraticForm Real CoverCoordinates :=
  metric.form.toBilinForm.toQuadraticMap

@[simp] theorem positiveMetricQuadraticForm_apply
    (metric : PositiveCoverMetric) (vector : CoverCoordinates) :
    positiveMetricQuadraticForm metric vector = metric.form vector vector := by
  rfl

/-- Exact quadratic isometry between the two Gram--Schmidt frames built from
the same seed basis. -/
def normalizedMetricIsometryEquiv
    (source target : PositiveCoverMetric)
    (seed : Basis (Fin 4) Real CoverCoordinates) :
    (positiveMetricQuadraticForm source).IsometryEquiv
      (positiveMetricQuadraticForm target) where
  __ := normalizedMetricLinearEquiv source target seed
  map_app' vector := by
    change target.form
        (normalizedMetricLinearEquiv source target seed vector)
        (normalizedMetricLinearEquiv source target seed vector) =
      source.form vector vector
    exact congrArg
      (fun form : LinearMap.BilinForm Real CoverCoordinates =>
        form vector vector)
      (normalizedMetricLinearEquiv_bilinear_isometry source target seed)

@[simp] theorem normalizedMetricIsometryEquiv_basis
    (source target : PositiveCoverMetric)
    (seed : Basis (Fin 4) Real CoverCoordinates) (index : Fin 4) :
    normalizedMetricIsometryEquiv source target seed
        (normalizedMetricFamily source seed index) =
      normalizedMetricFamily target seed index := by
  exact normalizedMetricLinearEquiv_basis source target seed index

/-- Coercion of the quadratic isometry has the finite-sum application formula
needed to prove smoothness once the source coordinates and target frame are
known smooth. -/
theorem normalizedMetricIsometryEquiv_apply
    (source target : PositiveCoverMetric)
    (seed : Basis (Fin 4) Real CoverCoordinates)
    (vector : CoverCoordinates) :
    normalizedMetricIsometryEquiv source target seed vector =
      ∑ index : Fin 4,
        ((normalizedMetricBasis source seed).repr vector index) •
          normalizedMetricFamily target seed index := by
  exact normalizedMetricLinearEquiv_apply source target seed vector

end

end ScratchMetricGSIsometry
end JanusFormal
