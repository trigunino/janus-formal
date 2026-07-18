import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.WhitneyEmbedding
import Mathlib.LinearAlgebra.Basis.Bilinear
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusAmbientPointwiseOrthonormalReduction4D
import JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation.Gates.P0EFTJanusMappingTorusCompactQuotient

/-!
# Smooth ambient orthonormal reduction

This gate is independent of the discontinuous reference-lift reduction.  It
first proves a set-local Gram--Schmidt theorem for a smoothly varying positive
bilinear form.  The geometric construction uses a Whitney embedding of the
compact quotient and pulls the Euclidean metric back in each genuine quotient
chart.  Thus odd overlaps remain genuine orientation-reversing `O(4)`
transitions; no global tangent trivialization is introduced.
-/

namespace JanusFormal
namespace P0EFTJanusMappingTorusAmbientSmoothOrthonormalReduction4D

set_option autoImplicit false

noncomputable section

open Set Finset Module Bundle
open scoped Manifold ContDiff InnerProductSpace

attribute [local instance] IsWellOrder.toHasWellFounded

/-! ## Gram--Schmidt for a varying positive form -/

universe u v

variable {Base : Type u} {V : Type v}
variable [NormedAddCommGroup V] [NormedSpace Real V]

/-- Unnormalised Gram--Schmidt for a bilinear form which may vary with the
base point.  The definition is total; positivity is required only on the set
where algebraic and regularity conclusions are used. -/
def metricGramSchmidt
    {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    [WellFoundedLT ι]
    (metric : Base → V →L[Real] V →L[Real] Real)
    (family : ι → V) (x : Base) (n : ι) : V :=
  family n - ∑ i : Finset.Iio n,
    (metric x (metricGramSchmidt metric family x i) (family n) /
        metric x (metricGramSchmidt metric family x i)
          (metricGramSchmidt metric family x i)) •
      metricGramSchmidt metric family x i
termination_by n
decreasing_by exact Finset.mem_Iio.mp i.2

/-- Finset recurrence for the varying-metric Gram--Schmidt family. -/
theorem metricGramSchmidt_def
    {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    [WellFoundedLT ι]
    (metric : Base → V →L[Real] V →L[Real] Real)
    (family : ι → V) (x : Base) (n : ι) :
    metricGramSchmidt metric family x n =
      family n - ∑ i ∈ Finset.Iio n,
        (metric x (metricGramSchmidt metric family x i) (family n) /
            metric x (metricGramSchmidt metric family x i)
              (metricGramSchmidt metric family x i)) •
          metricGramSchmidt metric family x i := by
  rw [← sum_attach, attach_eq_univ, metricGramSchmidt]

/-- Normalisation by the strictly positive metric square length. -/
def metricGramSchmidtNormed
    {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    [WellFoundedLT ι]
    (metric : Base → V →L[Real] V →L[Real] Real)
    (family : ι → V) (x : Base) (n : ι) : V :=
  (Real.sqrt
      (metric x (metricGramSchmidt metric family x n)
        (metricGramSchmidt metric family x n)))⁻¹ •
    metricGramSchmidt metric family x n

private theorem metricGramSchmidt_mem_span_Iic
    {ι : Type*} [LinearOrder ι] [LocallyFiniteOrderBot ι]
    [WellFoundedLT ι]
    (metric : Base → V →L[Real] V →L[Real] Real)
    (family : ι → V) (x : Base) :
    ∀ {j i}, i ≤ j →
      metricGramSchmidt metric family x i ∈
        Submodule.span Real (family '' Set.Iic j) := by
  intro j i hij
  rw [metricGramSchmidt_def]
  refine Submodule.sub_mem _ (Submodule.subset_span (Set.mem_image_of_mem _ hij))
    (Submodule.sum_mem _ fun k hk => ?_)
  let hkj : k < j := (Finset.mem_Iio.1 hk).trans_le hij
  exact Submodule.smul_mem _ _
    (Submodule.span_mono (Set.image_mono <| Set.Iic_subset_Iic.2 hkj.le) <|
      metricGramSchmidt_mem_span_Iic metric family x le_rfl)
termination_by j => j

/-- Every Gram--Schmidt pivot is nonzero on the positive locus. -/
theorem metricGramSchmidt_ne_zero
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    (metric : Base → V →L[Real] V →L[Real] Real)
    (family : ι → V) (hIndependent : LinearIndependent Real family)
    (u : Set Base)
    (hSymm : ∀ x ∈ u, ∀ first second,
      metric x first second = metric x second first)
    (hPos : ∀ x ∈ u, ∀ vector, vector ≠ 0 →
      0 < metric x vector vector)
    (x : Base) (hx : x ∈ u) (n : ι) :
    metricGramSchmidt metric family x n ≠ 0 := by
  by_contra hZero
  rw [metricGramSchmidt_def] at hZero
  have hFamily : family n = ∑ k ∈ Finset.Iio n,
      (metric x (metricGramSchmidt metric family x k) (family n) /
          metric x (metricGramSchmidt metric family x k)
            (metricGramSchmidt metric family x k)) •
        metricGramSchmidt metric family x k :=
    sub_eq_zero.mp hZero
  have hSpan : family n ∈ Submodule.span Real (family '' Set.Iio n) := by
    rw [hFamily]
    exact Submodule.sum_mem _ fun k hk => Submodule.smul_mem _ _ <|
      Submodule.span_mono
        (Set.image_mono <| Set.Iic_subset_Iio.2 (Finset.mem_Iio.1 hk)) <|
          metricGramSchmidt_mem_span_Iic metric family x le_rfl
  exact (hIndependent.notMem_span_image Set.self_notMem_Iio) hSpan

/-- The metric square length of every unnormalised pivot is strictly
positive on the positive locus. -/
theorem metricGramSchmidt_self_pos
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    (metric : Base → V →L[Real] V →L[Real] Real)
    (family : ι → V) (hIndependent : LinearIndependent Real family)
    (u : Set Base)
    (hSymm : ∀ x ∈ u, ∀ first second,
      metric x first second = metric x second first)
    (hPos : ∀ x ∈ u, ∀ vector, vector ≠ 0 →
      0 < metric x vector vector)
    (x : Base) (hx : x ∈ u) (n : ι) :
    0 < metric x (metricGramSchmidt metric family x n)
      (metricGramSchmidt metric family x n) :=
  hPos x hx _
    (metricGramSchmidt_ne_zero metric family hIndependent u
      hSymm hPos x hx n)

private theorem metricGramSchmidt_orthogonal
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    (metric : Base → V →L[Real] V →L[Real] Real)
    (family : ι → V) (hIndependent : LinearIndependent Real family)
    (u : Set Base)
    (hSymm : ∀ x ∈ u, ∀ first second,
      metric x first second = metric x second first)
    (hPos : ∀ x ∈ u, ∀ vector, vector ≠ 0 →
      0 < metric x vector vector)
    (x : Base) (hx : x ∈ u) {first second : ι}
    (hIndices : first ≠ second) :
    metric x (metricGramSchmidt metric family x first)
        (metricGramSchmidt metric family x second) = 0 := by
  suffices ∀ first second : ι, first < second →
      metric x (metricGramSchmidt metric family x first)
        (metricGramSchmidt metric family x second) = 0 by
    rcases hIndices.lt_or_gt with hFirst | hSecond
    · exact this first second hFirst
    · rw [hSymm x hx]
      exact this second first hSecond
  clear hIndices first second
  intro first second hFirst
  revert first
  apply wellFounded_lt.induction second
  intro second ih first hFirst
  rw [metricGramSchmidt_def metric family x second]
  simp only [map_sub, map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_eq_single_of_mem first (Finset.mem_Iio.mpr hFirst)]
  · have hPivot : metric x (metricGramSchmidt metric family x first)
        (metricGramSchmidt metric family x first) ≠ 0 :=
      ne_of_gt (metricGramSchmidt_self_pos metric family hIndependent u
        hSymm hPos x hx first)
    rw [div_mul_cancel₀ _ hPivot, sub_self]
  intro index hIndex hNe
  simp only [mul_eq_zero, div_eq_zero_iff]
  right
  rcases hNe.lt_or_gt with hBefore | hAfter
  · rw [hSymm x hx]
    exact ih first hFirst index hBefore
  · exact ih index (Finset.mem_Iio.1 hIndex) first hAfter

/-- The metric Gram matrix of the normalized family is the identity. -/
theorem metricGramSchmidtNormed_gram
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    (metric : Base → V →L[Real] V →L[Real] Real)
    (family : ι → V) (hIndependent : LinearIndependent Real family)
    (u : Set Base)
    (hSymm : ∀ x ∈ u, ∀ first second,
      metric x first second = metric x second first)
    (hPos : ∀ x ∈ u, ∀ vector, vector ≠ 0 →
      0 < metric x vector vector)
    (x : Base) (hx : x ∈ u) (first second : ι) :
    metric x (metricGramSchmidtNormed metric family x first)
        (metricGramSchmidtNormed metric family x second) =
      if first = second then 1 else 0 := by
  by_cases hIndices : first = second
  · subst second
    rw [if_pos rfl]
    have hSelf := metricGramSchmidt_self_pos metric family hIndependent u
      hSymm hPos x hx first
    have hSqrt : Real.sqrt
        (metric x (metricGramSchmidt metric family x first)
          (metricGramSchmidt metric family x first)) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr hSelf
    simp only [metricGramSchmidtNormed, map_smul, smul_apply, smul_eq_mul]
    field_simp
    nlinarith [Real.sq_sqrt hSelf.le]
  · rw [if_neg hIndices]
    simp only [metricGramSchmidtNormed, map_smul, smul_apply, smul_eq_mul,
      metricGramSchmidt_orthogonal metric family hIndependent u hSymm hPos
        x hx hIndices, mul_zero]

/-- Normalized varying Gram--Schmidt preserves linear independence on the
positive locus. -/
theorem metricGramSchmidtNormed_linearIndependent
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    (metric : Base → V →L[Real] V →L[Real] Real)
    (family : ι → V) (hIndependent : LinearIndependent Real family)
    (u : Set Base)
    (hSymm : ∀ x ∈ u, ∀ first second,
      metric x first second = metric x second first)
    (hPos : ∀ x ∈ u, ∀ vector, vector ≠ 0 →
      0 < metric x vector vector)
    (x : Base) (hx : x ∈ u) :
    LinearIndependent Real (metricGramSchmidtNormed metric family x) := by
  apply LinearMap.BilinForm.linearIndependent_of_iIsOrtho
      (B := (metric x).toBilinForm)
  · rw [LinearMap.BilinForm.iIsOrtho_def]
    intro first second hIndices
    simpa [hIndices] using metricGramSchmidtNormed_gram metric family
      hIndependent u hSymm hPos x hx first second
  · intro index
    rw [LinearMap.BilinForm.isOrtho_def]
    intro hZero
    change metric x (metricGramSchmidtNormed metric family x index)
      (metricGramSchmidtNormed metric family x index) = 0 at hZero
    have hUnit := metricGramSchmidtNormed_gram metric family hIndependent u
      hSymm hPos x hx index index
    rw [if_pos rfl] at hUnit
    linarith

/-! The same regularity argument over an arbitrary manifold base.  Its
hypothesis is deliberately the joint smoothness of metric evaluation, which
is exactly what local pullback metrics provide. -/

section ManifoldGramSchmidt

universe w

variable {E₀ H₀ M : Type w}
variable [NormedAddCommGroup E₀] [NormedSpace Real E₀]
variable [TopologicalSpace H₀] (I : ModelWithCorners Real E₀ H₀)
variable [TopologicalSpace M] [ChartedSpace H₀ M]

theorem metricGramSchmidt_contMDiffOn_of_apply
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    (metric : M → V →L[Real] V →L[Real] Real)
    (family : ι → V) (hIndependent : LinearIndependent Real family)
    (u : Set M)
    (hMetricApply : ∀ first second : M → V,
      ContMDiffOn I 𝓘(Real, V) ∞ first u →
      ContMDiffOn I 𝓘(Real, V) ∞ second u →
      ContMDiffOn I 𝓘(Real) ∞
        (fun x => metric x (first x) (second x)) u)
    (hSymm : ∀ x ∈ u, ∀ first second,
      metric x first second = metric x second first)
    (hPos : ∀ x ∈ u, ∀ vector, vector ≠ 0 →
      0 < metric x vector vector) :
    ∀ n, ContMDiffOn I 𝓘(Real, V) ∞
      (metricGramSchmidt metric family · n) u := by
  intro n
  apply wellFounded_lt.induction n
  intro n ih
  rw [show (metricGramSchmidt metric family · n) =
      fun x => family n - ∑ i ∈ Finset.Iio n,
        (metric x (metricGramSchmidt metric family x i) (family n) /
            metric x (metricGramSchmidt metric family x i)
              (metricGramSchmidt metric family x i)) •
          metricGramSchmidt metric family x i by
    funext x
    exact metricGramSchmidt_def metric family x n]
  apply contMDiffOn_const.sub
  apply contMDiffOn_finsetSum
  intro i hi
  have hi_lt : i < n := Finset.mem_Iio.mp hi
  have hPivot := ih i hi_lt
  have hNumerator := hMetricApply
    (metricGramSchmidt metric family · i) (fun _ => family n)
    hPivot contMDiffOn_const
  have hDenominator := hMetricApply
    (metricGramSchmidt metric family · i)
    (metricGramSchmidt metric family · i) hPivot hPivot
  have hDenominator_ne : ∀ x ∈ u,
      metric x (metricGramSchmidt metric family x i)
        (metricGramSchmidt metric family x i) ≠ 0 := by
    intro x hx
    exact ne_of_gt
      (metricGramSchmidt_self_pos metric family hIndependent u
        hSymm hPos x hx i)
  exact (hNumerator.div₀ hDenominator hDenominator_ne).smul hPivot

theorem metricGramSchmidtNormed_contMDiffOn_of_apply
    {ι : Type*} [Fintype ι] [LinearOrder ι]
    [LocallyFiniteOrderBot ι] [WellFoundedLT ι]
    (metric : M → V →L[Real] V →L[Real] Real)
    (family : ι → V) (hIndependent : LinearIndependent Real family)
    (u : Set M)
    (hMetricApply : ∀ first second : M → V,
      ContMDiffOn I 𝓘(Real, V) ∞ first u →
      ContMDiffOn I 𝓘(Real, V) ∞ second u →
      ContMDiffOn I 𝓘(Real) ∞
        (fun x => metric x (first x) (second x)) u)
    (hSymm : ∀ x ∈ u, ∀ first second,
      metric x first second = metric x second first)
    (hPos : ∀ x ∈ u, ∀ vector, vector ≠ 0 →
      0 < metric x vector vector) :
    ∀ n, ContMDiffOn I 𝓘(Real, V) ∞
      (metricGramSchmidtNormed metric family · n) u := by
  intro n
  have hPivot := metricGramSchmidt_contMDiffOn_of_apply I metric family
    hIndependent u hMetricApply hSymm hPos n
  have hSelf := hMetricApply
    (metricGramSchmidt metric family · n)
    (metricGramSchmidt metric family · n) hPivot hPivot
  have hSelf_ne : ∀ x ∈ u,
      metric x (metricGramSchmidt metric family x n)
        (metricGramSchmidt metric family x n) ≠ 0 := by
    intro x hx
    exact ne_of_gt
      (metricGramSchmidt_self_pos metric family hIndependent u
        hSymm hPos x hx n)
  have hSqrt : ContMDiffOn I 𝓘(Real) ∞
      (fun x => Real.sqrt
        (metric x (metricGramSchmidt metric family x n)
          (metricGramSchmidt metric family x n))) u := by
    intro x hx
    simpa only [Function.comp_def] using
      ((Real.contDiffAt_sqrt (hSelf_ne x hx)).contMDiffAt).comp_contMDiffWithinAt
        x (hSelf x hx)
  have hSqrt_ne : ∀ x ∈ u,
      Real.sqrt (metric x (metricGramSchmidt metric family x n)
        (metricGramSchmidt metric family x n)) ≠ 0 := by
    intro x hx
    exact Real.sqrt_ne_zero'.mpr
      (metricGramSchmidt_self_pos metric family hIndependent u
        hSymm hPos x hx n)
  change ContMDiffOn I 𝓘(Real, V) ∞
    (fun x => (Real.sqrt
      (metric x (metricGramSchmidt metric family x n)
        (metricGramSchmidt metric family x n)))⁻¹ •
      metricGramSchmidt metric family x n) u
  exact (hSqrt.inv₀ hSqrt_ne).smul hPivot

end ManifoldGramSchmidt

/-! ## Whitney data for the compact D8 quotient -/

open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotient
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusAmbientTangentOrientationCocycle
open P0EFTJanusMappingTorusAmbientTangentQuadraticReduction
open P0EFTJanusMappingTorusAmbientPointwiseOrthonormalReduction4D

attribute [local instance 2000] chartedSpaceSelf

variable (period : Real) (hPeriod : period ≠ 0)

private abbrev AmbientData := reflectedSphereData period hPeriod
private abbrev AmbientCover := MappingTorusCover (AmbientData period hPeriod)
private abbrev AmbientBase := MappingTorus (AmbientData period hPeriod)

private local instance ambientCoverChartedSpace :
    ChartedSpace CoverModel (AmbientCover period hPeriod) :=
  reflectedSphereCoverChartedSpace period hPeriod

private local instance ambientCoverIsManifold :
    IsManifold coverModelWithCorners ω (AmbientCover period hPeriod) :=
  reflectedSphereCover_isManifold period hPeriod

private local instance ambientBaseChartedSpace :
    ChartedSpace CoverModel (AmbientBase period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod

private local instance ambientBaseIsManifold :
    IsManifold coverModelWithCorners ω (AmbientBase period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod

private local instance ambientBaseCompactSpace :
    CompactSpace (AmbientBase period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod

private theorem existsWhitneyEmbedding :
    ∃ (dimension : Nat)
      (embedding : AmbientBase period hPeriod →
        EuclideanSpace Real (Fin dimension)),
      ContMDiff coverModelWithCorners
          𝓘(Real, EuclideanSpace Real (Fin dimension)) ∞ embedding ∧
        Topology.IsClosedEmbedding embedding ∧
        ∀ point, Function.Injective
          (mfderiv coverModelWithCorners
            𝓘(Real, EuclideanSpace Real (Fin dimension)) embedding point) := by
  exact exists_embedding_euclidean_of_compact
    (I := coverModelWithCorners)

private def whitneyDimension : Nat :=
  (existsWhitneyEmbedding period hPeriod).choose

private def whitneyEmbedding : AmbientBase period hPeriod →
    EuclideanSpace Real (Fin (whitneyDimension period hPeriod)) :=
  (existsWhitneyEmbedding period hPeriod).choose_spec.choose

private theorem whitneyEmbedding_contMDiff :
    ContMDiff coverModelWithCorners
      𝓘(Real, EuclideanSpace Real (Fin (whitneyDimension period hPeriod))) ∞
      (whitneyEmbedding period hPeriod) :=
  (existsWhitneyEmbedding period hPeriod).choose_spec.choose_spec.1

private theorem whitneyEmbedding_mfderiv_injective
    (point : AmbientBase period hPeriod) :
    Function.Injective
      (mfderiv coverModelWithCorners
        𝓘(Real, EuclideanSpace Real (Fin (whitneyDimension period hPeriod)))
        (whitneyEmbedding period hPeriod) point) :=
  (existsWhitneyEmbedding period hPeriod).choose_spec.choose_spec.2.2 point

private theorem ambientQuotientLocalChart_mem_maximalAtlas
    (anchor : AmbientCover period hPeriod) :
    ambientQuotientLocalChart period hPeriod anchor ∈
      IsManifold.maximalAtlas coverModelWithCorners ω
        (AmbientBase period hPeriod) := by
  exact localSectionChart_mem_maximalAtlas coverModelWithCorners ω
    (AmbientData period hPeriod)
    (reflectedSphereCover_deck_contMDiff period hPeriod) anchor

/-- A genuine quotient chart and its inverse, with their analytic
regularity packaged together. -/
private def ambientQuotientChartPartialDiffeomorph
    (anchor : AmbientCover period hPeriod) :
    PartialDiffeomorph coverModelWithCorners coverModelWithCorners
      (AmbientBase period hPeriod) CoverModel ω where
  __ := ambientQuotientLocalChart period hPeriod anchor
  contMDiffOn_toFun := contMDiffOn_of_mem_maximalAtlas
    (ambientQuotientLocalChart_mem_maximalAtlas period hPeriod anchor)
  contMDiffOn_invFun := contMDiffOn_symm_of_mem_maximalAtlas
    (ambientQuotientLocalChart_mem_maximalAtlas period hPeriod anchor)

/-- Local Euclidean realization associated with one genuine quotient chart. -/
def localWhitneyMap
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel) :
    EuclideanSpace Real (Fin (whitneyDimension period hPeriod)) :=
  whitneyEmbedding period hPeriod
    ((ambientQuotientLocalChart period hPeriod anchor).symm coordinate)

private theorem localWhitneyMap_contMDiffOn
    (anchor : AmbientCover period hPeriod) :
    ContMDiffOn coverModelWithCorners
      𝓘(Real, EuclideanSpace Real (Fin (whitneyDimension period hPeriod))) ∞
      (localWhitneyMap period hPeriod anchor)
      (ambientQuotientLocalChart period hPeriod anchor).target := by
  unfold localWhitneyMap
  simpa only [Function.comp_def] using
    (whitneyEmbedding_contMDiff period hPeriod).comp_contMDiffOn
      ((contMDiffOn_symm_of_mem_maximalAtlas
        (ambientQuotientLocalChart_mem_maximalAtlas period hPeriod anchor)).of_le
          (by simp))

/-- Its true manifold derivative in the selected quotient coordinates. -/
def localWhitneyDerivative
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel) :
    CoverCoordinates →L[Real]
      EuclideanSpace Real (Fin (whitneyDimension period hPeriod)) :=
  mfderiv coverModelWithCorners
    𝓘(Real, EuclideanSpace Real (Fin (whitneyDimension period hPeriod)))
    (localWhitneyMap period hPeriod anchor) coordinate

private theorem localWhitneyDerivative_injective
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target) :
    Function.Injective
      (localWhitneyDerivative period hPeriod anchor coordinate) := by
  have hChartLocal :=
    (ambientQuotientChartPartialDiffeomorph period hPeriod anchor).symm
      |>.isLocalDiffeomorphAt
        (I := coverModelWithCorners) (J := coverModelWithCorners) (n := ω)
        hCoordinate
  have hChartDifferentiable := hChartLocal.mdifferentiableAt (by simp)
  have hEmbeddingDifferentiable :
      MDifferentiableAt coverModelWithCorners
        𝓘(Real, EuclideanSpace Real (Fin (whitneyDimension period hPeriod)))
        (whitneyEmbedding period hPeriod)
        ((ambientQuotientLocalChart period hPeriod anchor).symm coordinate) :=
    (whitneyEmbedding_contMDiff period hPeriod).mdifferentiableAt (by simp)
  have hChartInjective : Function.Injective
      (mfderiv coverModelWithCorners coverModelWithCorners
        (ambientQuotientLocalChart period hPeriod anchor).symm coordinate) := by
    change Function.Injective
      (mfderiv coverModelWithCorners coverModelWithCorners
        (ambientQuotientChartPartialDiffeomorph period hPeriod anchor).symm
        coordinate)
    exact (hChartLocal.mfderivToContinuousLinearEquiv (by simp)).injective
  intro first second hEqual
  apply hChartInjective
  apply whitneyEmbedding_mfderiv_injective period hPeriod
    ((ambientQuotientLocalChart period hPeriod anchor).symm coordinate)
  have hFirst := mfderiv_comp_apply coordinate hEmbeddingDifferentiable
    hChartDifferentiable first
  have hSecond := mfderiv_comp_apply coordinate hEmbeddingDifferentiable
    hChartDifferentiable second
  rw [Function.comp_def] at hFirst hSecond
  rw [← hFirst, ← hSecond]
  exact hEqual

/-- Continuous Gram tensor of the local Whitney derivative. -/
def localWhitneyMetric
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel) :
    CoverCoordinates →L[Real] CoverCoordinates →L[Real] Real :=
  (innerSL Real).bilinearComp
    (localWhitneyDerivative period hPeriod anchor coordinate)
    (localWhitneyDerivative period hPeriod anchor coordinate)

@[simp] theorem localWhitneyMetric_apply
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (first second : CoverCoordinates) :
    localWhitneyMetric period hPeriod anchor coordinate first second =
      inner Real
        (localWhitneyDerivative period hPeriod anchor coordinate first)
        (localWhitneyDerivative period hPeriod anchor coordinate second) := by
  rfl

private theorem localWhitneyMetric_symm
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (first second : CoverCoordinates) :
    localWhitneyMetric period hPeriod anchor coordinate first second =
      localWhitneyMetric period hPeriod anchor coordinate second first := by
  simp only [localWhitneyMetric_apply]
  exact real_inner_comm _ _

private theorem localWhitneyMetric_pos
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target)
    (vector : CoverCoordinates) (hVector : vector ≠ 0) :
    0 < localWhitneyMetric period hPeriod anchor coordinate vector vector := by
  rw [localWhitneyMetric_apply]
  apply (real_inner_self_pos).2
  intro hZero
  apply hVector
  exact (localWhitneyDerivative_injective period hPeriod anchor coordinate
    hCoordinate) (by simpa using hZero)

private theorem localWhitneyMetric_apply_contMDiffOn
    (anchor : AmbientCover period hPeriod)
    (first second : CoverModel → CoverCoordinates)
    (hFirst : ContMDiffOn coverModelWithCorners 𝓘(Real, CoverCoordinates) ∞
      first (ambientQuotientLocalChart period hPeriod anchor).target)
    (hSecond : ContMDiffOn coverModelWithCorners 𝓘(Real, CoverCoordinates) ∞
      second (ambientQuotientLocalChart period hPeriod anchor).target) :
    ContMDiffOn coverModelWithCorners 𝓘(Real) ∞
      (fun coordinate => localWhitneyMetric period hPeriod anchor coordinate
        (first coordinate) (second coordinate))
      (ambientQuotientLocalChart period hPeriod anchor).target := by
  intro coordinate hCoordinate
  have hMapAt :=
    (localWhitneyMap_contMDiffOn period hPeriod anchor).contMDiffAt
      ((ambientQuotientLocalChart period hPeriod anchor).open_target.mem_nhds
        hCoordinate)
  have hDerivativeAt := hMapAt.mfderiv_const (m := ∞) (by simp)
  have hTargetMem :=
    (ambientQuotientLocalChart period hPeriod anchor).open_target.mem_nhds
      hCoordinate
  have hFirstImage := hDerivativeAt.clm_apply (hFirst.contMDiffAt hTargetMem)
  have hSecondImage := hDerivativeAt.clm_apply (hSecond.contMDiffAt hTargetMem)
  simpa only [localWhitneyMetric_apply, localWhitneyDerivative,
    inTangentCoordinates_model_space, Function.comp_def] using
    ContDiff.comp_contMDiffWithinAt
      (I := coverModelWithCorners)
      (g := fun pair :
        EuclideanSpace Real (Fin (whitneyDimension period hPeriod)) ×
          EuclideanSpace Real (Fin (whitneyDimension period hPeriod)) =>
        inner Real pair.1 pair.2)
      (contDiff_inner (𝕜 := Real) (E := EuclideanSpace Real
        (Fin (whitneyDimension period hPeriod))) (n := ∞))
      ((hFirstImage.prodMk_space hSecondImage).contMDiffWithinAt)

/-! ## Four-dimensional orthonormal frames -/

private abbrev AmbientHilbert := WithLp 2 CoverCoordinates

private abbrev ambientHilbertCoordinatesEquiv :
    AmbientHilbert ≃L[Real] CoverCoordinates :=
  WithLp.prodContinuousLinearEquiv 2 Real
    (EuclideanSpace Real (Fin 3)) Real

/-- Continuous Euclidean metric on the project's product-norm coordinate
model. -/
private def ambientEuclideanMetric :
    CoverCoordinates →L[Real] CoverCoordinates →L[Real] Real :=
  (innerSL Real).bilinearComp
    ambientHilbertCoordinatesEquiv.symm.toContinuousLinearMap
    ambientHilbertCoordinatesEquiv.symm.toContinuousLinearMap

@[simp] private theorem ambientEuclideanMetric_apply
    (first second : CoverCoordinates) :
    ambientEuclideanMetric first second =
      inner Real (WithLp.toLp 2 first) (WithLp.toLp 2 second) := by
  rfl

private theorem ambientEuclideanMetric_symm
    (first second : CoverCoordinates) :
    ambientEuclideanMetric first second =
      ambientEuclideanMetric second first := by
  simp only [ambientEuclideanMetric_apply]
  exact real_inner_comm _ _

private theorem ambientEuclideanMetric_pos
    (vector : CoverCoordinates) (hVector : vector ≠ 0) :
    0 < ambientEuclideanMetric vector vector := by
  rw [ambientEuclideanMetric_apply]
  exact (real_inner_self_pos).2
    (ambientHilbertCoordinatesEquiv.symm.injective.ne hVector)

private theorem ambientEuclideanMetric_toBilinForm :
    ambientEuclideanMetric.toBilinForm =
      ambientCoverEuclideanBilinearForm := by
  apply LinearMap.ext₂
  intro first second
  change inner Real (WithLp.toLp 2 first) (WithLp.toLp 2 second) =
    inner Real first.1 second.1 + first.2 * second.2
  rw [WithLp.prod_inner_apply]
  simp [mul_comm]

private theorem ambientEuclideanMetric_toQuadraticForm :
    ambientEuclideanMetric.toBilinForm.toQuadraticMap =
      ambientCoverEuclideanQuadraticForm := by
  rw [ambientEuclideanMetric_toBilinForm]
  rfl

private def ambientSeedBasis : Basis (Fin 4) Real CoverCoordinates :=
  Module.finBasisOfFinrankEq Real CoverCoordinates (by
    norm_num [CoverCoordinates])

private theorem ambientSeedBasis_linearIndependent :
    LinearIndependent Real (ambientSeedBasis : Fin 4 → CoverCoordinates) :=
  ambientSeedBasis.linearIndependent

/-- Constant Euclidean Gram--Schmidt family used as the source frame. -/
private def ambientEuclideanOrthonormalFamily (index : Fin 4) :
    CoverCoordinates :=
  metricGramSchmidtNormed (fun _ : Real => ambientEuclideanMetric)
    ambientSeedBasis 0 index

private theorem ambientEuclideanOrthonormalFamily_linearIndependent :
    LinearIndependent Real ambientEuclideanOrthonormalFamily := by
  exact metricGramSchmidtNormed_linearIndependent
    (fun _ : Real => ambientEuclideanMetric) ambientSeedBasis
    ambientSeedBasis_linearIndependent Set.univ
    (by
      intro _ _ first second
      exact ambientEuclideanMetric_symm first second)
    (by
      intro _ _ vector hVector
      exact ambientEuclideanMetric_pos vector hVector)
    0 (Set.mem_univ _)

private theorem ambientEuclideanOrthonormalFamily_gram
    (first second : Fin 4) :
    ambientEuclideanMetric
        (ambientEuclideanOrthonormalFamily first)
        (ambientEuclideanOrthonormalFamily second) =
      if first = second then 1 else 0 := by
  exact metricGramSchmidtNormed_gram
    (fun _ : Real => ambientEuclideanMetric) ambientSeedBasis
    ambientSeedBasis_linearIndependent Set.univ
    (by
      intro _ _ left right
      exact ambientEuclideanMetric_symm left right)
    (by
      intro _ _ vector hVector
      exact ambientEuclideanMetric_pos vector hVector)
    0 (Set.mem_univ _) first second

private def ambientEuclideanOrthonormalBasis :
    Basis (Fin 4) Real CoverCoordinates :=
  basisOfLinearIndependentOfCardEqFinrank
    ambientEuclideanOrthonormalFamily_linearIndependent (by
      norm_num [CoverCoordinates])

@[simp] private theorem ambientEuclideanOrthonormalBasis_apply
    (index : Fin 4) :
    ambientEuclideanOrthonormalBasis index =
      ambientEuclideanOrthonormalFamily index := by
  simp [ambientEuclideanOrthonormalBasis]

/-- The Whitney-metric Gram--Schmidt family in one genuine quotient chart. -/
def localWhitneyOrthonormalFamily
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (index : Fin 4) : CoverCoordinates :=
  metricGramSchmidtNormed (localWhitneyMetric period hPeriod anchor)
    ambientSeedBasis coordinate index

private theorem localWhitneyOrthonormalFamily_linearIndependent
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target) :
    LinearIndependent Real
      (localWhitneyOrthonormalFamily period hPeriod anchor coordinate) := by
  exact metricGramSchmidtNormed_linearIndependent
    (localWhitneyMetric period hPeriod anchor) ambientSeedBasis
    ambientSeedBasis_linearIndependent
    (ambientQuotientLocalChart period hPeriod anchor).target
    (by
      intro x _ first second
      exact localWhitneyMetric_symm period hPeriod anchor x first second)
    (by
      intro x hx vector hVector
      exact localWhitneyMetric_pos period hPeriod anchor x hx vector hVector)
    coordinate hCoordinate

private theorem localWhitneyOrthonormalFamily_gram
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target)
    (first second : Fin 4) :
    localWhitneyMetric period hPeriod anchor coordinate
        (localWhitneyOrthonormalFamily period hPeriod anchor coordinate first)
        (localWhitneyOrthonormalFamily period hPeriod anchor coordinate second) =
      if first = second then 1 else 0 := by
  exact metricGramSchmidtNormed_gram
    (localWhitneyMetric period hPeriod anchor) ambientSeedBasis
    ambientSeedBasis_linearIndependent
    (ambientQuotientLocalChart period hPeriod anchor).target
    (by
      intro x _ left right
      exact localWhitneyMetric_symm period hPeriod anchor x left right)
    (by
      intro x hx vector hVector
      exact localWhitneyMetric_pos period hPeriod anchor x hx vector hVector)
    coordinate hCoordinate first second

private theorem localWhitneyOrthonormalFamily_contMDiffOn
    (anchor : AmbientCover period hPeriod) (index : Fin 4) :
    ContMDiffOn coverModelWithCorners 𝓘(Real, CoverCoordinates) ∞
      (fun coordinate =>
        localWhitneyOrthonormalFamily period hPeriod anchor coordinate index)
      (ambientQuotientLocalChart period hPeriod anchor).target := by
  exact metricGramSchmidtNormed_contMDiffOn_of_apply coverModelWithCorners
    (localWhitneyMetric period hPeriod anchor) ambientSeedBasis
    ambientSeedBasis_linearIndependent
    (ambientQuotientLocalChart period hPeriod anchor).target
    (localWhitneyMetric_apply_contMDiffOn period hPeriod anchor)
    (by
      intro x _ first second
      exact localWhitneyMetric_symm period hPeriod anchor x first second)
    (by
      intro x hx vector hVector
      exact localWhitneyMetric_pos period hPeriod anchor x hx vector hVector)
    index

private def localWhitneyOrthonormalBasis
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target) :
    Basis (Fin 4) Real CoverCoordinates :=
  basisOfLinearIndependentOfCardEqFinrank
    (localWhitneyOrthonormalFamily_linearIndependent period hPeriod anchor
      coordinate hCoordinate) (by norm_num [CoverCoordinates])

@[simp] private theorem localWhitneyOrthonormalBasis_apply
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target)
    (index : Fin 4) :
    localWhitneyOrthonormalBasis period hPeriod anchor coordinate hCoordinate
        index =
      localWhitneyOrthonormalFamily period hPeriod anchor coordinate index := by
  simp [localWhitneyOrthonormalBasis]

/-- Linear change from the fixed Euclidean orthonormal frame to the local
Whitney orthonormal frame. -/
private def localWhitneyFrameLinearEquiv
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target) :
    CoverCoordinates ≃ₗ[Real] CoverCoordinates :=
  ambientEuclideanOrthonormalBasis.equiv
    (localWhitneyOrthonormalBasis period hPeriod anchor coordinate hCoordinate)
    (Equiv.refl (Fin 4))

@[simp] private theorem localWhitneyFrameLinearEquiv_basis
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target)
    (index : Fin 4) :
    localWhitneyFrameLinearEquiv period hPeriod anchor coordinate hCoordinate
        (ambientEuclideanOrthonormalBasis index) =
      localWhitneyOrthonormalFamily period hPeriod anchor coordinate index := by
  rw [← localWhitneyOrthonormalBasis_apply period hPeriod anchor coordinate
    hCoordinate index]
  exact Basis.equiv_apply _ _ _ _

private theorem localWhitneyFrame_bilinear_isometry
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target) :
    (localWhitneyMetric period hPeriod anchor coordinate).toBilinForm.compl₁₂
        (localWhitneyFrameLinearEquiv period hPeriod anchor coordinate
          hCoordinate).toLinearMap
        (localWhitneyFrameLinearEquiv period hPeriod anchor coordinate
          hCoordinate).toLinearMap =
      ambientEuclideanMetric.toBilinForm := by
  apply (LinearMap.BilinForm.ext_iff_basis
    ambientEuclideanOrthonormalBasis).2
  intro first second
  simp only [LinearMap.compl₁₂_apply,
    LinearEquiv.coe_coe,
    localWhitneyFrameLinearEquiv_basis]
  change localWhitneyMetric period hPeriod anchor coordinate
      (localWhitneyOrthonormalFamily period hPeriod anchor coordinate first)
      (localWhitneyOrthonormalFamily period hPeriod anchor coordinate second) =
    ambientEuclideanMetric (ambientEuclideanOrthonormalBasis first)
      (ambientEuclideanOrthonormalBasis second)
  rw [localWhitneyOrthonormalFamily_gram period hPeriod anchor coordinate
      hCoordinate first second,
    ambientEuclideanOrthonormalBasis_apply,
    ambientEuclideanOrthonormalBasis_apply,
    ambientEuclideanOrthonormalFamily_gram]

/-- Quadratic form induced by the local Whitney pullback metric. -/
def localWhitneyQuadraticForm
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel) :
    QuadraticForm Real CoverCoordinates :=
  (localWhitneyMetric period hPeriod anchor coordinate).toBilinForm.toQuadraticMap

@[simp] theorem localWhitneyQuadraticForm_apply
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (vector : CoverCoordinates) :
    localWhitneyQuadraticForm period hPeriod anchor coordinate vector =
      localWhitneyMetric period hPeriod anchor coordinate vector vector := by
  rfl

private def localWhitneyOrthonormalFrame
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target) :
    ambientCoverEuclideanQuadraticForm.IsometryEquiv
      (localWhitneyQuadraticForm period hPeriod anchor coordinate) where
  __ := localWhitneyFrameLinearEquiv period hPeriod anchor coordinate hCoordinate
  map_app' vector := by
    change localWhitneyMetric period hPeriod anchor coordinate
        (localWhitneyFrameLinearEquiv period hPeriod anchor coordinate
          hCoordinate vector)
        (localWhitneyFrameLinearEquiv period hPeriod anchor coordinate
          hCoordinate vector) =
      ambientCoverEuclideanQuadraticForm vector
    rw [← ambientEuclideanMetric_toQuadraticForm]
    exact congrArg (fun form : LinearMap.BilinForm Real CoverCoordinates =>
      form vector vector)
      (localWhitneyFrame_bilinear_isometry period hPeriod anchor coordinate
        hCoordinate)

private theorem localWhitneyFrameLinearEquiv_apply_sum
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target)
    (vector : CoverCoordinates) :
    localWhitneyFrameLinearEquiv period hPeriod anchor coordinate hCoordinate
        vector =
      ∑ index : Fin 4,
        (ambientEuclideanOrthonormalBasis.repr vector index) •
          localWhitneyOrthonormalFamily period hPeriod anchor coordinate index := by
  calc
    _ = localWhitneyFrameLinearEquiv period hPeriod anchor coordinate hCoordinate
        (∑ index : Fin 4,
          (ambientEuclideanOrthonormalBasis.repr vector index) •
            ambientEuclideanOrthonormalBasis index) := by
      rw [ambientEuclideanOrthonormalBasis.sum_repr]
    _ = _ := by
      simp only [map_sum, map_smul, localWhitneyFrameLinearEquiv_basis]

private theorem localWhitneyOrthonormalBasis_repr
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target)
    (vector : CoverCoordinates) (index : Fin 4) :
    (localWhitneyOrthonormalBasis period hPeriod anchor coordinate hCoordinate).repr
        vector index =
      localWhitneyMetric period hPeriod anchor coordinate vector
        (localWhitneyOrthonormalFamily period hPeriod anchor coordinate index) := by
  let basis := localWhitneyOrthonormalBasis period hPeriod anchor coordinate
    hCoordinate
  have hExpand : (∑ current : Fin 4,
      (basis.repr vector current) • basis current) = vector := basis.sum_repr vector
  change basis.repr vector index = _
  calc
    _ = localWhitneyMetric period hPeriod anchor coordinate
        (∑ current : Fin 4, (basis.repr vector current) • basis current)
        (localWhitneyOrthonormalFamily period hPeriod anchor coordinate index) := by
      rw [map_sum, _root_.sum_apply]
      simp only [map_smul, smul_eq_mul, basis,
        localWhitneyOrthonormalBasis_apply]
      rw [Finset.sum_eq_single index]
      · simp [localWhitneyOrthonormalFamily_gram period hPeriod anchor
          coordinate hCoordinate]
      · intro current _ hCurrent
        simp [localWhitneyOrthonormalFamily_gram period hPeriod anchor
          coordinate hCoordinate, hCurrent]
      · simp
    _ = _ := congrArg
      (fun current => localWhitneyMetric period hPeriod anchor coordinate current
        (localWhitneyOrthonormalFamily period hPeriod anchor coordinate index))
      hExpand

private theorem localWhitneyFrameLinearEquiv_symm_apply_sum
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target)
    (vector : CoverCoordinates) :
    (localWhitneyFrameLinearEquiv period hPeriod anchor coordinate hCoordinate).symm
        vector =
      ∑ index : Fin 4,
        localWhitneyMetric period hPeriod anchor coordinate vector
            (localWhitneyOrthonormalFamily period hPeriod anchor coordinate index) •
          ambientEuclideanOrthonormalBasis index := by
  apply (localWhitneyFrameLinearEquiv period hPeriod anchor coordinate
    hCoordinate).injective
  simp only [LinearEquiv.apply_symm_apply, map_sum, map_smul,
    localWhitneyFrameLinearEquiv_basis]
  let basis := localWhitneyOrthonormalBasis period hPeriod anchor coordinate
    hCoordinate
  calc
    vector = ∑ index : Fin 4, (basis.repr vector index) • basis index :=
      (basis.sum_repr vector).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro index _
      rw [show basis index = localWhitneyOrthonormalFamily period hPeriod anchor
          coordinate index by simp [basis, localWhitneyOrthonormalBasis_apply],
        localWhitneyOrthonormalBasis_repr period hPeriod anchor coordinate
          hCoordinate vector index]

private def ambientEuclideanFrameCoefficient (index : Fin 4) :
    CoverCoordinates →L[Real] Real :=
  (ambientEuclideanOrthonormalBasis.coord index).toContinuousLinearMap

@[simp] private theorem ambientEuclideanFrameCoefficient_apply
    (index : Fin 4) (vector : CoverCoordinates) :
    ambientEuclideanFrameCoefficient index vector =
      ambientEuclideanOrthonormalBasis.repr vector index := by
  rfl

private theorem contMDiffWithinAt_finset_sum
    {Index Target : Type*} [NormedAddCommGroup Target] [NormedSpace Real Target]
    (indices : Finset Index)
    (summand : Index → (CoverModel × CoverCoordinates) → Target)
    (domain : Set (CoverModel × CoverCoordinates))
    (point : CoverModel × CoverCoordinates)
    (hSummand : ∀ index ∈ indices,
      ContMDiffWithinAt (coverModelWithCorners.prod coverModelWithCorners)
        𝓘(Real, Target) ∞ (summand index) domain point) :
    ContMDiffWithinAt (coverModelWithCorners.prod coverModelWithCorners)
      𝓘(Real, Target) ∞ (fun input => ∑ index ∈ indices, summand index input)
      domain point := by
  classical
  induction indices using Finset.induction_on with
  | empty => simpa using
      (contMDiffWithinAt_const (I :=
        coverModelWithCorners.prod coverModelWithCorners) (x := point)
        (c := (0 : Target)) (n := ∞) (s := domain))
  | @insert index indices hIndex hInduction =>
      have hAdd := (hSummand index (Finset.mem_insert_self index indices)).add
        (hInduction fun current hCurrent =>
          hSummand current (Finset.mem_insert_of_mem hCurrent))
      refine hAdd.congr (fun input _ => ?_) ?_
      · simp [Finset.sum_insert hIndex]
      · simp [Finset.sum_insert hIndex]

private def localWhitneyFrameFormula
    (anchor : AmbientCover period hPeriod)
    (input : CoverModel × CoverCoordinates) : CoverCoordinates :=
  ∑ index : Fin 4,
    ambientEuclideanFrameCoefficient index input.2 •
      localWhitneyOrthonormalFamily period hPeriod anchor input.1 index

private theorem localWhitneyFrameFormula_contMDiffOn
    (anchor : AmbientCover period hPeriod) :
    ContMDiffOn (coverModelWithCorners.prod coverModelWithCorners)
      coverModelWithCorners ∞ (localWhitneyFrameFormula period hPeriod anchor)
      (chartTangentDomain period hPeriod anchor) := by
  intro input hInput
  classical
  unfold localWhitneyFrameFormula
  have hSelf :
      ContMDiffWithinAt (coverModelWithCorners.prod coverModelWithCorners)
        𝓘(Real, CoverCoordinates) ∞
        (fun current => ∑ index : Fin 4,
          ambientEuclideanFrameCoefficient index current.2 •
            localWhitneyOrthonormalFamily period hPeriod anchor current.1 index)
        (chartTangentDomain period hPeriod anchor) input := by
    simpa using contMDiffWithinAt_finset_sum (Finset.univ : Finset (Fin 4))
      (fun index input => ambientEuclideanFrameCoefficient index input.2 •
        localWhitneyOrthonormalFamily period hPeriod anchor input.1 index)
      (chartTangentDomain period hPeriod anchor) input (by
        intro index _
        have hTarget : input.1 ∈
            (ambientQuotientLocalChart period hPeriod anchor).target := hInput.1
        have hFst :
            ContMDiffAt (coverModelWithCorners.prod coverModelWithCorners)
              coverModelWithCorners ∞
              (fun current : CoverModel × CoverCoordinates => current.1) input :=
          contMDiff_fst.contMDiffAt
        have hFamilySelf :
            ContMDiffAt (coverModelWithCorners.prod coverModelWithCorners)
              𝓘(Real, CoverCoordinates) ∞
              (fun current : CoverModel × CoverCoordinates =>
                localWhitneyOrthonormalFamily period hPeriod anchor current.1 index)
              input :=
          ((localWhitneyOrthonormalFamily_contMDiffOn period hPeriod anchor index)
            |>.contMDiffAt
              ((ambientQuotientLocalChart period hPeriod anchor).open_target.mem_nhds
                hTarget)).comp input hFst
        have hCoefficient :
            ContMDiffAt (coverModelWithCorners.prod coverModelWithCorners)
              𝓘(Real, Real) ∞
              (fun current : CoverModel × CoverCoordinates =>
                ambientEuclideanFrameCoefficient index current.2) input :=
          (ambientEuclideanFrameCoefficient index).contDiff.contMDiff.contMDiffAt.comp
            input
            (((contMDiff_fst.comp contMDiff_snd).prodMk_space
              (contMDiff_snd.comp contMDiff_snd)) |>.contMDiffAt)
        exact (hCoefficient.smul hFamilySelf).contMDiffWithinAt)
  have hFirst := ContDiff.comp_contMDiffWithinAt
    (ContinuousLinearMap.fst Real (EuclideanSpace Real (Fin 3)) Real).contDiff
    hSelf
  have hSecond := ContDiff.comp_contMDiffWithinAt
    (ContinuousLinearMap.snd Real (EuclideanSpace Real (Fin 3)) Real).contDiff
    hSelf
  simpa using hFirst.prodMk hSecond

private def localWhitneyInverseFrameFormula
    (anchor : AmbientCover period hPeriod)
    (input : CoverModel × CoverCoordinates) : CoverCoordinates :=
  ∑ index : Fin 4,
    localWhitneyMetric period hPeriod anchor input.1 input.2
        (localWhitneyOrthonormalFamily period hPeriod anchor input.1 index) •
      ambientEuclideanOrthonormalBasis index

private def localWhitneyInverseFrameExpandedFormula
    (anchor : AmbientCover period hPeriod)
    (input : CoverModel × CoverCoordinates) : CoverCoordinates :=
  ∑ index : Fin 4,
    (∑ current : Fin 4,
      ambientEuclideanFrameCoefficient current input.2 *
        localWhitneyMetric period hPeriod anchor input.1
          (ambientEuclideanOrthonormalBasis current)
          (localWhitneyOrthonormalFamily period hPeriod anchor input.1 index)) •
      ambientEuclideanOrthonormalBasis index

private theorem localWhitneyInverseFrameExpandedFormula_eq
    (anchor : AmbientCover period hPeriod)
    (input : CoverModel × CoverCoordinates) :
    localWhitneyInverseFrameExpandedFormula period hPeriod anchor input =
      localWhitneyInverseFrameFormula period hPeriod anchor input := by
  unfold localWhitneyInverseFrameExpandedFormula localWhitneyInverseFrameFormula
  apply Finset.sum_congr rfl
  intro index _
  congr 1
  calc
    _ = localWhitneyMetric period hPeriod anchor input.1
        (∑ current : Fin 4,
          (ambientEuclideanOrthonormalBasis.repr input.2 current) •
            ambientEuclideanOrthonormalBasis current)
        (localWhitneyOrthonormalFamily period hPeriod anchor input.1 index) := by
      rw [map_sum, _root_.sum_apply]
      apply Finset.sum_congr rfl
      intro current _
      simp [ambientEuclideanFrameCoefficient]
    _ = _ := congrArg
      (fun vector => localWhitneyMetric period hPeriod anchor input.1 vector
        (localWhitneyOrthonormalFamily period hPeriod anchor input.1 index))
      (ambientEuclideanOrthonormalBasis.sum_repr input.2)

private theorem ambientEuclideanFrameCoefficient_snd_contMDiffAt
    (index : Fin 4) (input : CoverModel × CoverCoordinates) :
    ContMDiffAt (coverModelWithCorners.prod coverModelWithCorners)
      𝓘(Real, Real) ∞
      (fun current : CoverModel × CoverCoordinates =>
        ambientEuclideanFrameCoefficient index current.2) input :=
  (ambientEuclideanFrameCoefficient index).contDiff.contMDiff.contMDiffAt.comp
    input
    (((contMDiff_fst.comp contMDiff_snd).prodMk_space
      (contMDiff_snd.comp contMDiff_snd)) |>.contMDiffAt)

private theorem localWhitneyInverseFrameExpandedFormula_contMDiffOn
    (anchor : AmbientCover period hPeriod) :
    ContMDiffOn (coverModelWithCorners.prod coverModelWithCorners)
      coverModelWithCorners ∞
      (localWhitneyInverseFrameExpandedFormula period hPeriod anchor)
      (chartTangentDomain period hPeriod anchor) := by
  intro input hInput
  classical
  have hTarget : input.1 ∈
      (ambientQuotientLocalChart period hPeriod anchor).target := hInput.1
  have hFst :
      ContMDiffAt (coverModelWithCorners.prod coverModelWithCorners)
        coverModelWithCorners ∞
        (fun current : CoverModel × CoverCoordinates => current.1) input :=
    contMDiff_fst.contMDiffAt
  have hSelf :
      ContMDiffWithinAt (coverModelWithCorners.prod coverModelWithCorners)
        𝓘(Real, CoverCoordinates) ∞
        (localWhitneyInverseFrameExpandedFormula period hPeriod anchor)
        (chartTangentDomain period hPeriod anchor) input := by
    unfold localWhitneyInverseFrameExpandedFormula
    simpa using contMDiffWithinAt_finset_sum (Finset.univ : Finset (Fin 4))
      (fun index current =>
        (∑ basisIndex : Fin 4,
          ambientEuclideanFrameCoefficient basisIndex current.2 *
            localWhitneyMetric period hPeriod anchor current.1
              (ambientEuclideanOrthonormalBasis basisIndex)
              (localWhitneyOrthonormalFamily period hPeriod anchor current.1 index)) •
          ambientEuclideanOrthonormalBasis index)
      (chartTangentDomain period hPeriod anchor) input (by
        intro index _
        have hScalar :
            ContMDiffWithinAt (coverModelWithCorners.prod coverModelWithCorners)
              𝓘(Real, Real) ∞
              (fun current => ∑ basisIndex : Fin 4,
                ambientEuclideanFrameCoefficient basisIndex current.2 *
                  localWhitneyMetric period hPeriod anchor current.1
                    (ambientEuclideanOrthonormalBasis basisIndex)
                    (localWhitneyOrthonormalFamily period hPeriod anchor
                      current.1 index))
              (chartTangentDomain period hPeriod anchor) input := by
          simpa using contMDiffWithinAt_finset_sum
            (Finset.univ : Finset (Fin 4))
            (fun basisIndex current =>
              ambientEuclideanFrameCoefficient basisIndex current.2 *
                localWhitneyMetric period hPeriod anchor current.1
                  (ambientEuclideanOrthonormalBasis basisIndex)
                  (localWhitneyOrthonormalFamily period hPeriod anchor
                    current.1 index))
            (chartTangentDomain period hPeriod anchor) input (by
              intro basisIndex _
              have hMetricBase := localWhitneyMetric_apply_contMDiffOn
                period hPeriod anchor
                (fun _ => ambientEuclideanOrthonormalBasis basisIndex)
                (fun coordinate => localWhitneyOrthonormalFamily period hPeriod
                  anchor coordinate index)
                contMDiffOn_const
                (localWhitneyOrthonormalFamily_contMDiffOn period hPeriod anchor
                  index)
              have hMetric := (hMetricBase.contMDiffAt
                ((ambientQuotientLocalChart period hPeriod anchor).open_target.mem_nhds
                  hTarget)).comp input hFst
              exact ((ambientEuclideanFrameCoefficient_snd_contMDiffAt
                basisIndex input).mul hMetric).contMDiffWithinAt)
        exact hScalar.smul
          (contMDiffWithinAt_const (I :=
            coverModelWithCorners.prod coverModelWithCorners) (x := input)
            (c := ambientEuclideanOrthonormalBasis index) (n := ∞)
            (s := chartTangentDomain period hPeriod anchor)))
  have hFirst := ContDiff.comp_contMDiffWithinAt
    (ContinuousLinearMap.fst Real (EuclideanSpace Real (Fin 3)) Real).contDiff
    hSelf
  have hSecond := ContDiff.comp_contMDiffWithinAt
    (ContinuousLinearMap.snd Real (EuclideanSpace Real (Fin 3)) Real).contDiff
    hSelf
  simpa using hFirst.prodMk hSecond

private theorem localWhitneyInverseFrameFormula_contMDiffOn
    (anchor : AmbientCover period hPeriod) :
    ContMDiffOn (coverModelWithCorners.prod coverModelWithCorners)
      coverModelWithCorners ∞
      (localWhitneyInverseFrameFormula period hPeriod anchor)
      (chartTangentDomain period hPeriod anchor) := by
  intro input hInput
  refine (localWhitneyInverseFrameExpandedFormula_contMDiffOn period hPeriod
    anchor input hInput).congr ?_ ?_
  · intro current _
    exact (localWhitneyInverseFrameExpandedFormula_eq period hPeriod anchor current).symm
  · exact (localWhitneyInverseFrameExpandedFormula_eq period hPeriod anchor input).symm

private theorem chartTangentDomain_isOpen
    (anchor : AmbientCover period hPeriod) :
    IsOpen (chartTangentDomain period hPeriod anchor) :=
  (ambientQuotientLocalChart period hPeriod anchor).open_target.prod isOpen_univ

private theorem transitionTangentDomain_isOpen
    (first second : AmbientCover period hPeriod) :
    IsOpen (transitionTangentDomain period hPeriod first second) :=
  (ambientAtlasTransition period hPeriod first second).open_source.prod isOpen_univ

private def tangentTransitionAppliedToFrameFormula
    (first second : AmbientCover period hPeriod)
    (input : CoverModel × CoverCoordinates) : CoverCoordinates :=
  mfderiv coverModelWithCorners coverModelWithCorners
    (ambientAtlasTransition period hPeriod first second) input.1
    (localWhitneyFrameFormula period hPeriod first input)

private theorem tangentTransitionAppliedToFrameFormula_contMDiffOn
    (first second : AmbientCover period hPeriod) :
    ContMDiffOn (coverModelWithCorners.prod coverModelWithCorners)
      coverModelWithCorners ∞
      (tangentTransitionAppliedToFrameFormula period hPeriod first second)
      (transitionTangentDomain period hPeriod first second) := by
  intro input hInput
  have hSource : input.1 ∈
      (ambientAtlasTransition period hPeriod first second).source := hInput.1
  have hFirstTarget : input.1 ∈
      (ambientQuotientLocalChart period hPeriod first).target := by
    change input.1 ∈
      ((ambientQuotientLocalChart period hPeriod first).symm.trans
        (ambientQuotientLocalChart period hPeriod second)).source at hSource
    rw [OpenPartialHomeomorph.trans_source] at hSource
    exact hSource.1
  have hTransitionAt :
      ContMDiffAt coverModelWithCorners coverModelWithCorners ∞
        (ambientAtlasTransition period hPeriod first second) input.1 :=
    ((ambientAtlasPartialDiffeomorph period hPeriod first second).contMDiffOn_toFun
      |>.contMDiffAt
        ((ambientAtlasTransition period hPeriod first second).open_source.mem_nhds
          hSource)).of_le (by simp)
  have hUncurry :
      ContMDiffAt (coverModelWithCorners.prod coverModelWithCorners)
        coverModelWithCorners ∞
        (Function.uncurry (fun _ : CoverModel =>
          (ambientAtlasTransition period hPeriod first second :
            CoverModel → CoverModel))) (input.1, input.1) := by
    change ContMDiffAt (coverModelWithCorners.prod coverModelWithCorners)
      coverModelWithCorners ∞
      (fun current : CoverModel × CoverModel =>
        ambientAtlasTransition period hPeriod first second current.2)
      (input.1, input.1)
    exact hTransitionAt.comp (input.1, input.1) contMDiffAt_snd
  have hFst :
      ContMDiffAt (coverModelWithCorners.prod coverModelWithCorners)
        coverModelWithCorners ∞
        (fun current : CoverModel × CoverCoordinates => current.1) input :=
    contMDiff_fst.contMDiffAt
  have hFrame :=
    (localWhitneyFrameFormula_contMDiffOn period hPeriod first).contMDiffAt
      ((chartTangentDomain_isOpen period hPeriod first).mem_nhds
        ⟨hFirstTarget, Set.mem_univ input.2⟩)
  have hFrameFirst := contMDiffAt_fst.comp input hFrame
  have hFrameSecond := contMDiffAt_snd.comp input hFrame
  have hFrameSelf :
      ContMDiffAt (coverModelWithCorners.prod coverModelWithCorners)
        𝓘(Real, CoverCoordinates) ∞
        (localWhitneyFrameFormula period hPeriod first) input := by
    simpa using hFrameFirst.prodMk_space hFrameSecond
  have hApplied := ContMDiffAt.mfderiv_apply
    (I := coverModelWithCorners) (I' := coverModelWithCorners)
    (f := fun _ : CoverModel =>
      (ambientAtlasTransition period hPeriod first second : CoverModel → CoverModel))
    (g := id) (g₁ := fun current : CoverModel × CoverCoordinates => current.1)
    (g₂ := localWhitneyFrameFormula period hPeriod first)
    hUncurry contMDiffAt_id hFst hFrameSelf (by simp)
  have hAppliedWithin :
      ContMDiffWithinAt (coverModelWithCorners.prod coverModelWithCorners)
        𝓘(Real, CoverCoordinates) ∞ _
        (transitionTangentDomain period hPeriod first second) input :=
    hApplied.contMDiffWithinAt
  have hFirst := ContDiff.comp_contMDiffWithinAt
    (ContinuousLinearMap.fst Real (EuclideanSpace Real (Fin 3)) Real).contDiff
    hAppliedWithin
  have hSecond := ContDiff.comp_contMDiffWithinAt
    (ContinuousLinearMap.snd Real (EuclideanSpace Real (Fin 3)) Real).contDiff
    hAppliedWithin
  refine (hFirst.prodMk hSecond).congr ?_ ?_
  · intro current _
    simp only [tangentTransitionAppliedToFrameFormula,
      inTangentCoordinates_model_space, Function.comp_apply]
    rfl
  · simp only [tangentTransitionAppliedToFrameFormula,
      inTangentCoordinates_model_space, Function.comp_apply]
    rfl

/-! ## Compatibility on genuine atlas overlaps -/

private theorem transitionSource_mem_firstChart_target
    (first second : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    coordinate ∈
      (ambientQuotientLocalChart period hPeriod first).target := by
  change coordinate ∈
    ((ambientQuotientLocalChart period hPeriod first).symm.trans
      (ambientQuotientLocalChart period hPeriod second)).source at hCoordinate
  rw [OpenPartialHomeomorph.trans_source] at hCoordinate
  exact hCoordinate.1

private theorem transitionTarget_mem_secondChart_target
    (first second : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    ambientAtlasTransition period hPeriod first second coordinate ∈
      (ambientQuotientLocalChart period hPeriod second).target := by
  have hTarget :=
    (ambientAtlasTransition period hPeriod first second).map_source hCoordinate
  change ambientAtlasTransition period hPeriod first second coordinate ∈
    ((ambientQuotientLocalChart period hPeriod first).symm.trans
      (ambientQuotientLocalChart period hPeriod second)).target at hTarget
  rw [OpenPartialHomeomorph.trans_target] at hTarget
  exact hTarget.1

private theorem ambientAtlasTransition_chartInverse
    (first second : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    (ambientQuotientLocalChart period hPeriod second).symm
        (ambientAtlasTransition period hPeriod first second coordinate) =
      (ambientQuotientLocalChart period hPeriod first).symm coordinate := by
  change coordinate ∈
    ((ambientQuotientLocalChart period hPeriod first).symm.trans
      (ambientQuotientLocalChart period hPeriod second)).source at hCoordinate
  rw [OpenPartialHomeomorph.trans_source] at hCoordinate
  change
    (ambientQuotientLocalChart period hPeriod second).symm
        ((ambientQuotientLocalChart period hPeriod second)
          ((ambientQuotientLocalChart period hPeriod first).symm coordinate)) =
      (ambientQuotientLocalChart period hPeriod first).symm coordinate
  exact (ambientQuotientLocalChart period hPeriod second).left_inv hCoordinate.2

private theorem localWhitneyMap_transition
    (first second : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    localWhitneyMap period hPeriod second
        (ambientAtlasTransition period hPeriod first second coordinate) =
      localWhitneyMap period hPeriod first coordinate := by
  unfold localWhitneyMap
  rw [ambientAtlasTransition_chartInverse period hPeriod first second
    coordinate hCoordinate]

private theorem localWhitneyDerivative_transition_apply
    (first second : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source)
    (vector : CoverCoordinates) :
    localWhitneyDerivative period hPeriod second
        (ambientAtlasTransition period hPeriod first second coordinate)
        (ambientAtlasTangentTransition period hPeriod first second coordinate
          hCoordinate vector) =
      localWhitneyDerivative period hPeriod first coordinate vector := by
  have hSecondTarget := transitionTarget_mem_secondChart_target period hPeriod
    first second coordinate hCoordinate
  have hTransitionDifferentiable :
      MDifferentiableAt coverModelWithCorners coverModelWithCorners
        (ambientAtlasTransition period hPeriod first second) coordinate :=
    ((ambientAtlasPartialDiffeomorph period hPeriod first second)
      |>.isLocalDiffeomorphAt
        (I := coverModelWithCorners) (J := coverModelWithCorners) (n := ω)
        hCoordinate).mdifferentiableAt (by simp)
  have hSecondDifferentiable :
      MDifferentiableAt coverModelWithCorners
        𝓘(Real, EuclideanSpace Real (Fin (whitneyDimension period hPeriod)))
        (localWhitneyMap period hPeriod second)
        (ambientAtlasTransition period hPeriod first second coordinate) :=
    ((localWhitneyMap_contMDiffOn period hPeriod second).contMDiffAt
      ((ambientQuotientLocalChart period hPeriod second).open_target.mem_nhds
        hSecondTarget)).mdifferentiableAt (by simp)
  have hEventually :
      (localWhitneyMap period hPeriod second) ∘
          (ambientAtlasTransition period hPeriod first second) =ᶠ[nhds coordinate]
        localWhitneyMap period hPeriod first := by
    apply Filter.eventuallyEq_of_mem
      ((ambientAtlasTransition period hPeriod first second).open_source.mem_nhds
        hCoordinate)
    intro point hPoint
    exact localWhitneyMap_transition period hPeriod first second point hPoint
  have hDerivative := Filter.EventuallyEq.mfderiv_eq
    (I := coverModelWithCorners)
    (I' := 𝓘(Real,
      EuclideanSpace Real (Fin (whitneyDimension period hPeriod)))) hEventually
  change localWhitneyDerivative period hPeriod second
      (ambientAtlasTransition period hPeriod first second coordinate)
      ((ambientAtlasTangentTransition period hPeriod first second coordinate
        hCoordinate : CoverCoordinates →L[Real] CoverCoordinates) vector) =
    localWhitneyDerivative period hPeriod first coordinate vector
  rw [ambientAtlasTangentTransition_coe]
  change mfderiv coverModelWithCorners
      𝓘(Real, EuclideanSpace Real (Fin (whitneyDimension period hPeriod)))
      (localWhitneyMap period hPeriod second)
      (ambientAtlasTransition period hPeriod first second coordinate)
      (mfderiv coverModelWithCorners coverModelWithCorners
        (ambientAtlasTransition period hPeriod first second) coordinate vector) =
    mfderiv coverModelWithCorners
      𝓘(Real, EuclideanSpace Real (Fin (whitneyDimension period hPeriod)))
      (localWhitneyMap period hPeriod first) coordinate vector
  rw [← mfderiv_comp_apply coordinate hSecondDifferentiable
    hTransitionDifferentiable vector]
  exact congrArg (fun derivative => derivative vector) hDerivative

private theorem localWhitneyMetric_transition
    (first second : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source)
    (left right : CoverCoordinates) :
    localWhitneyMetric period hPeriod second
        (ambientAtlasTransition period hPeriod first second coordinate)
        (ambientAtlasTangentTransition period hPeriod first second coordinate
          hCoordinate left)
        (ambientAtlasTangentTransition period hPeriod first second coordinate
          hCoordinate right) =
      localWhitneyMetric period hPeriod first coordinate left right := by
  simp only [localWhitneyMetric_apply]
  rw [localWhitneyDerivative_transition_apply period hPeriod first second
      coordinate hCoordinate left,
    localWhitneyDerivative_transition_apply period hPeriod first second
      coordinate hCoordinate right]

/-! ## Total pointwise reduction -/

def ambientSmoothAtlasForm
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel) :
    QuadraticForm Real CoverCoordinates := by
  classical
  exact if coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target then
    localWhitneyQuadraticForm period hPeriod anchor coordinate
  else
    ambientCoverEuclideanQuadraticForm

private theorem ambientSmoothAtlasForm_posDef
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel) :
    (ambientSmoothAtlasForm period hPeriod anchor coordinate).PosDef := by
  classical
  by_cases hCoordinate : coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target
  · simp only [ambientSmoothAtlasForm, if_pos hCoordinate]
    intro vector hVector
    exact localWhitneyMetric_pos period hPeriod anchor coordinate hCoordinate
      vector hVector
  · simp only [ambientSmoothAtlasForm, if_neg hCoordinate]
    exact ambientCoverEuclideanQuadraticForm_posDef

def ambientSmoothAtlasOrthonormalFrame
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel) :
    ambientCoverEuclideanQuadraticForm.IsometryEquiv
      (ambientSmoothAtlasForm period hPeriod anchor coordinate) := by
  classical
  by_cases hCoordinate : coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target
  · refine
      { toLinearEquiv := localWhitneyFrameLinearEquiv period hPeriod anchor
          coordinate hCoordinate
        map_app' := ?_ }
    intro vector
    simp only [ambientSmoothAtlasForm, if_pos hCoordinate,
      localWhitneyQuadraticForm_apply]
    rw [← ambientEuclideanMetric_toQuadraticForm]
    exact congrArg (fun form : LinearMap.BilinForm Real CoverCoordinates =>
      form vector vector)
      (localWhitneyFrame_bilinear_isometry period hPeriod anchor coordinate
        hCoordinate)
  · refine
      { toLinearEquiv := LinearEquiv.refl Real CoverCoordinates
        map_app' := ?_ }
    intro vector
    simp only [ambientSmoothAtlasForm, if_neg hCoordinate]
    rfl

private def ambientSmoothAtlasTransition
    (first second : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientAtlasTransition period hPeriod first second).source) :
    (ambientSmoothAtlasForm period hPeriod first coordinate).IsometryEquiv
      (ambientSmoothAtlasForm period hPeriod second
        (ambientAtlasTransition period hPeriod first second coordinate)) where
  __ := (ambientAtlasTangentTransition period hPeriod first second coordinate
    hCoordinate).toLinearEquiv
  map_app' vector := by
    have hFirstTarget := transitionSource_mem_firstChart_target period hPeriod
      first second coordinate hCoordinate
    have hSecondTarget := transitionTarget_mem_secondChart_target period hPeriod
      first second coordinate hCoordinate
    simp only [ambientSmoothAtlasForm, if_pos hFirstTarget,
      if_pos hSecondTarget, localWhitneyQuadraticForm_apply]
    exact localWhitneyMetric_transition period hPeriod first second coordinate
      hCoordinate vector vector

/-- Pointwise reduction obtained from one global Whitney embedding and true
local quotient charts. -/
def ambientSmoothOrthonormalAtlasReduction :
    AmbientOrthonormalAtlasReduction period hPeriod where
  form := ambientSmoothAtlasForm period hPeriod
  positiveDefinite := ambientSmoothAtlasForm_posDef period hPeriod
  orthonormalFrame := ambientSmoothAtlasOrthonormalFrame period hPeriod
  transition := ambientSmoothAtlasTransition period hPeriod
  transition_coe := by
    intro first second coordinate hCoordinate
    rfl

/-! ## Joint smooth reduction -/

private def localWhitneyOrthogonalTransitionFormula
    (first second : AmbientCover period hPeriod)
    (input : CoverModel × CoverCoordinates) : CoverCoordinates :=
  localWhitneyInverseFrameFormula period hPeriod second
    (ambientAtlasTransition period hPeriod first second input.1,
      tangentTransitionAppliedToFrameFormula period hPeriod first second input)

private def localWhitneyTransitionInput
    (first second : AmbientCover period hPeriod)
    (input : CoverModel × CoverCoordinates) :
    CoverModel × CoverCoordinates :=
  (ambientAtlasTransition period hPeriod first second input.1,
    tangentTransitionAppliedToFrameFormula period hPeriod first second input)

private theorem localWhitneyTransitionInput_contMDiffOn
    (first second : AmbientCover period hPeriod) :
    ContMDiffOn (coverModelWithCorners.prod coverModelWithCorners)
      (coverModelWithCorners.prod coverModelWithCorners) ∞
      (localWhitneyTransitionInput period hPeriod first second)
      (transitionTangentDomain period hPeriod first second) := by
  intro input hInput
  have hTransitionAt :
      ContMDiffAt coverModelWithCorners coverModelWithCorners ∞
        (ambientAtlasTransition period hPeriod first second) input.1 :=
    ((ambientAtlasPartialDiffeomorph period hPeriod first second).contMDiffOn_toFun
      |>.contMDiffAt
        ((ambientAtlasTransition period hPeriod first second).open_source.mem_nhds
          hInput.1)).of_le (by simp)
  have hFirst :
      ContMDiffWithinAt (coverModelWithCorners.prod coverModelWithCorners)
        coverModelWithCorners ∞
        (fun current : CoverModel × CoverCoordinates =>
          ambientAtlasTransition period hPeriod first second current.1)
        (transitionTangentDomain period hPeriod first second) input :=
    (hTransitionAt.comp input contMDiffAt_fst).contMDiffWithinAt
  refine (hFirst.prodMk
    (tangentTransitionAppliedToFrameFormula_contMDiffOn period hPeriod first
      second input hInput)).congr ?_ ?_
  · intro current _
    rfl
  · rfl

private theorem localWhitneyTransitionInput_mapsTo
    (first second : AmbientCover period hPeriod) :
    Set.MapsTo
      (localWhitneyTransitionInput period hPeriod first second)
      (transitionTangentDomain period hPeriod first second)
      (chartTangentDomain period hPeriod second) := by
  intro input hInput
  exact ⟨transitionTarget_mem_secondChart_target period hPeriod first second
    input.1 hInput.1, Set.mem_univ _⟩

set_option maxHeartbeats 800000 in
private theorem localWhitneyOrthogonalTransitionFormula_contMDiffOn
    (first second : AmbientCover period hPeriod) :
    ContMDiffOn (coverModelWithCorners.prod coverModelWithCorners)
      coverModelWithCorners ∞
      (localWhitneyOrthogonalTransitionFormula period hPeriod first second)
      (transitionTangentDomain period hPeriod first second) := by
  intro input hInput
  have hComposed : ContMDiffWithinAt
      (coverModelWithCorners.prod coverModelWithCorners)
      coverModelWithCorners ∞
      (localWhitneyInverseFrameFormula period hPeriod second ∘
        localWhitneyTransitionInput period hPeriod first second)
      (transitionTangentDomain period hPeriod first second) input :=
    ContMDiffWithinAt.comp input
    (localWhitneyInverseFrameFormula_contMDiffOn period hPeriod second
      _ (localWhitneyTransitionInput_mapsTo period hPeriod first second hInput))
    (localWhitneyTransitionInput_contMDiffOn period hPeriod first second
      input hInput)
    (localWhitneyTransitionInput_mapsTo period hPeriod first second)
  refine hComposed.congr ?_ ?_
  · intro current _
    rfl
  · rfl

private theorem ambientSmoothAtlasOrthonormalFrame_toLinearEquiv
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target) :
    (ambientSmoothAtlasOrthonormalFrame period hPeriod anchor
      coordinate).toLinearEquiv =
      localWhitneyFrameLinearEquiv period hPeriod anchor coordinate
        hCoordinate := by
  classical
  unfold ambientSmoothAtlasOrthonormalFrame
  simp only [hCoordinate, dite_true]

private theorem ambientSmoothAtlasOrthonormalFrame_apply_eq_formula
    (anchor : AmbientCover period hPeriod) (coordinate : CoverModel)
    (hCoordinate : coordinate ∈
      (ambientQuotientLocalChart period hPeriod anchor).target)
    (vector : CoverCoordinates) :
    ambientSmoothAtlasOrthonormalFrame period hPeriod anchor coordinate vector =
      localWhitneyFrameFormula period hPeriod anchor (coordinate, vector) := by
  classical
  change (ambientSmoothAtlasOrthonormalFrame period hPeriod anchor
    coordinate).toLinearEquiv vector = _
  rw [ambientSmoothAtlasOrthonormalFrame_toLinearEquiv period hPeriod anchor
    coordinate hCoordinate]
  simpa only [localWhitneyFrameFormula,
    ambientEuclideanFrameCoefficient_apply] using
    localWhitneyFrameLinearEquiv_apply_sum period hPeriod anchor coordinate
      hCoordinate vector

private theorem reductionFrameApplication_eq_formula
    (anchor : AmbientCover period hPeriod)
    (input : CoverModel × CoverCoordinates)
    (hInput : input ∈ chartTangentDomain period hPeriod anchor) :
    reductionFrameApplication period hPeriod
        (ambientSmoothOrthonormalAtlasReduction period hPeriod) anchor input =
      localWhitneyFrameFormula period hPeriod anchor input := by
  exact ambientSmoothAtlasOrthonormalFrame_apply_eq_formula period hPeriod
    anchor input.1 hInput.1 input.2

private theorem reductionFrameApplication_contMDiffOn
    (anchor : AmbientCover period hPeriod) :
    ContMDiffOn (coverModelWithCorners.prod coverModelWithCorners)
      coverModelWithCorners ∞
      (reductionFrameApplication period hPeriod
        (ambientSmoothOrthonormalAtlasReduction period hPeriod) anchor)
      (chartTangentDomain period hPeriod anchor) := by
  intro input hInput
  refine (localWhitneyFrameFormula_contMDiffOn period hPeriod anchor input
    hInput).congr ?_ ?_
  · intro current hCurrent
    exact reductionFrameApplication_eq_formula period hPeriod anchor current
      hCurrent
  · exact reductionFrameApplication_eq_formula period hPeriod anchor input hInput

private def localWhitneyFormFormula
    (anchor : AmbientCover period hPeriod)
    (input : CoverModel × CoverCoordinates) : Real :=
  ambientCoverEuclideanQuadraticForm
    (localWhitneyInverseFrameFormula period hPeriod anchor input)

private theorem localWhitneyFormFormula_contMDiffOn
    (anchor : AmbientCover period hPeriod) :
    ContMDiffOn (coverModelWithCorners.prod coverModelWithCorners)
      𝓘(Real, Real) ∞ (localWhitneyFormFormula period hPeriod anchor)
      (chartTangentDomain period hPeriod anchor) := by
  intro input hInput
  have hQuadratic : ContDiff Real ∞
      (fun vector : CoverCoordinates => ambientEuclideanMetric vector vector) :=
    ambientEuclideanMetric.contDiff.clm_apply contDiff_id
  have hInverseAt :=
    ContMDiffOn.contMDiffAt
      (localWhitneyInverseFrameFormula_contMDiffOn period hPeriod anchor)
      ((chartTangentDomain_isOpen period hPeriod anchor).mem_nhds hInput)
  have hInverseFirst := contMDiffAt_fst.comp input hInverseAt
  have hInverseSecond := contMDiffAt_snd.comp input hInverseAt
  have hInverseSelf :
      ContMDiffWithinAt (coverModelWithCorners.prod coverModelWithCorners)
        𝓘(Real, CoverCoordinates) ∞
        (localWhitneyInverseFrameFormula period hPeriod anchor)
        (chartTangentDomain period hPeriod anchor) input := by
    exact (hInverseFirst.prodMk_space hInverseSecond).contMDiffWithinAt
  have hComposed := ContDiff.comp_contMDiffWithinAt hQuadratic
    hInverseSelf
  refine hComposed.congr ?_ ?_
  · intro current _
    unfold localWhitneyFormFormula
    rw [← ambientEuclideanMetric_toQuadraticForm]
    rfl
  · unfold localWhitneyFormFormula
    rw [← ambientEuclideanMetric_toQuadraticForm]
    rfl

private theorem reductionFormApplication_eq_formula
    (anchor : AmbientCover period hPeriod)
    (input : CoverModel × CoverCoordinates)
    (hInput : input ∈ chartTangentDomain period hPeriod anchor) :
    reductionFormApplication period hPeriod
        (ambientSmoothOrthonormalAtlasReduction period hPeriod) anchor input =
      localWhitneyFormFormula period hPeriod anchor input := by
  classical
  let frame := localWhitneyFrameLinearEquiv period hPeriod anchor input.1
    hInput.1
  have hInverse : frame.symm input.2 =
      localWhitneyInverseFrameFormula period hPeriod anchor input := by
    simpa only [frame, localWhitneyInverseFrameFormula] using
      localWhitneyFrameLinearEquiv_symm_apply_sum period hPeriod anchor input.1
        hInput.1 input.2
  change ambientSmoothAtlasForm period hPeriod anchor input.1 input.2 = _
  rw [show ambientSmoothAtlasForm period hPeriod anchor input.1 =
      localWhitneyQuadraticForm period hPeriod anchor input.1 by
    simp only [ambientSmoothAtlasForm, if_pos hInput.1]]
  calc
    localWhitneyQuadraticForm period hPeriod anchor input.1 input.2 =
        localWhitneyQuadraticForm period hPeriod anchor input.1
          (frame (frame.symm input.2)) := by rw [frame.apply_symm_apply]
    _ = ambientCoverEuclideanQuadraticForm (frame.symm input.2) := by
      exact (localWhitneyOrthonormalFrame period hPeriod anchor input.1
        hInput.1).map_app (frame.symm input.2)
    _ = localWhitneyFormFormula period hPeriod anchor input := by
      rw [hInverse]
      rfl

private theorem reductionFormApplication_contMDiffOn
    (anchor : AmbientCover period hPeriod) :
    ContMDiffOn (coverModelWithCorners.prod coverModelWithCorners)
      𝓘(Real, Real) ∞
      (reductionFormApplication period hPeriod
        (ambientSmoothOrthonormalAtlasReduction period hPeriod) anchor)
      (chartTangentDomain period hPeriod anchor) := by
  intro input hInput
  refine (localWhitneyFormFormula_contMDiffOn period hPeriod anchor input
    hInput).congr ?_ ?_
  · intro current hCurrent
    exact reductionFormApplication_eq_formula period hPeriod anchor current
      hCurrent
  · exact reductionFormApplication_eq_formula period hPeriod anchor input hInput

private theorem reductionOrthogonalTransitionApplication_eq_formula
    (first second : AmbientCover period hPeriod)
    (input : CoverModel × CoverCoordinates)
    (hInput : input ∈ transitionTangentDomain period hPeriod first second) :
    reductionOrthogonalTransitionApplication period hPeriod
        (ambientSmoothOrthonormalAtlasReduction period hPeriod) first second
        input =
      localWhitneyOrthogonalTransitionFormula period hPeriod first second
        input := by
  classical
  have hFirstTarget := transitionSource_mem_firstChart_target period hPeriod
    first second input.1 hInput.1
  have hSecondTarget := transitionTarget_mem_secondChart_target period hPeriod
    first second input.1 hInput.1
  have hFirstFrame :
      localWhitneyFrameLinearEquiv period hPeriod first input.1 hFirstTarget
          input.2 =
        localWhitneyFrameFormula period hPeriod first input := by
    simpa only [localWhitneyFrameFormula,
      ambientEuclideanFrameCoefficient_apply] using
      localWhitneyFrameLinearEquiv_apply_sum period hPeriod first input.1
        hFirstTarget input.2
  simp only [reductionOrthogonalTransitionApplication, hInput.1, dite_true]
  change
    (ambientSmoothAtlasOrthonormalFrame period hPeriod second
      (ambientAtlasTransition period hPeriod first second input.1)).toLinearEquiv.symm
      ((ambientSmoothAtlasTransition period hPeriod first second input.1
        hInput.1).toLinearEquiv
        ((ambientSmoothAtlasOrthonormalFrame period hPeriod first
          input.1).toLinearEquiv input.2)) = _
  rw [ambientSmoothAtlasOrthonormalFrame_toLinearEquiv period hPeriod first
      input.1 hFirstTarget,
    ambientSmoothAtlasOrthonormalFrame_toLinearEquiv period hPeriod second
      (ambientAtlasTransition period hPeriod first second input.1) hSecondTarget]
  change
    (localWhitneyFrameLinearEquiv period hPeriod second
      (ambientAtlasTransition period hPeriod first second input.1)
      hSecondTarget).symm
      ((ambientAtlasTangentTransition period hPeriod first second input.1
        hInput.1 : CoverCoordinates →L[Real] CoverCoordinates)
        (localWhitneyFrameLinearEquiv period hPeriod first input.1
          hFirstTarget input.2)) = _
  rw [ambientAtlasTangentTransition_coe, hFirstFrame]
  unfold localWhitneyOrthogonalTransitionFormula
  unfold tangentTransitionAppliedToFrameFormula localWhitneyInverseFrameFormula
  rw [localWhitneyFrameLinearEquiv_symm_apply_sum period hPeriod second
    (ambientAtlasTransition period hPeriod first second input.1) hSecondTarget]
  rfl

private theorem reductionOrthogonalTransitionApplication_contMDiffOn
    (first second : AmbientCover period hPeriod) :
    ContMDiffOn (coverModelWithCorners.prod coverModelWithCorners)
      coverModelWithCorners ∞
      (reductionOrthogonalTransitionApplication period hPeriod
        (ambientSmoothOrthonormalAtlasReduction period hPeriod) first second)
      (transitionTangentDomain period hPeriod first second) := by
  intro input hInput
  refine (localWhitneyOrthogonalTransitionFormula_contMDiffOn period hPeriod
    first second input hInput).congr ?_ ?_
  · intro current hCurrent
    exact reductionOrthogonalTransitionApplication_eq_formula period hPeriod
      first second current hCurrent
  · exact reductionOrthogonalTransitionApplication_eq_formula period hPeriod
      first second input hInput

/-- The Whitney pullback metric, its Gram--Schmidt frame and all genuine
orthogonal overlap maps form a jointly `C∞` atlas reduction. -/
def ambientSmoothContMDiffOrthonormalAtlasReduction :
    AmbientContMDiffOrthonormalAtlasReduction period hPeriod where
  toPointwise := ambientSmoothOrthonormalAtlasReduction period hPeriod
  form_contMDiffOn := reductionFormApplication_contMDiffOn period hPeriod
  frame_contMDiffOn := reductionFrameApplication_contMDiffOn period hPeriod
  transition_contMDiffOn :=
    reductionOrthogonalTransitionApplication_contMDiffOn period hPeriod

theorem ambientContMDiffOrthonormalAtlasReduction_nonempty :
    Nonempty (AmbientContMDiffOrthonormalAtlasReduction period hPeriod) :=
  ⟨ambientSmoothContMDiffOrthonormalAtlasReduction period hPeriod⟩

end

end P0EFTJanusMappingTorusAmbientSmoothOrthonormalReduction4D
end JanusFormal
