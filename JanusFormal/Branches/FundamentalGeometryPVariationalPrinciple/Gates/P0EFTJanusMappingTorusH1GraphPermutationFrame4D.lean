import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusH1GraphFrameChangeCoherence4D

namespace JanusFormal
namespace P0EFTJanusMappingTorusH1GraphPermutationFrame4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusH1GraphFrameChange4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

/-- Reordering a finite generating family changes no geometric vector. -/
def permuteSmoothD8Frame
    (frame : SmoothD8Frame period hPeriod)
    (permutation : Fin frame.count ≃ Fin frame.count) :
    SmoothD8Frame period hPeriod where
  count := frame.count
  vectorAt point j := frame.vectorAt point (permutation j)
  spansAt point := by
    rw [show Set.range (fun j => frame.vectorAt point (permutation j)) =
        Set.range (frame.vectorAt point) by
      ext vector
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨permutation j, rfl⟩
      · rintro ⟨i, rfl⟩
        exact ⟨permutation.symm i, by simp⟩]
    exact frame.spansAt point
  contMDiff_vector j := frame.contMDiff_vector (permutation j)

universe u
variable (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

theorem norm_comp_fin_equiv
    {n : Nat} (permutation : Fin n ≃ Fin n) (values : Fin n → Fiber) :
    ‖fun j => values (permutation j)‖ = ‖values‖ := by
  simp only [Pi.norm_def, NNReal.coe_inj]
  apply le_antisymm
  · apply Finset.sup_le
    intro j hj
    exact Finset.le_sup (f := fun i => ‖values i‖₊) (Finset.mem_univ (permutation j))
  · apply Finset.sup_le
    intro i hi
    simpa using Finset.le_sup (f := fun j => ‖values (permutation j)‖₊)
      (Finset.mem_univ (permutation.symm i))

theorem norm_comp_fintype_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    (equiv : α ≃ β) (values : β → Fiber) :
    ‖fun i => values (equiv i)‖ = ‖values‖ := by
  simp only [Pi.norm_def, NNReal.coe_inj]
  apply le_antisymm
  · apply Finset.sup_le
    intro i hi
    exact Finset.le_sup (f := fun j => ‖values j‖₊) (Finset.mem_univ (equiv i))
  · apply Finset.sup_le
    intro j hj
    simpa using Finset.le_sup (f := fun i => ‖values (equiv i)‖₊)
      (Finset.mem_univ (equiv.symm j))

/-- A permutation is a smooth frame change with the sharp bound one. -/
def permutationUniformSmoothFrameChange
    (frame : SmoothD8Frame period hPeriod)
    (permutation : Fin frame.count ≃ Fin frame.count) :
    UniformSmoothFrameChange period hPeriod Fiber frame
      (permuteSmoothD8Frame period hPeriod frame permutation) where
  coefficient _ j i := if i = permutation j then 1 else 0
  coefficient_smooth j i := contMDiff_const
  vector_eq point j := by simp [permuteSmoothD8Frame]
  bound := 1
  one_le_bound := le_rfl
  matrix_bound point values := by
    change ‖fun j : Fin frame.count =>
        ∑ i, (if i = permutation j then (1 : Real) else 0) • values i‖ ≤
      1 * ‖values‖
    have hFunction :
        (fun j => ∑ i, (if i = permutation j then (1 : Real) else 0) • values i) =
          fun j => values (permutation j) := by
      funext j
      simp
    rw [hFunction, norm_comp_fin_equiv Fiber permutation, one_mul]

/-- The reverse permutation supplies the inverse sharp frame change. -/
def permutationUniformSmoothFrameChangeBack
    (frame : SmoothD8Frame period hPeriod)
    (permutation : Fin frame.count ≃ Fin frame.count) :
    UniformSmoothFrameChange period hPeriod Fiber
      (permuteSmoothD8Frame period hPeriod frame permutation) frame where
  coefficient _ j i := if i = permutation.symm j then 1 else 0
  coefficient_smooth j i := contMDiff_const
  vector_eq point j := by simp [permuteSmoothD8Frame]
  bound := 1
  one_le_bound := le_rfl
  matrix_bound point values := by
    change ‖fun j : Fin frame.count =>
        ∑ i, (if i = permutation.symm j then (1 : Real) else 0) • values i‖ ≤
      1 * ‖values‖
    have hFunction :
        (fun j => ∑ i, (if i = permutation.symm j then (1 : Real) else 0) • values i) =
          fun j => values (permutation.symm j) := by
      funext j
      simp
    rw [hFunction, norm_comp_fin_equiv Fiber permutation.symm, one_mul]
    exact le_rfl

theorem constantMatrixAction_norm_le_card
    {n : Nat} (matrix : Fin n → Fin n → Real)
    (hEntry : ∀ j i, |matrix j i| ≤ 1)
    (values : Fin n → Fiber) :
    ‖fun j => ∑ i, matrix j i • values i‖ ≤ n * ‖values‖ := by
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))).2
  intro j
  calc
    ‖∑ i, matrix j i • values i‖ ≤ ∑ i, ‖matrix j i • values i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, ‖values‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs]
      calc
        |matrix j i| * ‖values i‖ ≤ ‖values i‖ := by
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (hEntry j i) (norm_nonneg (values i))
        _ ≤ ‖values‖ :=
          (pi_norm_le_iff_of_nonneg (norm_nonneg values)).1 le_rfl i
    _ = n * ‖values‖ := by simp

/-- A constant orthogonal change between two supplied generating frames.
The two vector identities record the matrix and its transpose geometrically;
the entry bound is the standard coordinate consequence of orthogonality. -/
structure ConstantOrthogonalFrameChange
    (source target : SmoothD8Frame period hPeriod) where
  matrix : Matrix (Fin source.count) (Fin source.count) Real
  same_count : target.count = source.count
  orthogonal :
    Matrix.transpose matrix * matrix =
      (1 : Matrix (Fin source.count) (Fin source.count) Real)
  entry_bound : ∀ j i, |matrix j i| ≤ 1
  target_vector_eq : ∀ point (j : Fin source.count),
    target.vectorAt point (Fin.cast same_count.symm j) =
      ∑ i, matrix j i • source.vectorAt point i
  source_vector_eq : ∀ point (j : Fin source.count),
    source.vectorAt point j =
      ∑ i : Fin target.count,
        matrix (Fin.cast same_count i) j • target.vectorAt point i

/-- The forward orthogonal change has the explicit sup-norm bound
`max 1 (cardinality)`. -/
def constantOrthogonalUniformSmoothFrameChange
    (source target : SmoothD8Frame period hPeriod)
    (change : ConstantOrthogonalFrameChange period hPeriod source target) :
    UniformSmoothFrameChange period hPeriod Fiber source target where
  coefficient _ j i := change.matrix (Fin.cast change.same_count j) i
  coefficient_smooth j i := contMDiff_const
  vector_eq point j := by
    simpa using change.target_vector_eq point (Fin.cast change.same_count j)
  bound := max 1 source.count
  one_le_bound := le_max_left _ _
  matrix_bound point values := by
    let reindex : Fin target.count ≃ Fin source.count := Fin.castOrderIso change.same_count
    have h := constantMatrixAction_norm_le_card Fiber change.matrix change.entry_bound values
    have hReindex :
        ‖fun j : Fin target.count =>
            ∑ i, change.matrix (Fin.cast change.same_count j) i • values i‖ =
          ‖fun j : Fin source.count => ∑ i, change.matrix j i • values i‖ := by
      exact norm_comp_fintype_equiv Fiber reindex
        (fun j => ∑ i, change.matrix j i • values i)
    rw [hReindex]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

def constantOrthogonalUniformSmoothFrameChangeBack
    (source target : SmoothD8Frame period hPeriod)
    (change : ConstantOrthogonalFrameChange period hPeriod source target) :
    UniformSmoothFrameChange period hPeriod Fiber target source where
  coefficient _ j i :=
    change.matrix (Fin.cast change.same_count i) j
  coefficient_smooth j i := contMDiff_const
  vector_eq point j := change.source_vector_eq point j
  bound := max 1 source.count
  one_le_bound := le_max_left _ _
  matrix_bound point values := by
    let reindex : Fin target.count ≃ Fin source.count := Fin.castOrderIso change.same_count
    let transposeMatrix : Matrix (Fin source.count) (Fin source.count) Real :=
      Matrix.transpose change.matrix
    have hEntry : ∀ j i, |transposeMatrix j i| ≤ 1 := by
      intro j i
      exact change.entry_bound i j
    have h := constantMatrixAction_norm_le_card Fiber transposeMatrix hEntry
      (fun i => values (reindex.symm i))
    have hValues : ‖fun i => values (reindex.symm i)‖ = ‖values‖ :=
      norm_comp_fintype_equiv Fiber reindex.symm values
    have hLeft :
        ‖fun j : Fin source.count =>
            ∑ i : Fin target.count,
              change.matrix (Fin.cast change.same_count i) j • values i‖ =
          ‖fun j : Fin source.count =>
            ∑ i : Fin source.count, transposeMatrix j i • values (reindex.symm i)‖ := by
      congr 1
      funext j
      apply Fintype.sum_equiv reindex
      intro i
      rfl
    rw [← hLeft, hValues] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

/-- The concrete H¹ equivalence induced by reordering the generators. -/
def permutationH1GraphEquiv
    [CompleteSpace Fiber]
    (frame : SmoothD8Frame period hPeriod)
    (permutation : Fin frame.count ≃ Fin frame.count)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] :=
  h1GraphFrameChangeEquiv period hPeriod Fiber frame
    (permuteSmoothD8Frame period hPeriod frame permutation)
    (permutationUniformSmoothFrameChange period hPeriod Fiber frame permutation)
    (permutationUniformSmoothFrameChangeBack period hPeriod Fiber frame permutation) mu

@[simp] theorem permutationH1GraphEquiv_smooth
    [CompleteSpace Fiber]
    (frame : SmoothD8Frame period hPeriod)
    (permutation : Fin frame.count ≃ Fin frame.count)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothQuotientField period hPeriod Fiber) :
    permutationH1GraphEquiv period hPeriod Fiber frame permutation mu
        (smoothToH1GraphLinearMap period hPeriod Fiber frame mu field) =
      smoothToH1GraphLinearMap period hPeriod Fiber
        (permuteSmoothD8Frame period hPeriod frame permutation) mu field := by
  apply h1GraphFrameChangeEquiv_smooth

/-- The concrete bicontinuous H¹ equivalence induced by a constant
orthogonal change of generators. -/
def constantOrthogonalH1GraphEquiv
    [CompleteSpace Fiber]
    (source target : SmoothD8Frame period hPeriod)
    (change : ConstantOrthogonalFrameChange period hPeriod source target)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] :=
  h1GraphFrameChangeEquiv period hPeriod Fiber source target
    (constantOrthogonalUniformSmoothFrameChange period hPeriod Fiber source target change)
    (constantOrthogonalUniformSmoothFrameChangeBack period hPeriod Fiber source target change) mu

@[simp] theorem constantOrthogonalH1GraphEquiv_smooth
    [CompleteSpace Fiber]
    (source target : SmoothD8Frame period hPeriod)
    (change : ConstantOrthogonalFrameChange period hPeriod source target)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothQuotientField period hPeriod Fiber) :
    constantOrthogonalH1GraphEquiv period hPeriod Fiber source target change mu
        (smoothToH1GraphLinearMap period hPeriod Fiber source mu field) =
      smoothToH1GraphLinearMap period hPeriod Fiber target mu field := by
  apply h1GraphFrameChangeEquiv_smooth

end
end P0EFTJanusMappingTorusH1GraphPermutationFrame4D
end JanusFormal
