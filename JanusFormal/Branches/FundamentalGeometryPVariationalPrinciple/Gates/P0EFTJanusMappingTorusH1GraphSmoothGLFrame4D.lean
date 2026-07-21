import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusH1GraphSmoothOrthogonalFrame4D

namespace JanusFormal
namespace P0EFTJanusMappingTorusH1GraphSmoothGLFrame4D

set_option autoImplicit false
noncomputable section

open scoped ENNReal Manifold ContDiff
open MeasureTheory
open P0EFTJanusMappingTorusQuotient
open P0EFTJanusMappingTorusSmoothAtlasFrontier
open P0EFTJanusMappingTorusSmoothQuotientManifold
open P0EFTJanusMappingTorusCompactQuotient
open P0EFTJanusMappingTorusSmoothFieldDescent4D
open P0EFTJanusMappingTorusH1GraphTrace4D
open P0EFTJanusMappingTorusH1GraphFrameChange4D
open P0EFTJanusMappingTorusH1GraphPermutationFrame4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : CompactSpace (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientCompactSpace period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

/-- A genuine smooth `GL(n,ℝ)` change of finite tangent generators. -/
structure SmoothGLFrameChange
    (source target : SmoothD8Frame period hPeriod) where
  matrix : EffectiveQuotient period hPeriod →
    Matrix (Fin source.count) (Fin source.count) Real
  inverseMatrix : EffectiveQuotient period hPeriod →
    Matrix (Fin source.count) (Fin source.count) Real
  same_count : target.count = source.count
  matrix_smooth : ∀ j i,
    ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (fun point => matrix point j i)
  inverse_smooth : ∀ j i,
    ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (fun point => inverseMatrix point j i)
  left_inverse : ∀ point, inverseMatrix point * matrix point = 1
  right_inverse : ∀ point, matrix point * inverseMatrix point = 1
  target_vector_eq : ∀ point (j : Fin source.count),
    target.vectorAt point (Fin.cast same_count.symm j) =
      ∑ i, matrix point j i • source.vectorAt point i
  source_vector_eq : ∀ point (j : Fin source.count),
    source.vectorAt point j =
      ∑ i : Fin target.count,
        inverseMatrix point j (Fin.cast same_count i) • target.vectorAt point i

theorem smoothMatrix_exists_uniform_entry_bound
    {n : Nat}
    (matrix : EffectiveQuotient period hPeriod → Matrix (Fin n) (Fin n) Real)
    (smooth : ∀ j i,
      ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
        (fun point => matrix point j i)) :
    ∃ bound : Real, 0 ≤ bound ∧ ∀ point j i, |matrix point j i| ≤ bound := by
  let localBound : Fin n × Fin n → Real := fun index =>
    Classical.choose
      (isCompact_univ.bddAbove_image
        ((smooth index.1 index.2).continuous.norm.continuousOn))
  have hLocal : ∀ point j i, |matrix point j i| ≤ localBound (j, i) := by
    intro point j i
    exact Classical.choose_spec
      (isCompact_univ.bddAbove_image
        ((smooth j i).continuous.norm.continuousOn)) ⟨point, Set.mem_univ point, rfl⟩
  obtain ⟨upper, hUpper⟩ := Finite.exists_le localBound
  refine ⟨max 0 upper, le_max_left _ _, ?_⟩
  intro point j i
  exact (hLocal point j i).trans ((hUpper (j, i)).trans (le_max_right _ _))

noncomputable def smoothMatrixUniformEntryBound
    {n : Nat}
    (matrix : EffectiveQuotient period hPeriod → Matrix (Fin n) (Fin n) Real)
    (smooth : ∀ j i,
      ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
        (fun point => matrix point j i)) : Real :=
  Classical.choose (smoothMatrix_exists_uniform_entry_bound period hPeriod matrix smooth)

theorem smoothMatrixUniformEntryBound_nonneg
    {n : Nat}
    (matrix : EffectiveQuotient period hPeriod → Matrix (Fin n) (Fin n) Real)
    (smooth : ∀ j i,
      ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
        (fun point => matrix point j i)) :
    0 ≤ smoothMatrixUniformEntryBound period hPeriod matrix smooth :=
  (Classical.choose_spec
    (smoothMatrix_exists_uniform_entry_bound period hPeriod matrix smooth)).1

theorem smoothMatrix_le_uniformEntryBound
    {n : Nat}
    (matrix : EffectiveQuotient period hPeriod → Matrix (Fin n) (Fin n) Real)
    (smooth : ∀ j i,
      ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
        (fun point => matrix point j i))
    (point : EffectiveQuotient period hPeriod) (j i : Fin n) :
    |matrix point j i| ≤ smoothMatrixUniformEntryBound period hPeriod matrix smooth :=
  (Classical.choose_spec
    (smoothMatrix_exists_uniform_entry_bound period hPeriod matrix smooth)).2 point j i

universe u
variable (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

theorem matrixAction_norm_le_card_mul
    {n : Nat} (matrix : Matrix (Fin n) (Fin n) Real)
    (bound : Real) (hBound : 0 ≤ bound)
    (hEntry : ∀ j i, |matrix j i| ≤ bound)
    (values : Fin n → Fiber) :
    ‖fun j => ∑ i, matrix j i • values i‖ ≤ (n * bound) * ‖values‖ := by
  apply (pi_norm_le_iff_of_nonneg
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hBound) (norm_nonneg _))).2
  intro j
  calc
    ‖∑ i, matrix j i • values i‖ ≤ ∑ i, ‖matrix j i • values i‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, bound * ‖values‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hEntry j i)
        ((pi_norm_le_iff_of_nonneg (norm_nonneg values)).1 le_rfl i)
        (norm_nonneg _) hBound
    _ = (n * bound) * ‖values‖ := by simp; ring

noncomputable def smoothGLUniformFrameChange
    (source target : SmoothD8Frame period hPeriod)
    (change : SmoothGLFrameChange period hPeriod source target) :
    UniformSmoothFrameChange period hPeriod Fiber source target := by
  let entryBound := smoothMatrixUniformEntryBound period hPeriod
    change.matrix change.matrix_smooth
  have hEntryBound := smoothMatrixUniformEntryBound_nonneg period hPeriod
    change.matrix change.matrix_smooth
  have hEntry := smoothMatrix_le_uniformEntryBound period hPeriod
    change.matrix change.matrix_smooth
  refine
    { coefficient := fun point j i =>
        change.matrix point (Fin.cast change.same_count j) i
      coefficient_smooth := fun j i =>
        change.matrix_smooth (Fin.cast change.same_count j) i
      vector_eq := fun point j => by
        simpa using change.target_vector_eq point (Fin.cast change.same_count j)
      bound := max 1 (source.count * entryBound)
      one_le_bound := le_max_left _ _
      matrix_bound := ?_ }
  intro point values
  let reindex : Fin target.count ≃ Fin source.count := Fin.castOrderIso change.same_count
  have h := matrixAction_norm_le_card_mul Fiber (change.matrix point)
    entryBound hEntryBound (hEntry point) values
  have hReindex :
      ‖fun j : Fin target.count =>
          ∑ i, change.matrix point (Fin.cast change.same_count j) i • values i‖ =
        ‖fun j : Fin source.count => ∑ i, change.matrix point j i • values i‖ :=
    norm_comp_fintype_equiv Fiber reindex
      (fun j => ∑ i, change.matrix point j i • values i)
  rw [hReindex]
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

noncomputable def smoothGLUniformFrameChangeBack
    (source target : SmoothD8Frame period hPeriod)
    (change : SmoothGLFrameChange period hPeriod source target) :
    UniformSmoothFrameChange period hPeriod Fiber target source := by
  let entryBound := smoothMatrixUniformEntryBound period hPeriod
    change.inverseMatrix change.inverse_smooth
  have hEntryBound := smoothMatrixUniformEntryBound_nonneg period hPeriod
    change.inverseMatrix change.inverse_smooth
  have hEntry := smoothMatrix_le_uniformEntryBound period hPeriod
    change.inverseMatrix change.inverse_smooth
  refine
    { coefficient := fun point j i =>
        change.inverseMatrix point j (Fin.cast change.same_count i)
      coefficient_smooth := fun j i =>
        change.inverse_smooth j (Fin.cast change.same_count i)
      vector_eq := change.source_vector_eq
      bound := max 1 (source.count * entryBound)
      one_le_bound := le_max_left _ _
      matrix_bound := ?_ }
  intro point values
  let reindex : Fin target.count ≃ Fin source.count := Fin.castOrderIso change.same_count
  have h := matrixAction_norm_le_card_mul Fiber (change.inverseMatrix point)
    entryBound hEntryBound (hEntry point) (fun i => values (reindex.symm i))
  have hValues : ‖fun i => values (reindex.symm i)‖ = ‖values‖ :=
    norm_comp_fintype_equiv Fiber reindex.symm values
  have hLeft :
      ‖fun j : Fin source.count =>
          ∑ i : Fin target.count,
            change.inverseMatrix point j (Fin.cast change.same_count i) • values i‖ =
        ‖fun j : Fin source.count =>
          ∑ i : Fin source.count,
            change.inverseMatrix point j i • values (reindex.symm i)‖ := by
    congr 1
    funext j
    apply Fintype.sum_equiv reindex
    intro i
    rfl
  rw [← hLeft, hValues] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

noncomputable def smoothGLH1GraphEquiv
    [CompleteSpace Fiber]
    (source target : SmoothD8Frame period hPeriod)
    (change : SmoothGLFrameChange period hPeriod source target)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] :=
  h1GraphFrameChangeEquiv period hPeriod Fiber source target
    (smoothGLUniformFrameChange period hPeriod Fiber source target change)
    (smoothGLUniformFrameChangeBack period hPeriod Fiber source target change) mu

@[simp] theorem smoothGLH1GraphEquiv_smooth
    [CompleteSpace Fiber]
    (source target : SmoothD8Frame period hPeriod)
    (change : SmoothGLFrameChange period hPeriod source target)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothQuotientField period hPeriod Fiber) :
    smoothGLH1GraphEquiv period hPeriod Fiber source target change mu
        (smoothToH1GraphLinearMap period hPeriod Fiber source mu field) =
      smoothToH1GraphLinearMap period hPeriod Fiber target mu field := by
  apply h1GraphFrameChangeEquiv_smooth

end
end P0EFTJanusMappingTorusH1GraphSmoothGLFrame4D
end JanusFormal
