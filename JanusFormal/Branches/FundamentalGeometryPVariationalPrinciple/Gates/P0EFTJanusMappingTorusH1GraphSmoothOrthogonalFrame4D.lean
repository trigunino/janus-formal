import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusMappingTorusH1GraphPermutationFrame4D

namespace JanusFormal
namespace P0EFTJanusMappingTorusH1GraphSmoothOrthogonalFrame4D

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
open P0EFTJanusMappingTorusH1GraphPermutationFrame4D

variable (period : Real) (hPeriod : period ≠ 0)
private abbrev sphereData := reflectedSphereData period hPeriod
private abbrev EffectiveQuotient := MappingTorus (sphereData period hPeriod)

local instance : ChartedSpace CoverModel (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotientChartedSpace period hPeriod
local instance : IsManifold coverModelWithCorners ω (EffectiveQuotient period hPeriod) :=
  reflectedSphereQuotient_isManifold period hPeriod
local instance : MeasurableSpace (EffectiveQuotient period hPeriod) := borel _
local instance : BorelSpace (EffectiveQuotient period hPeriod) where measurable_eq := rfl

/-- A point-dependent smooth orthogonal change between two finite tangent
generating families.  The two vector identities express the inverse transpose
on the actual tangent bundle. -/
structure SmoothOrthogonalFrameChange
    (source target : SmoothD8Frame period hPeriod) where
  matrix : EffectiveQuotient period hPeriod →
    Matrix (Fin source.count) (Fin source.count) Real
  same_count : target.count = source.count
  coefficient_smooth : ∀ j i,
    ContMDiff coverModelWithCorners 𝓘(Real, Real) ∞
      (fun point => matrix point j i)
  orthogonal : ∀ point,
    Matrix.transpose (matrix point) * matrix point =
      (1 : Matrix (Fin source.count) (Fin source.count) Real)
  entry_bound : ∀ point j i, |matrix point j i| ≤ 1
  target_vector_eq : ∀ point (j : Fin source.count),
    target.vectorAt point (Fin.cast same_count.symm j) =
      ∑ i, matrix point j i • source.vectorAt point i
  source_vector_eq : ∀ point (j : Fin source.count),
    source.vectorAt point j =
      ∑ i : Fin target.count,
        matrix point (Fin.cast same_count i) j • target.vectorAt point i

universe u
variable (Fiber : Type u) [NormedAddCommGroup Fiber] [NormedSpace Real Fiber]

/-- Forward pointwise-orthogonal frame change, uniformly bounded in the
sup norm by `max 1 n`. -/
def smoothOrthogonalUniformFrameChange
    (source target : SmoothD8Frame period hPeriod)
    (change : SmoothOrthogonalFrameChange period hPeriod source target) :
    UniformSmoothFrameChange period hPeriod Fiber source target where
  coefficient point j i := change.matrix point (Fin.cast change.same_count j) i
  coefficient_smooth j i :=
    change.coefficient_smooth (Fin.cast change.same_count j) i
  vector_eq point j := by
    simpa using change.target_vector_eq point (Fin.cast change.same_count j)
  bound := max 1 source.count
  one_le_bound := le_max_left _ _
  matrix_bound point values := by
    let reindex : Fin target.count ≃ Fin source.count := Fin.castOrderIso change.same_count
    have h := constantMatrixAction_norm_le_card Fiber (change.matrix point)
      (change.entry_bound point) values
    have hReindex :
        ‖fun j : Fin target.count =>
            ∑ i, change.matrix point (Fin.cast change.same_count j) i • values i‖ =
          ‖fun j : Fin source.count => ∑ i, change.matrix point j i • values i‖ :=
      norm_comp_fintype_equiv Fiber reindex
        (fun j => ∑ i, change.matrix point j i • values i)
    rw [hReindex]
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

/-- The inverse smooth change is the pointwise transpose and has the same
uniform bound. -/
def smoothOrthogonalUniformFrameChangeBack
    (source target : SmoothD8Frame period hPeriod)
    (change : SmoothOrthogonalFrameChange period hPeriod source target) :
    UniformSmoothFrameChange period hPeriod Fiber target source where
  coefficient point j i := change.matrix point (Fin.cast change.same_count i) j
  coefficient_smooth j i :=
    change.coefficient_smooth (Fin.cast change.same_count i) j
  vector_eq point j := change.source_vector_eq point j
  bound := max 1 source.count
  one_le_bound := le_max_left _ _
  matrix_bound point values := by
    let reindex : Fin target.count ≃ Fin source.count := Fin.castOrderIso change.same_count
    let transposeMatrix : Matrix (Fin source.count) (Fin source.count) Real :=
      Matrix.transpose (change.matrix point)
    have hEntry : ∀ j i, |transposeMatrix j i| ≤ 1 := by
      intro j i
      exact change.entry_bound point i j
    have h := constantMatrixAction_norm_le_card Fiber transposeMatrix hEntry
      (fun i => values (reindex.symm i))
    have hValues : ‖fun i => values (reindex.symm i)‖ = ‖values‖ :=
      norm_comp_fintype_equiv Fiber reindex.symm values
    have hLeft :
        ‖fun j : Fin source.count =>
            ∑ i : Fin target.count,
              change.matrix point (Fin.cast change.same_count i) j • values i‖ =
          ‖fun j : Fin source.count =>
            ∑ i : Fin source.count, transposeMatrix j i • values (reindex.symm i)‖ := by
      congr 1
      funext j
      apply Fintype.sum_equiv reindex
      intro i
      rfl
    rw [← hLeft, hValues] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))

/-- Canonical H¹ equivalence for a smooth pointwise orthogonal change. -/
def smoothOrthogonalH1GraphEquiv
    [CompleteSpace Fiber]
    (source target : SmoothD8Frame period hPeriod)
    (change : SmoothOrthogonalFrameChange period hPeriod source target)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu] :=
  h1GraphFrameChangeEquiv period hPeriod Fiber source target
    (smoothOrthogonalUniformFrameChange period hPeriod Fiber source target change)
    (smoothOrthogonalUniformFrameChangeBack period hPeriod Fiber source target change) mu

@[simp] theorem smoothOrthogonalH1GraphEquiv_smooth
    [CompleteSpace Fiber]
    (source target : SmoothD8Frame period hPeriod)
    (change : SmoothOrthogonalFrameChange period hPeriod source target)
    (mu : Measure (EffectiveQuotient period hPeriod)) [IsFiniteMeasure mu]
    (field : SmoothQuotientField period hPeriod Fiber) :
    smoothOrthogonalH1GraphEquiv period hPeriod Fiber source target change mu
        (smoothToH1GraphLinearMap period hPeriod Fiber source mu field) =
      smoothToH1GraphLinearMap period hPeriod Fiber target mu field := by
  apply h1GraphFrameChangeEquiv_smooth

end
end P0EFTJanusMappingTorusH1GraphSmoothOrthogonalFrame4D
end JanusFormal
