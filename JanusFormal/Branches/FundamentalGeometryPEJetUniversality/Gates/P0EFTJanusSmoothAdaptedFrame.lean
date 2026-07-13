import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSmoothProjectorField

namespace JanusFormal
namespace P0EFTJanusSmoothAdaptedFrame

set_option autoImplicit false

noncomputable section

open scoped ContDiff InnerProductSpace Topology
open Set Filter Finset Submodule Module

universe u v

variable {Base : Type u}
variable {Ambient : Type v}
variable [NormedAddCommGroup Base]
variable [NormedSpace ℝ Base]
variable [NormedAddCommGroup Ambient]
variable [InnerProductSpace ℝ Ambient]

open P0EFTJanusSmoothProjectorField

/-- Pointwise Gram--Schmidt family associated with a varying finite family. -/
def varyingGramSchmidt
    {κ : Type*} [LinearOrder κ] [LocallyFiniteOrderBot κ]
    [WellFoundedLT κ]
    (family : κ → Base → Ambient)
    (k : κ)
    (x : Base) : Ambient :=
  InnerProductSpace.gramSchmidt ℝ (fun j => family j x) k

/-- Pointwise normalized Gram--Schmidt family. -/
def varyingGramSchmidtNormed
    {κ : Type*} [LinearOrder κ] [LocallyFiniteOrderBot κ]
    [WellFoundedLT κ]
    (family : κ → Base → Ambient)
    (k : κ)
    (x : Base) : Ambient :=
  InnerProductSpace.gramSchmidtNormed ℝ (fun j => family j x) k

/-- Gram--Schmidt is smooth on every set where the input family is pointwise
linearly independent. The proof follows the recursive projection formula and
uses that all Gram--Schmidt denominators are nonzero on that locus. -/
theorem varyingGramSchmidt_contDiffOn
    {κ : Type*} [Fintype κ] [LinearOrder κ]
    [LocallyFiniteOrderBot κ] [WellFoundedLT κ]
    (family : κ → Base → Ambient)
    (hSmooth : ∀ k, ContDiff ℝ ∞ (family k))
    (u : Set Base)
    (hIndependent : ∀ x ∈ u,
      LinearIndependent ℝ (fun k => family k x)) :
    ∀ k, ContDiffOn ℝ ∞ (varyingGramSchmidt family k) u := by
  intro k
  induction k using wellFounded_lt.induction with
  | h k ih =>
      have hFormula :
          varyingGramSchmidt family k =
            fun x => family k x -
              ∑ i ∈ Finset.Iio k,
                (inner ℝ (varyingGramSchmidt family i x) (family k x) /
                    ‖varyingGramSchmidt family i x‖ ^ 2) •
                  varyingGramSchmidt family i x := by
        funext x
        simp only [varyingGramSchmidt]
        rw [InnerProductSpace.gramSchmidt_def]
        simp_rw [Submodule.starProjection_singleton]
      rw [hFormula]
      apply (hSmooth k).contDiffOn.sub
      apply ContDiffOn.sum
      intro i hi
      have hi_lt : i < k := Finset.mem_Iio.mp hi
      have hgi : ContDiffOn ℝ ∞ (varyingGramSchmidt family i) u :=
        ih i hi_lt
      have hInner : ContDiffOn ℝ ∞
          (fun x => inner ℝ (varyingGramSchmidt family i x) (family k x)) u :=
        hgi.inner ℝ (hSmooth k).contDiffOn
      have hNormSq : ContDiffOn ℝ ∞
          (fun x => ‖varyingGramSchmidt family i x‖ ^ 2) u :=
        hgi.norm_sq ℝ
      have hDenominator : ∀ x ∈ u,
          ‖varyingGramSchmidt family i x‖ ^ 2 ≠ 0 := by
        intro x hx
        apply pow_ne_zero
        exact norm_ne_zero_iff.mpr
          (InnerProductSpace.gramSchmidt_ne_zero ℝ i
            (hIndependent x hx))
      exact (hInner.div hNormSq hDenominator).smul hgi

/-- The normalized Gram--Schmidt frame is smooth on the same independence
locus. -/
theorem varyingGramSchmidtNormed_contDiffOn
    {κ : Type*} [Fintype κ] [LinearOrder κ]
    [LocallyFiniteOrderBot κ] [WellFoundedLT κ]
    (family : κ → Base → Ambient)
    (hSmooth : ∀ k, ContDiff ℝ ∞ (family k))
    (u : Set Base)
    (hIndependent : ∀ x ∈ u,
      LinearIndependent ℝ (fun k => family k x)) :
    ∀ k, ContDiffOn ℝ ∞ (varyingGramSchmidtNormed family k) u := by
  intro k
  have hg : ContDiffOn ℝ ∞ (varyingGramSchmidt family k) u :=
    varyingGramSchmidt_contDiffOn family hSmooth u hIndependent k
  have hg_ne : ∀ x ∈ u, varyingGramSchmidt family k x ≠ 0 := by
    intro x hx
    exact InnerProductSpace.gramSchmidt_ne_zero ℝ k
      (hIndependent x hx)
  have hNorm : ContDiffOn ℝ ∞
      (fun x => ‖varyingGramSchmidt family k x‖) u :=
    hg.norm ℝ hg_ne
  have hNorm_ne : ∀ x ∈ u, ‖varyingGramSchmidt family k x‖ ≠ 0 := by
    intro x hx
    exact norm_ne_zero_iff.mpr (hg_ne x hx)
  change ContDiffOn ℝ ∞
    (fun x => ‖varyingGramSchmidt family k x‖⁻¹ •
      varyingGramSchmidt family k x) u
  exact (hNorm.inv hNorm_ne).smul hg

/-- On the pointwise independence locus, normalized Gram--Schmidt gives an
orthonormal family. -/
theorem varyingGramSchmidtNormed_orthonormal
    {κ : Type*} [Fintype κ] [LinearOrder κ]
    [LocallyFiniteOrderBot κ] [WellFoundedLT κ]
    (family : κ → Base → Ambient)
    (x : Base)
    (hIndependent : LinearIndependent ℝ (fun k => family k x)) :
    Orthonormal ℝ (fun k => varyingGramSchmidtNormed family k x) := by
  exact InnerProductSpace.gramSchmidtNormed_orthonormal hIndependent

/-- Smooth projected normal seed family. -/
def projectedNormalFamily
    {ι κ : Type*} [Fintype ι]
    (tangentFrame : ι → Base → Ambient)
    (seed : κ → Base → Ambient)
    (k : κ)
    (x : Base) : Ambient :=
  normalProjector tangentFrame x (seed k x)

/-- The locus where projected normal seeds are linearly independent. -/
def normalIndependenceLocus
    {ι κ : Type*} [Fintype ι]
    (tangentFrame : ι → Base → Ambient)
    (seed : κ → Base → Ambient) : Set Base :=
  {x | LinearIndependent ℝ
    (fun k => projectedNormalFamily tangentFrame seed k x)}

/-- The projected-seed independence locus is open. -/
theorem normalIndependenceLocus_isOpen
    {ι κ : Type*} [Fintype ι] [Finite κ]
    (tangentFrame : ι → Base → Ambient)
    (seed : κ → Base → Ambient)
    (hTangent : ∀ i, ContDiff ℝ ∞ (tangentFrame i))
    (hSeed : ∀ k, ContDiff ℝ ∞ (seed k)) :
    IsOpen (normalIndependenceLocus tangentFrame seed) := by
  let projected : Base → κ → Ambient :=
    fun x k => projectedNormalFamily tangentFrame seed k x
  have hContinuous : Continuous projected := by
    apply continuous_pi
    intro k
    exact (projectedNormalSeed_contDiff tangentFrame seed hTangent hSeed k).continuous
  exact isOpen_setOf_linearIndependent.preimage hContinuous

/-- Normal orthonormal frame produced by projecting fixed smooth seeds and then
applying normalized Gram--Schmidt. -/
def smoothNormalFrame
    {ι κ : Type*} [Fintype ι] [LinearOrder κ]
    [LocallyFiniteOrderBot κ] [WellFoundedLT κ]
    (tangentFrame : ι → Base → Ambient)
    (seed : κ → Base → Ambient)
    (k : κ)
    (x : Base) : Ambient :=
  varyingGramSchmidtNormed
    (projectedNormalFamily tangentFrame seed) k x

/-- The constructed normal frame is smooth on the independence locus. -/
theorem smoothNormalFrame_contDiffOn
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]
    (tangentFrame : ι → Base → Ambient)
    (seed : κ → Base → Ambient)
    (hTangent : ∀ i, ContDiff ℝ ∞ (tangentFrame i))
    (hSeed : ∀ k, ContDiff ℝ ∞ (seed k)) :
    ∀ k, ContDiffOn ℝ ∞
      (smoothNormalFrame tangentFrame seed k)
      (normalIndependenceLocus tangentFrame seed) := by
  apply varyingGramSchmidtNormed_contDiffOn
  · intro k
    exact projectedNormalSeed_contDiff tangentFrame seed hTangent hSeed k
  · intro x hx
    exact hx

/-- The constructed normal frame is orthonormal at every point of the
independence locus. -/
theorem smoothNormalFrame_orthonormal
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]
    (tangentFrame : ι → Base → Ambient)
    (seed : κ → Base → Ambient)
    {x : Base}
    (hx : x ∈ normalIndependenceLocus tangentFrame seed) :
    Orthonormal ℝ (fun k => smoothNormalFrame tangentFrame seed k x) := by
  exact varyingGramSchmidtNormed_orthonormal
    (projectedNormalFamily tangentFrame seed) x hx

/-- Every Gram--Schmidt normal vector lies in the span of the projected normal
seed family. -/
theorem smoothNormalFrame_mem_projected_span
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]
    (tangentFrame : ι → Base → Ambient)
    (seed : κ → Base → Ambient)
    (x : Base)
    (k : κ) :
    smoothNormalFrame tangentFrame seed k x ∈
      Submodule.span ℝ
        (Set.range (fun j => projectedNormalFamily tangentFrame seed j x)) := by
  rw [← InnerProductSpace.span_gramSchmidtNormed_range]
  exact Submodule.subset_span (Set.mem_range_self k)

/-- The smooth normal frame is orthogonal to the tangent frame. -/
theorem tangent_inner_smoothNormalFrame_eq_zero
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]
    (tangentFrame : ι → Base → Ambient)
    (seed : κ → Base → Ambient)
    (hTangentOrthonormal : ∀ x,
      Orthonormal ℝ (fun i => tangentFrame i x))
    (x : Base)
    (i : ι)
    (k : κ) :
    inner ℝ (tangentFrame i x)
      (smoothNormalFrame tangentFrame seed k x) = 0 := by
  have hGenerators :
      Set.range (fun j => projectedNormalFamily tangentFrame seed j x) ⊆
        (ℝ ∙ tangentFrame i x)ᗮ := by
    rintro vector ⟨j, rfl⟩
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    exact inner_tangent_normalProjector_eq_zero
      tangentFrame x (hTangentOrthonormal x) i (seed j x)
  have hSpan :
      Submodule.span ℝ
          (Set.range (fun j => projectedNormalFamily tangentFrame seed j x)) ≤
        (ℝ ∙ tangentFrame i x)ᗮ :=
    Submodule.span_le.2 hGenerators
  have hMem := hSpan
    (smoothNormalFrame_mem_projected_span tangentFrame seed x k)
  exact Submodule.mem_orthogonal_singleton_iff_inner_left.mp hMem

/-- Combined tangent/normal adapted frame. -/
def combinedAdaptedFrame
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]
    (tangentFrame : ι → Base → Ambient)
    (seed : κ → Base → Ambient)
    (index : Sum ι κ)
    (x : Base) : Ambient :=
  Sum.elim (fun i => tangentFrame i x)
    (fun k => smoothNormalFrame tangentFrame seed k x) index

/-- Tangent and normal pieces combine to an orthonormal adapted family. -/
theorem combinedAdaptedFrame_orthonormal
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]
    (tangentFrame : ι → Base → Ambient)
    (seed : κ → Base → Ambient)
    (hTangentOrthonormal : ∀ x,
      Orthonormal ℝ (fun i => tangentFrame i x))
    {x : Base}
    (hx : x ∈ normalIndependenceLocus tangentFrame seed) :
    Orthonormal ℝ (fun index =>
      combinedAdaptedFrame tangentFrame seed index x) := by
  rw [orthonormal_iff_ite]
  intro first second
  cases first with
  | inl i =>
      cases second with
      | inl j =>
          simpa [combinedAdaptedFrame] using
            (orthonormal_iff_ite.mp (hTangentOrthonormal x) i j)
      | inr k =>
          simp [combinedAdaptedFrame,
            tangent_inner_smoothNormalFrame_eq_zero
              tangentFrame seed hTangentOrthonormal x i k]
  | inr k =>
      cases second with
      | inl i =>
          rw [show inner ℝ
              (smoothNormalFrame tangentFrame seed k x)
              (tangentFrame i x) =
            inner ℝ (tangentFrame i x)
              (smoothNormalFrame tangentFrame seed k x) by
            exact real_inner_comm _ _]
          simp [combinedAdaptedFrame,
            tangent_inner_smoothNormalFrame_eq_zero
              tangentFrame seed hTangentOrthonormal x i k]
      | inr l =>
          simpa [combinedAdaptedFrame] using
            (orthonormal_iff_ite.mp
              (smoothNormalFrame_orthonormal tangentFrame seed hx) k l)

/-- With the expected number of tangent and normal vectors, the adapted
orthonormal family spans the entire ambient space. -/
theorem combinedAdaptedFrame_span_eq_top
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]
    [FiniteDimensional ℝ Ambient]
    (tangentFrame : ι → Base → Ambient)
    (seed : κ → Base → Ambient)
    (hTangentOrthonormal : ∀ x,
      Orthonormal ℝ (fun i => tangentFrame i x))
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    {x : Base}
    (hx : x ∈ normalIndependenceLocus tangentFrame seed) :
    Submodule.span ℝ
        (Set.range (fun index =>
          combinedAdaptedFrame tangentFrame seed index x)) = ⊤ := by
  have hLI := (combinedAdaptedFrame_orthonormal
    tangentFrame seed hTangentOrthonormal hx).linearIndependent
  apply LinearIndependent.span_eq_top_of_card_eq_finrank' hLI
  simpa using hDimension

/-- Existence of a genuine open neighborhood carrying the explicit smooth
adapted frame. -/
theorem exists_open_smooth_adapted_frame
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [LinearOrder κ] [LocallyFiniteOrderBot κ] [WellFoundedLT κ]
    [FiniteDimensional ℝ Ambient]
    (tangentFrame : ι → Base → Ambient)
    (seed : κ → Base → Ambient)
    (hTangent : ∀ i, ContDiff ℝ ∞ (tangentFrame i))
    (hSeed : ∀ k, ContDiff ℝ ∞ (seed k))
    (hTangentOrthonormal : ∀ x,
      Orthonormal ℝ (fun i => tangentFrame i x))
    (hDimension : Fintype.card ι + Fintype.card κ = finrank ℝ Ambient)
    (x₀ : Base)
    (hIndependent : LinearIndependent ℝ
      (fun k => projectedNormalFamily tangentFrame seed k x₀)) :
    ∃ u : Set Base,
      IsOpen u ∧ x₀ ∈ u ∧
      (∀ k, ContDiffOn ℝ ∞
        (smoothNormalFrame tangentFrame seed k) u) ∧
      (∀ x ∈ u,
        Orthonormal ℝ (fun index =>
          combinedAdaptedFrame tangentFrame seed index x)) ∧
      (∀ x ∈ u,
        Submodule.span ℝ
          (Set.range (fun index =>
            combinedAdaptedFrame tangentFrame seed index x)) = ⊤) := by
  refine ⟨normalIndependenceLocus tangentFrame seed,
    normalIndependenceLocus_isOpen tangentFrame seed hTangent hSeed,
    hIndependent, ?_, ?_, ?_⟩
  · exact smoothNormalFrame_contDiffOn tangentFrame seed hTangent hSeed
  · intro x hx
    exact combinedAdaptedFrame_orthonormal
      tangentFrame seed hTangentOrthonormal hx
  · intro x hx
    exact combinedAdaptedFrame_span_eq_top
      tangentFrame seed hTangentOrthonormal hDimension hx

/-- S5.2 closure status. -/
structure SmoothAdaptedFrameStatus where
  projectedNormalSeedsConstructed : Prop
  independenceLocusOpen : Prop
  gramSchmidtSmoothOnIndependentLocus : Prop
  normalFrameOrthonormal : Prop
  tangentNormalCrossOrthogonality : Prop
  combinedFrameSpansAmbient : Prop
  openAdaptedFrameNeighborhoodConstructed : Prop
  tangentFrameDerivedFromImmersionChart : Prop
  normalSeedsDerivedFromAmbientBundleTrivialization : Prop
  manifoldLocalFramePackaged : Prop

/-- Full manifold-level S5.2 closure. -/
def smoothAdaptedFrameClosed (s : SmoothAdaptedFrameStatus) : Prop :=
  s.projectedNormalSeedsConstructed /\
  s.independenceLocusOpen /\
  s.gramSchmidtSmoothOnIndependentLocus /\
  s.normalFrameOrthonormal /\
  s.tangentNormalCrossOrthogonality /\
  s.combinedFrameSpansAmbient /\
  s.openAdaptedFrameNeighborhoodConstructed /\
  s.tangentFrameDerivedFromImmersionChart /\
  s.normalSeedsDerivedFromAmbientBundleTrivialization /\
  s.manifoldLocalFramePackaged

/-- The coordinate theorem still needs to be inserted into actual manifold
bundle trivializations. -/
theorem missing_manifold_packaging_blocks_full_S5_2
    (s : SmoothAdaptedFrameStatus)
    (hMissing : Not s.manifoldLocalFramePackaged) :
    Not (smoothAdaptedFrameClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2.2.2

end

end P0EFTJanusSmoothAdaptedFrame
end JanusFormal
