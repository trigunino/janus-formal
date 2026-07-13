import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.Normed.Module.FiniteDimension
import JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusSecondFundamentalResidualEquivariance

namespace JanusFormal
namespace P0EFTJanusSmoothProjectorField

set_option autoImplicit false

noncomputable section

open scoped ContDiff InnerProductSpace
open Set

universe u v

variable {Base : Type u}
variable {Ambient : Type v}
variable [NormedAddCommGroup Base]
variable [NormedSpace ℝ Base]
variable [NormedAddCommGroup Ambient]
variable [InnerProductSpace ℝ Ambient]

/-- Tangent projector determined by a finite family of vectors. When the family
is orthonormal this is the orthogonal projector onto its span. -/
def tangentProjector
    {ι : Type*} [Fintype ι]
    (frame : ι → Base → Ambient)
    (x : Base)
    (vector : Ambient) : Ambient :=
  ∑ i, inner ℝ (frame i x) vector • frame i x

/-- Complementary projector. -/
def normalProjector
    {ι : Type*} [Fintype ι]
    (frame : ι → Base → Ambient)
    (x : Base)
    (vector : Ambient) : Ambient :=
  vector - tangentProjector frame x vector

/-- Joint smoothness of the tangent projector in the base point and vector
argument. This is the coordinate form of a smooth field of bundle
endomorphisms. -/
theorem tangentProjector_contDiff
    {ι : Type*} [Fintype ι]
    (frame : ι → Base → Ambient)
    (hSmooth : ∀ i, ContDiff ℝ ∞ (frame i)) :
    ContDiff ℝ ∞
      (fun point : Base × Ambient =>
        tangentProjector frame point.1 point.2) := by
  classical
  unfold tangentProjector
  apply ContDiff.sum
  intro i hi
  have hFrame : ContDiff ℝ ∞ (fun point : Base × Ambient => frame i point.1) :=
    (hSmooth i).comp contDiff_fst
  have hInner : ContDiff ℝ ∞
      (fun point : Base × Ambient => inner ℝ (frame i point.1) point.2) :=
    hFrame.inner ℝ contDiff_snd
  exact hInner.smul hFrame

/-- Joint smoothness of the complementary normal projector. -/
theorem normalProjector_contDiff
    {ι : Type*} [Fintype ι]
    (frame : ι → Base → Ambient)
    (hSmooth : ∀ i, ContDiff ℝ ∞ (frame i)) :
    ContDiff ℝ ∞
      (fun point : Base × Ambient =>
        normalProjector frame point.1 point.2) := by
  exact contDiff_snd.sub (tangentProjector_contDiff frame hSmooth)

/-- Smoothness of the projector field after evaluation on any smooth vector
field. -/
theorem tangentProjector_apply_contDiff
    {ι : Type*} [Fintype ι]
    (frame : ι → Base → Ambient)
    (vector : Base → Ambient)
    (hFrame : ∀ i, ContDiff ℝ ∞ (frame i))
    (hVector : ContDiff ℝ ∞ vector) :
    ContDiff ℝ ∞ (fun x => tangentProjector frame x (vector x)) := by
  exact (tangentProjector_contDiff frame hFrame).comp
    (contDiff_id.prodMk hVector)

/-- Smoothness of the normal projector field after evaluation on a smooth vector
field. -/
theorem normalProjector_apply_contDiff
    {ι : Type*} [Fintype ι]
    (frame : ι → Base → Ambient)
    (vector : Base → Ambient)
    (hFrame : ∀ i, ContDiff ℝ ∞ (frame i))
    (hVector : ContDiff ℝ ∞ vector) :
    ContDiff ℝ ∞ (fun x => normalProjector frame x (vector x)) := by
  exact (normalProjector_contDiff frame hFrame).comp
    (contDiff_id.prodMk hVector)

/-- The tangent projector fixes every member of an orthonormal frame. -/
theorem tangentProjector_frame
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (frame : ι → Base → Ambient)
    (x : Base)
    (hOrthonormal : Orthonormal ℝ (fun i => frame i x))
    (j : ι) :
    tangentProjector frame x (frame j x) = frame j x := by
  classical
  simp only [tangentProjector]
  rw [← one_smul ℝ (frame j x)]
  apply Finset.sum_eq_single j
  · intro i hi hij
    rw [hOrthonormal.inner_eq_zero hij]
    simp
  · intro hj
    exact (hj (Finset.mem_univ j)).elim
  · rw [inner_self_eq_norm_sq_to_K, hOrthonormal.norm_eq_one]
    norm_num

/-- The normal projector kills every member of the tangent orthonormal frame. -/
theorem normalProjector_frame
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (frame : ι → Base → Ambient)
    (x : Base)
    (hOrthonormal : Orthonormal ℝ (fun i => frame i x))
    (j : ι) :
    normalProjector frame x (frame j x) = 0 := by
  rw [normalProjector, tangentProjector_frame frame x hOrthonormal j, sub_self]

/-- The two projectors sum to the identity by construction. -/
theorem tangent_add_normal_projector
    {ι : Type*} [Fintype ι]
    (frame : ι → Base → Ambient)
    (x : Base)
    (vector : Ambient) :
    tangentProjector frame x vector + normalProjector frame x vector = vector := by
  simp [normalProjector]

/-- Tangent projection is idempotent for an orthonormal frame. -/
theorem tangentProjector_idempotent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (frame : ι → Base → Ambient)
    (x : Base)
    (hOrthonormal : Orthonormal ℝ (fun i => frame i x))
    (vector : Ambient) :
    tangentProjector frame x (tangentProjector frame x vector) =
      tangentProjector frame x vector := by
  classical
  simp only [tangentProjector]
  rw [Finset.sum_apply]
  simp_rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [map_smul, tangentProjector_frame frame x hOrthonormal i]

/-- The complementary normal projection is idempotent as well. -/
theorem normalProjector_idempotent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (frame : ι → Base → Ambient)
    (x : Base)
    (hOrthonormal : Orthonormal ℝ (fun i => frame i x))
    (vector : Ambient) :
    normalProjector frame x (normalProjector frame x vector) =
      normalProjector frame x vector := by
  simp only [normalProjector]
  rw [show tangentProjector frame x
      (vector - tangentProjector frame x vector) = 0 by
    unfold tangentProjector
    simp_rw [inner_sub_right, Finset.sum_sub_distrib]
    rw [tangentProjector_idempotent frame x hOrthonormal]
    simp]
  simp

/-- Projecting smooth seed vector fields to the normal complement yields smooth
normal sections. -/
theorem projectedNormalSeed_contDiff
    {ι κ : Type*} [Fintype ι]
    (tangentFrame : ι → Base → Ambient)
    (seed : κ → Base → Ambient)
    (hTangent : ∀ i, ContDiff ℝ ∞ (tangentFrame i))
    (hSeed : ∀ k, ContDiff ℝ ∞ (seed k)) :
    ∀ k, ContDiff ℝ ∞
      (fun x => normalProjector tangentFrame x (seed k x)) := by
  intro k
  exact normalProjector_apply_contDiff tangentFrame (seed k) hTangent (hSeed k)

/-- Linear independence of projected normal seeds persists on an open
neighborhood of any base point where it holds. -/
theorem eventually_projectedNormalSeed_linearIndependent
    {ι κ : Type*} [Fintype ι] [Finite κ]
    (tangentFrame : ι → Base → Ambient)
    (seed : κ → Base → Ambient)
    (hTangent : ∀ i, ContDiff ℝ ∞ (tangentFrame i))
    (hSeed : ∀ k, ContDiff ℝ ∞ (seed k))
    (x₀ : Base)
    (hIndependent : LinearIndependent ℝ
      (fun k => normalProjector tangentFrame x₀ (seed k x₀))) :
    ∀ᶠ x in 𝓝 x₀,
      LinearIndependent ℝ
        (fun k => normalProjector tangentFrame x (seed k x)) := by
  let projected : Base → κ → Ambient :=
    fun x k => normalProjector tangentFrame x (seed k x)
  have hContinuous : Continuous projected := by
    rw [continuous_pi]
    intro k
    exact (projectedNormalSeed_contDiff tangentFrame seed hTangent hSeed k).continuous
  have hOpen : IsOpen {family : κ → Ambient | LinearIndependent ℝ family} :=
    isOpen_setOf_linearIndependent
  exact hContinuous.continuousAt
    (hOpen.mem_nhds hIndependent)

/-- S5.1 closure status. -/
structure SmoothProjectorStatus where
  finiteSmoothTangentFrameProvided : Prop
  tangentProjectorJointlySmooth : Prop
  normalProjectorJointlySmooth : Prop
  projectorIdentitiesProved : Prop
  projectedNormalSeedsSmooth : Prop
  localIndependencePersistenceProved : Prop
  tangentFrameDerivedFromImmersionDifferential : Prop
  manifoldBundleProjectorsConstructed : Prop

/-- Full manifold-level S5.1 closure. -/
def smoothProjectorClosed (s : SmoothProjectorStatus) : Prop :=
  s.finiteSmoothTangentFrameProvided /\
  s.tangentProjectorJointlySmooth /\
  s.normalProjectorJointlySmooth /\
  s.projectorIdentitiesProved /\
  s.projectedNormalSeedsSmooth /\
  s.localIndependencePersistenceProved /\
  s.tangentFrameDerivedFromImmersionDifferential /\
  s.manifoldBundleProjectorsConstructed

/-- Coordinate smoothness does not alone construct the projectors as morphisms
of the actual tangent and ambient manifold bundles. -/
theorem missing_bundle_instantiation_blocks_full_S5_1
    (s : SmoothProjectorStatus)
    (hMissing : Not s.manifoldBundleProjectorsConstructed) :
    Not (smoothProjectorClosed s) := by
  intro hClosed
  exact hMissing hClosed.2.2.2.2.2.2.2

end

end P0EFTJanusSmoothProjectorField
end JanusFormal
