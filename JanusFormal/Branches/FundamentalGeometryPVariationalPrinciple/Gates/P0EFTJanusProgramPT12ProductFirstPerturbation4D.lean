import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ProductSelfAdjoint4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12BoundedSelfAdjointPerturbation4D

/-! A symmetric perturbation killing the second factor acts only on the first factor. -/
namespace JanusFormal.P0EFTJanusProgramPT12ProductFirstPerturbation4D
set_option autoImplicit false
noncomputable section
open P0EFTJanusProgramPT12ProductClosedOperator4D
open P0EFTJanusProgramPT12BoundedSelfAdjointPerturbation4D
variable {H K : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
variable [NormedAddCommGroup K] [InnerProductSpace Real K] [CompleteSpace K]

def firstInclusion : H →L[Real] WithLp 2 (H × K) :=
  (WithLp.prodContinuousLinearEquiv 2 Real H K).symm.toContinuousLinearMap.comp
    ((ContinuousLinearMap.id Real H).prod (0 : H →L[Real] K))

def firstCompression (B : WithLp 2 (H × K) →L[Real] WithLp 2 (H × K)) : H →L[Real] H :=
  (WithLp.fstL 2 Real H K).comp (B.comp firstInclusion)

variable (B : WithLp 2 (H × K) →L[Real] WithLp 2 (H × K))
variable (hSym : IsSelfAdjoint B) (hZero : ∀ k : K, B (WithLp.toLp 2 (0, k)) = 0)

include hSym hZero in
theorem firstPerturbation_snd_zero (x : WithLp 2 (H × K)) : (B x).snd = 0 := by
  apply ext_inner_right Real
  intro k
  have h := hSym.isSymmetric x (WithLp.toLp 2 (0, k))
  change inner Real (B x) (WithLp.toLp 2 (0, k)) = inner Real x (B (WithLp.toLp 2 (0, k))) at h
  rw [hZero] at h
  simpa only [WithLp.prod_inner_apply, WithLp.ofLp_fst, WithLp.ofLp_snd,
    inner_zero_right, inner_zero_left, zero_add] using h

include hSym hZero in
theorem firstPerturbation_apply (x : WithLp 2 (H × K)) :
    B x = WithLp.toLp 2 (firstCompression B x.fst, 0) := by
  have hSplit : x = firstInclusion (K := K) x.fst + WithLp.toLp 2 (0, x.snd) := by
    apply WithLp.ofLp_injective 2
    exact Prod.ext (add_zero _).symm (zero_add _).symm
  have hFirst : B x = B (firstInclusion (K := K) x.fst) := by
    calc
      B x = B (firstInclusion (K := K) x.fst + WithLp.toLp 2 (0, x.snd)) := congrArg B hSplit
      _ = B (firstInclusion (K := K) x.fst) := by rw [map_add, hZero, add_zero]
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change (B x).fst = (B (firstInclusion (K := K) x.fst)).fst
    exact congrArg WithLp.fst hFirst
  · exact firstPerturbation_snd_zero B hSym hZero x

include hSym in
theorem firstCompression_selfAdjoint : IsSelfAdjoint (firstCompression B) := by
  apply LinearMap.IsSymmetric.isSelfAdjoint
  intro x y
  change inner Real (B (firstInclusion (K := K) x)).fst y = inner Real x (B (firstInclusion (K := K) y)).fst
  have h := hSym.isSymmetric (firstInclusion (K := K) x) (firstInclusion (K := K) y)
  change inner Real (B (firstInclusion (K := K) x)).fst y + inner Real (B (firstInclusion (K := K) x)).snd 0 =
    inner Real x (B (firstInclusion (K := K) y)).fst + inner Real 0 (B (firstInclusion (K := K) y)).snd at h
  simpa only [inner_zero_right, inner_zero_left, add_zero] using h

include hSym hZero in
/-- Equality of complete graphs and domains, not just a smooth pairing identity. -/
theorem product_firstPerturbation (A : H →ₗ.[Real] H) (C : K →ₗ.[Real] K) :
    boundedPerturbation (productOperator A C) B =
      productOperator (boundedPerturbation A (firstCompression B)) C := by
  apply LinearPMap.eq_of_eq_graph
  ext pair
  rcases pair with ⟨input, output⟩
  rw [boundedPerturbation_mem_graph_iff, productOperator_mem_graph_iff,
    productOperator_mem_graph_iff, boundedPerturbation_mem_graph_iff,
    firstPerturbation_apply B hSym hZero]
  change ((input.fst, output.fst - firstCompression B input.fst) ∈ A.graph ∧
    (input.snd, output.snd - 0) ∈ C.graph) ↔ _
  rw [sub_zero]

end
end JanusFormal.P0EFTJanusProgramPT12ProductFirstPerturbation4D
