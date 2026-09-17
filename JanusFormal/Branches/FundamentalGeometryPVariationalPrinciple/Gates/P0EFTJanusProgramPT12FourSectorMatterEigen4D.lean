import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12DiagonalFourSectorRieszCommutation4D

/-! A matter eigenmode remains an eigenmode of a block-separated four-sector Riesz map. -/

namespace JanusFormal
namespace P0EFTJanusProgramPT12FourSectorMatterEigen4D

set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 1200000

noncomputable section

open scoped InnerProductSpace

variable {D A M L : Type*}
  [NormedAddCommGroup D] [InnerProductSpace Real D]
  [NormedAddCommGroup A] [InnerProductSpace Real A]
  [NormedAddCommGroup M] [InnerProductSpace Real M]
  [NormedAddCommGroup L] [InnerProductSpace Real L]

private abbrev FourGraph := WithLp 2
  (D × WithLp 2 (A × WithLp 2 (M × L)))

def pureMatter (m : M) : FourGraph (D := D) (A := A) (M := M) (L := L) :=
  WithLp.toLp 2 (0, WithLp.toLp 2 (0, WithLp.toLp 2 (m, 0)))

theorem pureMatter_eigen_of_block_form
    (B : FourGraph (D := D) (A := A) (M := M) (L := L) →L[Real]
      FourGraph (D := D) (A := A) (M := M) (L := L) →L[Real] Real)
    (R : FourGraph (D := D) (A := A) (M := M) (L := L) →L[Real]
      FourGraph (D := D) (A := A) (M := M) (L := L))
    (bD : D →L[Real] D →L[Real] Real)
    (bA : A →L[Real] A →L[Real] Real)
    (bM : M →L[Real] M →L[Real] Real)
    (bL : L →L[Real] L →L[Real] Real)
    (rM : M →L[Real] M)
    (hB : ∀ x y,
      B x y = bD x.fst y.fst + bA x.snd.fst y.snd.fst +
        bM x.snd.snd.fst y.snd.snd.fst +
        bL x.snd.snd.snd y.snd.snd.snd)
    (hR : ∀ x y, inner Real (R x) y = B x y)
    (hrM : ∀ u v, inner Real (rM u) v = bM u v)
    (m : M) (μ : Real) (hm : rM m = μ • m) :
    R (pureMatter (D := D) (A := A) (L := L) m) =
      μ • pureMatter (D := D) (A := A) (L := L) m := by
  apply ext_inner_right Real
  intro y
  calc
    inner Real (R (pureMatter (D := D) (A := A) (L := L) m)) y =
        B (pureMatter (D := D) (A := A) (L := L) m) y := hR _ _
    _ = bM m y.snd.snd.fst := by
      rw [hB]
      simp [pureMatter]
    _ = inner Real (μ • m) y.snd.snd.fst := by rw [← hm, hrM]
    _ = inner Real (μ • pureMatter (D := D) (A := A) (L := L) m) y := by
      simp [pureMatter, WithLp.prod_inner_apply]

end
end P0EFTJanusProgramPT12FourSectorMatterEigen4D
end JanusFormal
