import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12ClosedNullPMapQuotient4D

/-! A Hilbert quotient pairing determines an actual unbounded operator intertwiner. -/
namespace JanusFormal.P0EFTJanusProgramPT12QuotientPairingIntertwiner4D
set_option autoImplicit false
noncomputable section
open Set
open P0EFTJanusProgramPT12ClosedNullPMapQuotient4D
open P0EFTJanusProgramPT12ClosedNullQuotient4D
variable {E V : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace Real E] [CompleteSpace E]
variable [NormedAddCommGroup V] [InnerProductSpace Real V] [CompleteSpace V]

theorem quotientFirst_adjoint_right_inverse
    (N : Submodule Real E) [IsClosed (N : Set E)]
    (Q : WithLp 2 (E × V) →L[Real] WithLp 2 ((E ⧸ N) × V))
    (hQ : ∀ x, Q x = WithLp.toLp 2 (N.mkQ x.fst, x.snd))
    (z : WithLp 2 ((E ⧸ N) × V)) : Q (Q.adjoint z) = z := by
  have hAdj : Q.adjoint z = WithLp.toLp 2 (quotientLift N z.fst, z.snd) := by
    apply ext_inner_right Real
    intro y
    rw [Q.adjoint_inner_left, hQ]
    change inner Real z.fst (N.mkQ y.fst) + inner Real z.snd y.snd =
      inner Real (quotientLift N z.fst) y.fst + inner Real z.snd y.snd
    have h := inner_mk_of_left_orthogonal N (quotientLift N z.fst) y.fst
      (N.quotientEquivOrthogonal z.fst).property
    rw [mk_quotientLift] at h
    exact congrArg (fun t => t + inner Real z.snd y.snd) h
  rw [hAdj, hQ]
  apply WithLp.ofLp_injective 2
  exact Prod.ext (mk_quotientLift N z.fst) rfl

variable {K : Type*} [NormedAddCommGroup K] [InnerProductSpace Real K] [CompleteSpace K]

theorem operator_intertwining_of_pairing
    (A : E →ₗ.[Real] E) (B : K →ₗ.[Real] K) (Q : E →L[Real] K)
    (hQ : ∀ z, Q (Q.adjoint z) = z)
    (hDomain : ∀ x ∈ A.domain, Q x ∈ B.domain)
    (hPair : ∀ (x : A.domain) (y : E),
      inner Real (B ⟨Q x.val, hDomain x.val x.property⟩) (Q y) = inner Real (A x) y)
    (x : A.domain) : B ⟨Q x.val, hDomain x.val x.property⟩ = Q (A x) := by
  have hAdj : Q.adjoint (B ⟨Q x.val, hDomain x.val x.property⟩) = A x := by
    apply ext_inner_right Real
    intro y
    rw [Q.adjoint_inner_left]
    exact hPair x y
  exact (hQ _).symm.trans (congrArg Q hAdj)

end
end JanusFormal.P0EFTJanusProgramPT12QuotientPairingIntertwiner4D
