import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPT12NullQuotientFredholm4D
import Mathlib.Analysis.Normed.Operator.Banach

/-! Finite observations turn an a priori estimate into closed range and finite kernel. -/
namespace JanusFormal.P0EFTJanusProgramPT12FiniteObservationEstimate4D
set_option autoImplicit false
noncomputable section
open Set

private theorem bounded_finite_observation
    {X H F : Type*} [NormedAddCommGroup X] [NormedSpace Real X] [CompleteSpace X]
    [NormedAddCommGroup H] [NormedSpace Real H]
    [NormedAddCommGroup F] [NormedSpace Real F] [FiniteDimensional Real F]
    (f : X →L[Real] H) (j : X →L[Real] F) (C : NNReal)
    (hBound : ∀ x, ‖x‖ ≤ C * ‖(f.prod j) x‖) :
    IsClosed (LinearMap.range f.toLinearMap : Set H) ∧
      FiniteDimensional Real (LinearMap.ker f.toLinearMap) := by
  have hAnti := (f.prod j).antilipschitz_of_bound hBound
  have hClosed : IsClosed (LinearMap.range (f.prod j).toLinearMap : Set (H × F)) :=
    hAnti.isClosed_range (f.prod j).uniformContinuous
  let vertical := LinearMap.range (LinearMap.inr Real H F)
  have hSum := Submodule.isClosed_sup_finiteDimensional _ vertical hClosed
  have hSlice : (LinearMap.range f.toLinearMap : Set H) =
      (fun y : H => (y, (0 : F))) ⁻¹'
        ((LinearMap.range (f.prod j).toLinearMap ⊔ vertical : Submodule Real (H × F)) : Set (H × F)) := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Submodule.mem_sup.mpr ⟨(f x, j x), ⟨x, rfl⟩,
        (0, -j x), ⟨-j x, rfl⟩, by simp⟩
    · intro h
      obtain ⟨a, ⟨x, rfl⟩, b, ⟨z, rfl⟩, heq⟩ := Submodule.mem_sup.mp h
      exact ⟨x, by simpa using congrArg Prod.fst heq⟩
  refine ⟨hSlice ▸ hSum.preimage (by fun_prop), ?_⟩
  apply FiniteDimensional.of_injective (j.toLinearMap.comp (LinearMap.ker f.toLinearMap).subtype)
  intro x y h
  apply Subtype.ext
  apply hAnti.injective
  exact Prod.ext (x.property.trans y.property.symm) h

variable {H F : Type*} [NormedAddCommGroup H] [InnerProductSpace Real H] [CompleteSpace H]
variable [NormedAddCommGroup F] [NormedSpace Real F] [FiniteDimensional Real F]

/-- The observation is finite dimensional; neither a finite kernel nor a closed range is assumed. -/
theorem closedOperator_finite_observation (A : H →ₗ.[Real] H) (hClosed : A.IsClosed)
    (observation : H →L[Real] F) (C : NNReal)
    (hEstimate : ∀ u : A.domain, ‖(u : H)‖ ≤ C * (‖A u‖ + ‖observation u‖)) :
    IsClosed (LinearMap.range A.toFun : Set H) ∧ FiniteDimensional Real (LinearMap.ker A.toFun) := by
  letI : CompleteSpace A.graph := hClosed.completeSpace_coe
  let input : A.graph →L[Real] H := (ContinuousLinearMap.fst Real H H).comp A.graph.subtypeL
  let output : A.graph →L[Real] H := (ContinuousLinearMap.snd Real H H).comp A.graph.subtypeL
  let observed := observation.comp input
  have hBound (v : A.graph) : ‖v‖ ≤ (2 * C + 1 : NNReal) * ‖(output.prod observed) v‖ := by
    obtain ⟨u, hu, hAu⟩ := A.mem_graph_iff.mp v.property
    have h := hEstimate u
    rw [hu, hAu] at h
    change max ‖v.val.1‖ ‖v.val.2‖ ≤
      ((2 * C + 1 : NNReal) : Real) * max ‖v.val.2‖ ‖observation v.val.1‖
    simp only [NNReal.coe_add, NNReal.coe_mul, NNReal.coe_ofNat, NNReal.coe_one]
    have h1 := le_max_left ‖v.val.2‖ ‖observation v.val.1‖
    have h2 := le_max_right ‖v.val.2‖ ‖observation v.val.1‖
    have h0 := C.coe_nonneg
    have hn := norm_nonneg v.val.2
    apply max_le <;> nlinarith
  obtain ⟨hRange, _⟩ := bounded_finite_observation output observed (2 * C + 1) hBound
  have hRanges : LinearMap.range output.toLinearMap = LinearMap.range A.toFun := by
    ext y
    constructor
    · rintro ⟨v, rfl⟩
      obtain ⟨u, _, hAu⟩ := A.mem_graph_iff.mp v.property
      exact ⟨u, hAu⟩
    · rintro ⟨u, rfl⟩
      exact ⟨⟨(u.val, A u), A.mem_graph u⟩, rfl⟩
  refine ⟨hRanges ▸ hRange, ?_⟩
  let observeKernel : LinearMap.ker A.toFun →ₗ[Real] F :=
    observation.toLinearMap.comp (A.domain.subtype.comp (LinearMap.ker A.toFun).subtype)
  apply FiniteDimensional.of_injective observeKernel
  intro x y hxy
  have h := hEstimate (x.val - y.val)
  have hImage : A (x.val - y.val) = 0 := by
    change A.toFun (x.val - y.val) = 0
    rw [map_sub, show A.toFun x.val = 0 from x.property, show A.toFun y.val = 0 from y.property, sub_self]
  have hObs : observation ((x.val - y.val : A.domain) : H) = 0 := by
    change observation ((x.val : H) - (y.val : H)) = 0
    rw [map_sub]
    exact sub_eq_zero.mpr hxy
  simp only [hImage, hObs, norm_zero, add_zero, mul_zero] at h
  apply Subtype.ext
  apply Subtype.ext
  exact sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm h (norm_nonneg _)))

theorem selfAdjoint_fredholm_of_finite_observation (A : H →ₗ.[Real] H) (hSelf : IsSelfAdjoint A)
    (observation : H →L[Real] F) (C : NNReal)
    (hEstimate : ∀ u : A.domain, ‖(u : H)‖ ≤ C * (‖A u‖ + ‖observation u‖)) :
    IsClosed (LinearMap.range A.toFun : Set H) ∧ FiniteDimensional Real (LinearMap.ker A.toFun) ∧
      FiniteDimensional Real (H ⧸ LinearMap.range A.toFun) :=
  (P0EFTJanusProgramPT12NullQuotientFredholm4D.selfAdjoint_fredholm_iff A hSelf).mpr
    (closedOperator_finite_observation A hSelf.isClosed observation C hEstimate)

end
end JanusFormal.P0EFTJanusProgramPT12FiniteObservationEstimate4D
