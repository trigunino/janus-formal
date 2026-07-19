import Mathlib.Data.Set.Basic

/-! # MF-REF-001: pair-covering refinement and uniqueness of pair data -/

namespace Janus.ProgramM

variable {α ι V : Type*}

/-- Every ordered pair is eventually jointly visible in one patch. -/
def PairCovered (patch : ι → Set α) : Prop :=
  ∀ x y, ∃ i, x ∈ patch i ∧ y ∈ patch i

/-- Two global pair assignments have identical restrictions to every patch. -/
def LocallyAgree (patch : ι → Set α) (f g : α → α → V) : Prop :=
  ∀ i x, x ∈ patch i → ∀ y, y ∈ patch i → f x y = g x y

theorem pairCovered_pairData_unique {patch : ι → Set α}
    (hcover : PairCovered patch) {f g : α → α → V}
    (hlocal : LocallyAgree patch f g) : f = g := by
  funext x y
  obtain ⟨i, hx, hy⟩ := hcover x y
  exact hlocal i x hx y hy

theorem not_pairCovered_pairData_ambiguous [DecidableEq α]
    {patch : ι → Set α} (hcover : ¬ PairCovered patch) :
    ∃ f g : α → α → Bool, LocallyAgree patch f g ∧ f ≠ g := by
  rw [PairCovered] at hcover
  push Not at hcover
  obtain ⟨a, b, hab⟩ := hcover
  let f : α → α → Bool := fun _ _ ↦ false
  let g : α → α → Bool := fun x y ↦ decide (x = a ∧ y = b)
  refine ⟨f, g, ?_, ?_⟩
  · intro i x hx y hy
    simp only [f, g, Bool.false_eq, decide_eq_false_iff_not]
    intro h
    exact hab i (h.1 ▸ hx) (h.2 ▸ hy)
  · intro hfg
    have := congrFun (congrFun hfg a) b
    simp [f, g] at this

theorem pairCovered_iff_pairData_unique [DecidableEq α]
    (patch : ι → Set α) :
    PairCovered patch ↔
      ∀ f g : α → α → Bool, LocallyAgree patch f g → f = g := by
  constructor
  · intro h f g
    exact pairCovered_pairData_unique h
  · intro h
    by_contra hcover
    obtain ⟨f, g, hlocal, hne⟩ := not_pairCovered_pairData_ambiguous hcover
    exact hne (h f g hlocal)

end Janus.ProgramM
