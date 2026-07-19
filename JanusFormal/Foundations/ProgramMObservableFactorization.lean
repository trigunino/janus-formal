import JanusFormal.Foundations.ProgramMDecoratedSkeleton

/-!
# MF-OBS-000: safe observables under compression

An observable may be computed from compressed data exactly when it is constant
on every pair of primitive states identified by the compression.
-/

namespace JanusFormal.ProgramM

open Function

universe u v w x

/-- The safety condition for a proposed compression, exposed under a
Program-M-specific name. -/
def CompressionSafe {A : Type u} {C : Type v} {O : Type w}
    (compress : A → C) (observable : A → O) : Prop :=
  observable.FactorsThrough compress

theorem compressionSafe_iff_constant_on_collisions
    {A : Type u} {C : Type v} {O : Type w}
    (compress : A → C) (observable : A → O) :
    CompressionSafe compress observable ↔
      ∀ ⦃a b⦄, compress a = compress b → observable a = observable b :=
  Iff.rfl

/-- With a nonempty output type, safety is equivalent to the existence of an
observable defined entirely on compressed states. -/
theorem compressionSafe_iff_exists_downstream
    {A : Type u} {C : Type v} {O : Type w} [Nonempty O]
    (compress : A → C) (observable : A → O) :
    CompressionSafe compress observable ↔
      ∃ downstream : C → O, observable = downstream ∘ compress := by
  exact factorsThrough_iff observable

/-- One collision with different observable values is a complete no-go
witness for that observable/compression pair. -/
theorem not_compressionSafe_of_collision
    {A : Type u} {C : Type v} {O : Type w}
    {compress : A → C} {observable : A → O} {a b : A}
    (hCompression : compress a = compress b)
    (hObservable : observable a ≠ observable b) :
    ¬ CompressionSafe compress observable := by
  intro hSafe
  exact hObservable (hSafe hCompression)

/-- An observable factors through the bare skeleton exactly when it is constant
on every mutual-reachability component. -/
theorem factorsThrough_causalClass_iff
    {Obj : Type u} {Rel : Type v} {O : Type w}
    (S : RelationalSystem Obj Rel) (q : Rel) (observable : Obj → O) :
    CompressionSafe (causalClass S q) observable ↔
      ∀ ⦃x y : Obj⦄,
        (reachability S q x y ∧ reachability S q y x) → observable x = observable y := by
  constructor
  · intro hSafe x y hMutual
    exact hSafe ((causalClass_eq_iff_mutual_reachability S q x y).2 hMutual)
  · intro hConstant x y hClass
    exact hConstant ((causalClass_eq_iff_mutual_reachability S q x y).1 hClass)

/-- The lossless fiber decomposition is safe for every observable. -/
theorem every_observable_factorsThrough_causalFiberDecomposition
    {Obj : Type u} {Rel : Type v} {O : Type w}
    (S : RelationalSystem Obj Rel) (q : Rel) (observable : Obj → O) :
    CompressionSafe (causalFiberDecompositionEquiv S q) observable :=
  (causalFiberDecompositionEquiv S q).injective.factorsThrough observable

end JanusFormal.ProgramM
