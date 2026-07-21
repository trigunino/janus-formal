import JanusFormal.Foundations.ProgramMConfigurationGroupoid

/-!
# MF-OBS-001: scalar observables on the relational configuration groupoid

An observable is admissible when exact relational isomorphisms cannot change
its value.  This supplies an interface, not a preferred physical action.
-/

namespace JanusFormal.ProgramM

universe u v w

/-- A family of relational configurations, possibly with different carriers. -/
structure ConfigurationFamily (ι : Type u) where
  Obj : ι → Type v
  Rel : ι → Type w
  system : (i : ι) → RelationalSystem (Obj i) (Rel i)

/-- A scalar assignment descends to the configuration groupoid exactly when it
is constant along every relational isomorphism. -/
def GroupoidInvariant
    {ι : Type u} (C : ConfigurationFamily ι) {Scalar : Type*}
    (value : ι → Scalar) : Prop :=
  ∀ i j, RelationalSystemIso (C.system i) (C.system j) → value i = value j

theorem groupoidInvariant_refl
    {ι : Type u} (C : ConfigurationFamily ι) {Scalar : Type*}
    (value : ι → Scalar) (h : GroupoidInvariant C value) (i : ι) :
    value i = value i :=
  h i i (RelationalSystemIso.refl (C.system i))

theorem groupoidInvariant_symm
    {ι : Type u} (C : ConfigurationFamily ι) {Scalar : Type*}
    (value : ι → Scalar) (h : GroupoidInvariant C value)
    {i j : ι} (e : RelationalSystemIso (C.system i) (C.system j)) :
    value j = value i :=
  h j i (RelationalSystemIso.symm e)

theorem groupoidInvariant_trans
    {ι : Type u} (C : ConfigurationFamily ι) {Scalar : Type*}
    (value : ι → Scalar) (h : GroupoidInvariant C value)
    {i j k : ι}
    (e : RelationalSystemIso (C.system i) (C.system j))
    (f : RelationalSystemIso (C.system j) (C.system k)) :
    value i = value k :=
  h i k (RelationalSystemIso.trans e f)

/-- Applying any scalar map to an invariant observable preserves invariance. -/
theorem GroupoidInvariant.comp
    {ι : Type u} (C : ConfigurationFamily ι) {Scalar Target : Type*}
    {value : ι → Scalar} (h : GroupoidInvariant C value) (f : Scalar → Target) :
    GroupoidInvariant C (fun i ↦ f (value i)) := by
  intro i j e
  exact congrArg f (h i j e)

/-- Constant scalar assignments are admissible but contain no configuration
information. -/
theorem groupoidInvariant_const
    {ι : Type u} (C : ConfigurationFamily ι) {Scalar : Type*} (c : Scalar) :
    GroupoidInvariant C (fun _ ↦ c) := by
  intro _ _ _
  rfl

/-- Groupoid invariance alone never selects a unique scalar functional on a
nonempty configuration family: the two Boolean constants are distinct and both
admissible. -/
theorem groupoidInvariance_does_not_select_unique
    {ι : Type u} (C : ConfigurationFamily ι) (i : ι) :
    ∃ first second : ι → Bool,
      GroupoidInvariant C first ∧ GroupoidInvariant C second ∧ first ≠ second := by
  refine ⟨fun _ ↦ false, fun _ ↦ true,
    groupoidInvariant_const C false, groupoidInvariant_const C true, ?_⟩
  intro h
  have := congrFun h i
  cases this

/-- If an isomorphism identifies two configurations but proposed values differ,
the proposed observable is not admissible. -/
theorem not_groupoidInvariant_of_iso_value_ne
    {ι : Type u} (C : ConfigurationFamily ι) {Scalar : Type*}
    (value : ι → Scalar) {i j : ι}
    (e : RelationalSystemIso (C.system i) (C.system j))
    (hne : value i ≠ value j) :
    ¬ GroupoidInvariant C value := by
  intro h
  exact hne (h i j e)

end JanusFormal.ProgramM
