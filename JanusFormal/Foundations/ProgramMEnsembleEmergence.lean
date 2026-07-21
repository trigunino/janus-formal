import JanusFormal.Foundations.ProgramMFiniteIdentifiabilityNoGo
import Mathlib.Topology.Instances.ENNReal.Lemmas

/-!
# MF-ENS-001: exchangeable projective laws and held-out asymptotic emergence

No geometry is built into the sample type: it is only a finite partial order.
-/

namespace JanusFormal.ProgramM

open Filter Topology

/-- A partial order on `Fin n`, bundled without assigning physical meaning. -/
structure FinitePoset (n : ℕ) where
  rel : Fin n → Fin n → Prop
  refl : ∀ x, rel x x
  antisymm : ∀ {x y}, rel x y → rel y x → x = y
  trans : ∀ {x y z}, rel x y → rel y z → rel x z

namespace FinitePoset

def relabel {n : ℕ} (P : FinitePoset n) (e : Equiv.Perm (Fin n)) : FinitePoset n where
  rel x y := P.rel (e.symm x) (e.symm y)
  refl x := P.refl (e.symm x)
  antisymm hxy hyx := by
    exact e.symm.injective (P.antisymm hxy hyx)
  trans hxy hyz := P.trans hxy hyz

def induce {k n : ℕ} (P : FinitePoset n) (f : Fin k ↪ Fin n) : FinitePoset k where
  rel x y := P.rel (f x) (f y)
  refl x := P.refl (f x)
  antisymm hxy hyx := f.injective (P.antisymm hxy hyx)
  trans hxy hyz := P.trans hxy hyz

end FinitePoset

/-- A law on every finite size, invariant under labels and consistent when a
fixed injected subset is observed.  These are assumptions, not consequences of
an arbitrary primitive relation. -/
structure ExchangeableProjectiveOrderLaw where
  identifier : String
  identifier_nonempty : identifier ≠ ""
  law : ∀ n : ℕ, PMF (FinitePoset n)
  exchangeable : ∀ (n : ℕ) (e : Equiv.Perm (Fin n)),
    (law n).map (fun P => P.relabel e) = law n
  projective : ∀ {k n} (f : Fin k ↪ Fin n),
    (law n).map (fun P => P.induce f) = law k

/-- Probability that a Boolean test accepts at size `n`. -/
noncomputable def acceptanceProbability
    (model : ExchangeableProjectiveOrderLaw)
    (test : ∀ n : ℕ, FinitePoset n → Bool) (n : ℕ) : ENNReal :=
  ((model.law n).map (test n)) true

def IsAsymptoticallyAccepted
    (model : ExchangeableProjectiveOrderLaw)
    (test : ∀ n : ℕ, FinitePoset n → Bool) : Prop :=
  Tendsto (fun n => (acceptanceProbability model test n).toReal) atTop (𝓝 1)

def IsAsymptoticallyRejected
    (model : ExchangeableProjectiveOrderLaw)
    (test : ∀ n : ℕ, FinitePoset n → Bool) : Prop :=
  Tendsto (fun n => (acceptanceProbability model test n).toReal) atTop (𝓝 0)

/-- Sizes used to design tests are disjoint from an unbounded validation set. -/
structure HeldoutScaleSplit where
  training : Set ℕ
  validation : Set ℕ
  disjoint : Disjoint training validation
  validation_unbounded : ∀ bound, ∃ n ∈ validation, bound ≤ n

/-- What a future ensemble-level emergence claim must supply.  The equivalence
relation is explicit because approximate geometric uniqueness cannot be hidden
inside the word "same". -/
structure EnsembleEmergenceCertificate
    (target : ExchangeableProjectiveOrderLaw)
    (competitor : Set ExchangeableProjectiveOrderLaw)
    (equivalent : ExchangeableProjectiveOrderLaw →
      ExchangeableProjectiveOrderLaw → Prop) where
  split : HeldoutScaleSplit
  test : ∀ n : ℕ, FinitePoset n → Bool
  equivalent_refl : ∀ model, equivalent model model
  equivalent_symm : ∀ {left right}, equivalent left right → equivalent right left
  equivalent_trans : ∀ {first second third},
    equivalent first second → equivalent second third → equivalent first third
  target_accepted : IsAsymptoticallyAccepted target test
  inequivalent_competitors_rejected : ∀ model ∈ competitor,
    ¬ equivalent model target → IsAsymptoticallyRejected model test
  validation_only_claim : ∀ n, n ∈ split.training → n ∉ split.validation

/-- A certificate really does separate every declared inequivalent competitor;
this theorem merely exposes the stored obligation and adds no hidden model. -/
theorem EnsembleEmergenceCertificate.separates
    {target : ExchangeableProjectiveOrderLaw}
    {competitor : Set ExchangeableProjectiveOrderLaw}
    {equivalent : ExchangeableProjectiveOrderLaw →
      ExchangeableProjectiveOrderLaw → Prop}
    (certificate : EnsembleEmergenceCertificate target competitor equivalent)
    (model : ExchangeableProjectiveOrderLaw) (hmodel : model ∈ competitor)
    (hinequivalent : ¬ equivalent model target) :
    IsAsymptoticallyRejected model certificate.test :=
  certificate.inequivalent_competitors_rejected model hmodel hinequivalent

end JanusFormal.ProgramM
