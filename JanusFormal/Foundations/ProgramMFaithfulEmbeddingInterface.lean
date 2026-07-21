import JanusFormal.Foundations.ProgramMManifoldlikeOrderEmbeddingNoGo
import Mathlib.Data.Real.Basic
import Mathlib.Data.Set.Card

/-!
# MF-MAN-001: explicit faithful-embedding interface

This interface separates a proposed statistical specification from a closed
certificate proving its sampling assumptions. It constructs no manifold.
-/

namespace JanusFormal.ProgramM

open Set

universe u v w

/-- Data and obligations required before an order embedding can be treated as
a finite faithful-embedding proposal. -/
structure FaithfulEmbeddingSpecification
    (C : Type u) (M : Type v) (Region : Type w)
    [PartialOrder C] [PartialOrder M] [Finite C] where
  embedding : C ↪o M
  contains : Region → M → Prop
  volume : Region → ℝ
  density : ℝ
  tolerance : Region → ℝ
  scale : Region → ℝ
  minScale : ℝ
  maxScale : ℝ
  admissible : Region → Prop
  samplingAssumption : Prop
  failureProbability : ℝ
  density_pos : 0 < density
  volume_nonneg : ∀ r, 0 ≤ volume r
  tolerance_nonneg : ∀ r, 0 ≤ tolerance r
  scaleWindow : minScale ≤ maxScale
  admissible_scale : ∀ r, admissible r → minScale ≤ scale r ∧ scale r ≤ maxScale
  failureProbability_mem : failureProbability ∈ Set.Icc (0 : ℝ) 1
  countVolumeLaw : samplingAssumption → ∀ r, admissible r →
    |(Set.ncard {c : C | contains r (embedding c)} : ℝ) - density * volume r| ≤ tolerance r

/-- A closed certificate supplies the statistical assumption that a mere
specification leaves as an explicit obligation. -/
structure FaithfulEmbeddingCertificate
    (C : Type u) (M : Type v) (Region : Type w)
    [PartialOrder C] [PartialOrder M] [Finite C] where
  specification : FaithfulEmbeddingSpecification C M Region
  samplingProof : specification.samplingAssumption

theorem FaithfulEmbeddingCertificate.order_preserved_and_reflected
    {C : Type u} {M : Type v} {Region : Type w}
    [PartialOrder C] [PartialOrder M] [Finite C]
    (cert : FaithfulEmbeddingCertificate C M Region) (x y : C) :
    cert.specification.embedding x ≤ cert.specification.embedding y ↔ x ≤ y :=
  cert.specification.embedding.le_iff_le

theorem FaithfulEmbeddingCertificate.verified_countVolumeLaw
    {C : Type u} {M : Type v} {Region : Type w}
    [PartialOrder C] [PartialOrder M] [Finite C]
    (cert : FaithfulEmbeddingCertificate C M Region)
    (r : Region) (hr : cert.specification.admissible r) :
    |(Set.ncard {c : C |
        cert.specification.contains r (cert.specification.embedding c)} : ℝ) -
        cert.specification.density * cert.specification.volume r| ≤
      cert.specification.tolerance r :=
  cert.specification.countVolumeLaw cert.samplingProof r hr

theorem FaithfulEmbeddingCertificate.verified_scaleWindow
    {C : Type u} {M : Type v} {Region : Type w}
    [PartialOrder C] [PartialOrder M] [Finite C]
    (cert : FaithfulEmbeddingCertificate C M Region)
    (r : Region) (hr : cert.specification.admissible r) :
    cert.specification.minScale ≤ cert.specification.scale r ∧
      cert.specification.scale r ≤ cert.specification.maxScale :=
  cert.specification.admissible_scale r hr

end JanusFormal.ProgramM
