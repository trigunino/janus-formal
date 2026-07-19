import JanusFormal.Foundations.ProgramMFaithfulEmbeddingInterface

/-!
# MF-MAN-002: the abstract faithful-embedding contract is non-discriminating

Every finite partial order satisfies `MF-MAN-001` by taking itself as target
and defining region volume to be cardinality.  This is a deliberate no-go:
geometric target axioms and an independently fixed volume are indispensable.
-/

namespace JanusFormal.ProgramM

open Set

universe u

/-- The tautological specification witnesses why an arbitrary ordered target
and a freely chosen volume do not test manifold-likeness. -/
noncomputable def tautologicalFaithfulEmbeddingSpecification
    (C : Type u) [PartialOrder C] [Finite C] :
    FaithfulEmbeddingSpecification C C (Set C) where
  embedding := (OrderIso.refl C).toOrderEmbedding
  contains r x := x ∈ r
  volume r := (r.ncard : ℝ)
  density := 1
  tolerance _ := 0
  scale _ := 0
  minScale := 0
  maxScale := 0
  admissible _ := True
  samplingAssumption := True
  failureProbability := 0
  density_pos := by norm_num
  volume_nonneg := by intro r; exact_mod_cast Nat.zero_le r.ncard
  tolerance_nonneg := by intro r; norm_num
  scaleWindow := le_rfl
  admissible_scale := by intro r hr; exact ⟨le_rfl, le_rfl⟩
  failureProbability_mem := by constructor <;> norm_num
  countVolumeLaw := by
    intro hs r hr
    simp

/-- Hence every finite partial order has a closed `MF-MAN-001` certificate,
without supplying any continuum geometry. -/
noncomputable def tautologicalFaithfulEmbeddingCertificate
    (C : Type u) [PartialOrder C] [Finite C] :
    FaithfulEmbeddingCertificate C C (Set C) where
  specification := tautologicalFaithfulEmbeddingSpecification C
  samplingProof := trivial

theorem abstract_faithful_embedding_is_automatic
    (C : Type u) [PartialOrder C] [Finite C] :
    Nonempty (FaithfulEmbeddingCertificate C C (Set C)) :=
  ⟨tautologicalFaithfulEmbeddingCertificate C⟩

end JanusFormal.ProgramM
