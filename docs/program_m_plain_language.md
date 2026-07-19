# Program M — Plain-language guide

## The question

Program M asks whether familiar physical structures can be obtained from
weaker mathematics instead of being assumed at the start.

It does **not** begin by assuming a universe, four dimensions, a metric, two
sectors or a Janus throat. Its first pilot contains only objects and labelled
relations between them.

## The first construction

For one selected relation, MF-TOP-001 defines reachability:

```text
A reaches A
A -> B and B -> C imply A reaches C
```

Reachability is a preorder. Mathlib's upper-set construction then gives a
topology: a mathematical notion of open regions and neighbourhoods.

```text
objects and a selected relation
  -> reflexive-transitive reachability
  -> preorder
  -> Alexandrov upper-set topology
```

This construction is invariant under renaming the objects. It therefore uses
the relational pattern, not the chosen names.

## What has actually been proved

- **MF-TOP-001 (T):** every selected binary relation supports this explicit
  Alexandrov-topology construction.
- **MF-TOP-002 (T):** isomorphic relational systems produce homeomorphic
  reconstructed spaces.
- **MF-NOGO-001 (T):** different primitive relations can lose their difference
  during reconstruction and produce the same topology.
- **MF-NOGO-002 (T):** the same relation can produce different standard
  topologies when the upper/lower convention changes.
- **MF-SEL-001 (T):** those two conventions agree exactly when reachability is
  reversible in both directions.
- **MF-ENUM-001 (X):** every directed relation on one to four objects has been
  enumerated after removing duplicates caused by renaming.
- **MF-CAUS-000 (T):** cycles can be grouped while retaining the irreversible
  order between groups; the result is a partial order.
- **MF-DEC-001 (T):** the original objects and links can be attached back to
  that order as fibers, with no information loss.
- **MF-COMP-001 (X/N):** fiber sizes and numbers of links still fail to
  distinguish many genuinely different systems.
- **MF-OBS-000 (T):** a compression may be used for an observable exactly when
  all states it confounds have the same observable value.
- **MF-CAUS-001 (T/N):** finite skeletons satisfy automatically the usual
  causal-set condition of local finiteness, so this condition selects nothing
  in the current census.
- **MF-DIM-000 (X/N):** ordering fraction, height, width and interval sizes do
  not uniquely determine even a small directed order or its orientation.
- **MF-DIM-001 (X/N):** l'ordre seul retrouve `d≈2` sur des données Poisson
  tenues à l'écart, mais donne aussi `d≈1,897` à une grille déjà connue comme
  anisotrope : une estimation de dimension n'est pas une géométrie reconstruite.
- **MF-LOC-001 (X/N):** le profil des tailles d'intervalles, toujours sans
  coordonnées, accepte 100 % des Poisson tenus à l'écart et rejette cette
  grille ; il ajoute donc un filtre réel, mais pas une preuve de variété.
- **MF-LOC-002 (X/N):** à quatre tailles, grilles et ordres trois-couches sont
  tous rejetés, mais le gate Poisson échoue à `N=256` avec 87,5 % au lieu des
  90 % requis ; le seuil n'a pas été corrigé après coup.
- **MF-LOC-003 (X/C):** sur des graines entièrement nouvelles, un seuil conforme
  garantit 90 % de couverture marginale par taille ; les couvertures observées
  sont 90–97,5 % et les deux familles adverses restent rejetées.
- **MF-GATE-001 (X/I):** un tiers peut maintenant fournir uniquement une matrice
  d'ordre et recevoir un rapport traçable : ordre invalide, taille non supportée,
  compatible ou incompatible avec les diagnostics Minkowski 1+1 actuels.
- **MF-MAN-000 (T/N):** every partial order embeds into some ordered space, so
  an unspecified order embedding proves no resemblance to a manifold.
- **MF-MAN-001 (I/T):** a compiled contract now requires exact order,
  number-volume, scale and sampling obligations, but no realization exists yet.
- **MF-MAN-002 (T/N):** if target and volume may be invented freely, every
  finite order passes that contract; they must therefore come from an
  independently defined geometric class.
- **MF-MAN-003 (I/T):** the target now owns its volume and clock, while the
  discrete side computes its longest chains intrinsically. No concrete
  spacetime target has yet passed this stronger contract.
- **MF-MAN-004 (I/T):** Minkowski 1+1 is available as an explicitly external
  test target; its internal volume/time formulas are proved, but no candidate
  M has yet passed the embedding test.
- **MF-MAN-005 (X/N):** a three-element chain passes the exact 1+1 order test,
  its finite volume tolerance and exact chain-step/time test; the six-element
  order `S₃` provably fails already at the order gate.
- **MF-MAN-006 (X/N):** enlarging the example reveals the trap : une chaîne ne
  remplit pas le volume 1+1 ; une grille remplit mieux le volume mais conserve
  une erreur temporelle directionnelle d'environ 6,07 %.
- **MF-MAN-007 (X/C):** un sprinkling de Poisson préenregistré passe les seuils
  finis de comptage et de temps dans trois directions ; cela valide le test sur
  Minkowski connu, pas l'émergence de Minkowski depuis les relations faibles.

These are mathematical results, not evidence that physical spacetime is an
Alexandrov space.

## Why the negative results matter

MF-TOP-001 proves existence, not unique emergence. The no-go results show that
the topology neither remembers all primitive information nor follows uniquely
without a declared orientation convention. Any future claim of emergence must
therefore list its extra assumptions.

Requiring reversibility removes this particular ambiguity, but it may also
erase a genuine arrow of time or causal direction. MF-SEL-001 is therefore a
diagnostic criterion, not a reason to impose symmetry.

The finite census finds 3,044 distinct four-object relation patterns but only
33 reachability patterns. This quantifies how much information is lost before
the topology is even constructed. See
[`program_m_finite_enumeration.md`](program_m_finite_enumeration.md).

The next construction preserves the directed skeleton but not the inside of
each cycle. Program M therefore retains both levels rather than replacing the
primitive relation. See
[`program_m_causal_skeleton.md`](program_m_causal_skeleton.md).

The lossless decorated version keeps both internal links and bridges between
components. It is explained in
[`program_m_decorated_skeleton.md`](program_m_decorated_skeleton.md).

The compression audit shows that even edge counts retain only 990 signatures
among 3,044 four-object relation classes. Exact endpoint incidence must remain
available. See
[`program_m_controlled_compression.md`](program_m_controlled_compression.md).

Compression is now governed by a proof obligation rather than convenience.
The rule is explained in
[`program_m_observable_factorization.md`](program_m_observable_factorization.md).

The first comparison with causal-set kinematics is explained in
[`program_m_causal_set_gate.md`](program_m_causal_set_gate.md). It deliberately
does not identify the skeleton order with physical time.

The first dimension audit keeps exact invariants separate from physical
interpretation. See
[`program_m_dimension_invariants.md`](program_m_dimension_invariants.md).
The coordinate-blind estimator and its negative control are documented in
[`program_m_blind_dimension_audit.md`](program_m_blind_dimension_audit.md).
The interval-abundance discriminator is documented in
[`program_m_interval_abundance_audit.md`](program_m_interval_abundance_audit.md).
Its deliberately retained multi-scale failure is documented in
[`program_m_interval_multiscale_audit.md`](program_m_interval_multiscale_audit.md).
The fresh conformal replacement is documented in
[`program_m_interval_conformal_audit.md`](program_m_interval_conformal_audit.md).
The reusable order-only candidate report is documented in
[`program_m_order_candidate_gate.md`](program_m_order_candidate_gate.md).
The preceding raw-relation adapter and its explicit information-loss witness
are documented in
[`program_m_relation_candidate_gate.md`](program_m_relation_candidate_gate.md).
The first exact failure of uniqueness for rank-based 1+1 embeddings is
documented in
[`program_m_embedding_ambiguity.md`](program_m_embedding_ambiguity.md).
The follow-up test of whether interval counts remove that ambiguity is
documented in
[`program_m_volume_selection.md`](program_m_volume_selection.md).
The independent longest-chain test and its conflict with volume are documented
in [`program_m_chain_time_selection.md`](program_m_chain_time_selection.md).
The formal proof that an arbitrary weighted sum does not resolve this conflict
is documented in [`program_m_tradeoff_nogo.md`](program_m_tradeoff_nogo.md).
The derived unit-free density/chain-scale relation and its finite no-go are
documented in
[`program_m_scale_consistency.md`](program_m_scale_consistency.md).
Its Poisson calibration and the retained square-grid collision are documented
in [`program_m_scale_conformal.md`](program_m_scale_conformal.md).
The independently calibrated fluctuation test that rejects this grid is
documented in
[`program_m_count_fluctuations.md`](program_m_count_fluctuations.md).
Its coordinate-free immediate-link successor is documented in
[`program_m_intrinsic_link_fluctuations.md`](program_m_intrinsic_link_fluctuations.md).
The fresh attempt to break that test and the retained collisions are documented
in [`program_m_adversarial_orders.md`](program_m_adversarial_orders.md).
The successful targeted attack that breaks all three gates is documented in
[`program_m_twin_adversary.md`](program_m_twin_adversary.md).
The calibrated exact-twin repair is documented in
[`program_m_exact_twins.md`](program_m_exact_twins.md), and its repeated-branch
counterattack in
[`program_m_branch_adversary.md`](program_m_branch_adversary.md).
The multi-level WL repair is documented in
[`program_m_wl_compressibility.md`](program_m_wl_compressibility.md), and the
asymmetric short-description attack that breaks it in
[`program_m_wl_adversary.md`](program_m_wl_adversary.md).

The first manifold-like no-go and the missing requirements for a faithful
embedding are explained in
[`program_m_manifoldlike_gate.md`](program_m_manifoldlike_gate.md).
The formal contract is explained in
[`program_m_faithful_embedding_interface.md`](program_m_faithful_embedding_interface.md).
Its tautological counterexample is explained in
[`program_m_faithful_embedding_nogo.md`](program_m_faithful_embedding_nogo.md).
The strengthened contract is explained in
[`program_m_well_conditioned_embedding.md`](program_m_well_conditioned_embedding.md).
The first concrete test target is explained in
[`program_m_minkowski_two_target.md`](program_m_minkowski_two_target.md).
Its first executable order gate is explained in
[`program_m_minkowski_two_order_audit.md`](program_m_minkowski_two_order_audit.md).
The first scaling audit is explained in
[`program_m_minkowski_two_scaling_audit.md`](program_m_minkowski_two_scaling_audit.md).
The preregistered Poisson audit is explained in
[`program_m_poisson_minkowski_two_audit.md`](program_m_poisson_minkowski_two_audit.md).
The single-finite-observation obstruction is explained in
[`program_m_finite_identifiability_nogo.md`](program_m_finite_identifiability_nogo.md).
The replacement ensemble-level contract is explained in
[`program_m_ensemble_emergence.md`](program_m_ensemble_emergence.md).
Its first concrete two-law experiment is explained in
[`program_m_ensemble_first_separation.md`](program_m_ensemble_first_separation.md).
The first ensemble adversary matching both tested means is explained in
[`program_m_ensemble_moment_adversary.md`](program_m_ensemble_moment_adversary.md).
The ergodic six-level adversary that breaks the two-statistic gate is explained
in [`program_m_ergodic_layer_adversary.md`](program_m_ergodic_layer_adversary.md).
The intrinsic height-growth repair is explained in
[`program_m_height_growth.md`](program_m_height_growth.md).
The infinite-level attack that also reproduces square-root height is explained
in [`program_m_infinite_layer_adversary.md`](program_m_infinite_layer_adversary.md).
The ensemble-scale exact-twin repair is explained in
[`program_m_twin_fraction_decay.md`](program_m_twin_fraction_decay.md).
The randomly decorated attack that also removes macroscopic exact twins is
explained in
[`program_m_decorated_layer_adversary.md`](program_m_decorated_layer_adversary.md).
The principled replacement by the hierarchy of all finite induced patterns is
explained in [`program_m_induced_patterns.md`](program_m_induced_patterns.md).

## Vocabulary

| Term | Meaning here |
| --- | --- |
| primitive object | an element with no assumed spatial or physical meaning |
| relation | a declared link between two primitive objects |
| reachability | zero or more consecutive relation steps |
| preorder | a reflexive and transitive relation |
| topology | a collection of subsets called open sets |
| Alexandrov topology | a topology also closed under arbitrary intersections |
| isomorphism | a reversible relabelling preserving all primitive relations |
| homeomorphism | a reversible map preserving the reconstructed topology |
| no-go | a proof that a stronger conclusion does not follow from current data |

## Current boundary

Nothing yet derives dimension, continuity, a metric, causal cones, fields,
bimetry, PT symmetry or a throat. A first formal contract dit maintenant ce
qu'un candidat au plongement fidèle doit fournir : ordre exact, comptage lié
au volume, tolérance, échelles et hypothèse d'échantillonnage. Aucun candidat
géométrique satisfaisant ce contrat n'a encore été construit, et l'unicité
approximative reste ouverte.

The accumulated finite gates are therefore diagnostics, not a universal
certificate. MF-ID-001 proves the obstruction. MF-ENS-001 moves the next claim
to coherent probability laws over all finite sizes, with held-out asymptotic
separation. No concrete law has yet passed that interface.

## Where to verify details

- axioms and anti-smuggling rules:
  `formal/axioms/program_m_foundations.md`;
- Lean proofs:
  `JanusFormal/Foundations/ProgramMTop001.lean` and
  `JanusFormal/Foundations/ProgramMTopNoGo.lean`, plus the exact selection
  criterion in `JanusFormal/Foundations/ProgramMTopologySelection.lean`;
- claim-by-claim provenance:
  `docs/program_m_provenance_register.md`.
# Current pattern test

`MF-PAT-002` compares every small causal shape, rather than a few averages. The
latest adversary looks correct on pairs and on two selected three-point averages,
but fails the complete three-point distribution. See
`docs/program_m_pattern_ladder.md`.

The next representation test asks whether two hidden order coordinates can be
reconstructed from the relation itself. This cannot be tested with fewer than
six objects; see `docs/program_m_two_order_representation.md`.
