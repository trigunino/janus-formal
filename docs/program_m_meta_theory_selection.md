# Program M — Meta-selection of theories

## Purpose

Program M asks a question upstream of Program P:

> Why select the Janus geometry, fields and variational problem rather than a
> competing theory with the same target observations?

It defines a reproducible protocol that can reject Janus, expose missing
assumptions, or justify sending a surviving Janus candidate into Program P.

## Scope boundary

```text
M: candidate theories and selection rules
  -> P: action and Euler system for each survivor
  -> A/B/C: scale and normalization
  -> E: observational falsification
```

Program M compares theory specifications. Program P reconstructs or selects an
action within one specification. No abstract score substitutes for prediction.

## Foundational objective

The central experiment is to determine whether characteristic Janus structures
can emerge without being assumed:

> Can a throat, bimetric sector structure or PT law be reconstructed from
> weaker mathematical axioms, and which exact axiom is responsible?

The first bounded branch is the relational pilot specified in
[`../formal/axioms/program_m_foundations.md`](../formal/axioms/program_m_foundations.md).
It assumes no topology or geometry. It is a pilot, not a claim that relations
are the unique fundamental language.

Every reconstruction must be entered in the
[`program_m_provenance_register.md`](program_m_provenance_register.md).
A non-technical introduction and current proof boundary are maintained in
[`program_m_plain_language.md`](program_m_plain_language.md).
The first exhaustive finite audit is documented in
[`program_m_finite_enumeration.md`](program_m_finite_enumeration.md).
The first order-theoretic quotient is documented in
[`program_m_causal_skeleton.md`](program_m_causal_skeleton.md).
Its lossless fiber decoration is documented in
[`program_m_decorated_skeleton.md`](program_m_decorated_skeleton.md).
The first controlled information-loss audit is documented in
[`program_m_controlled_compression.md`](program_m_controlled_compression.md).
The rule governing observable-safe compression is documented in
[`program_m_observable_factorization.md`](program_m_observable_factorization.md).
The locally finite causal-set comparison and its finite no-go are documented in
[`program_m_causal_set_gate.md`](program_m_causal_set_gate.md).
The exact finite-order invariant and dimension-estimator boundary is documented
in [`program_m_dimension_invariants.md`](program_m_dimension_invariants.md).
The order-embedding no-go and faithful-embedding obligations are documented in
[`program_m_manifoldlike_gate.md`](program_m_manifoldlike_gate.md).

## Evidence rule

The repository labels `T`, `X`, `C`, `I`, `N` and `O` apply. Every M claim must
also name its candidate class and equivalence relation.

## Work packages

### MF — Foundations and emergence

Start from explicitly weak primitive structures, reconstruct topology,
dimension, metric/causality, fields and geometry, and audit every arrow for
hidden assumptions. Alternative relational, algebraic, categorical and
spectral foundations remain separate candidates.

**Gate MF:** each derived structure has a provenance certificate, an
equivalence-invariance proof, a uniqueness or multiplicity result and a
countermodel. Janus-specific structures are forbidden as undeclared inputs.

### M0 — Candidate specification

Record topology, regularity, field bundles, gauge and discrete symmetries,
operator class, boundary data, quantization, parameter domain and the map to
observables.

**Gate M0:** the candidate can be serialized without an unnamed convention.

### M1 — Equivalence and redundancy

Quotient changes of variables, gauge choices, boundary terms and
observationally invisible reparameterizations.

**Gate M1:** publish allowed equivalences and invariants before counting
parameters.

### M2 — Hard consistency

Test well-posedness, constraint propagation, gauge/BRST closure, anomalies,
causality, hyperbolicity, physical ghosts, instabilities and global bundles.

**Gate M2:** reject failures or state the exact admissible regime.

### M3 — Variational realizability

Route survivors through Program P: pairings, Helmholtz/Noether conditions,
anomalies, action selection and normalization.

**Gate M3:** produce a concrete Euler family and action class, or an explicit
no-go. A fitted effective equation is insufficient.

### M4 — Predictivity and scale closure

Classify every parameter, initial condition and counterterm as derived,
independently measured, nuisance or fitted.

**Gate M4:** retain a prediction after calibration; hidden use of `H0`, a
bridge radius or an equivalent scale is prohibited.

### M5 — Discriminating observables

Compare initially flat Lambda-CDM, CPL, a consistent representative bimetric
theory and Janus. Pre-register where and how they differ.

**Gate M5:** executable forward predictions exist before held-out test data are
used. Degeneracy with a reparameterized comparator is a negative result.

### M6 — Selection ledger

Maintain a versioned matrix of candidates, M0–M5 gates, assumptions,
complexity, failures and surviving predictions.

**Gate M6:** every preference is reproducible under a named rule, with
sensitivity to priors, datasets and complexity penalties.

## Selection rule

1. Reject required consistency failures.
2. Quotient equivalent descriptions.
3. Require calculable and discriminating observables.
4. Compare empirical performance and parameter complexity.
5. Retain several candidates when evidence does not distinguish them.

Simplicity is a tie-breaker, not evidence of truth.

## First Janus comparison slice

The first bounded application is homogeneous expansion:

1. specify the exact Janus background and all free data;
2. express flat Lambda-CDM and CPL in identical observable conventions;
3. separate derived and fitted Janus quantities;
4. justify the background equations through the relevant Program P gates;
5. generate `H(z)/H0`, `D_M/r_d`, `D_H/r_d` and supernova distances;
6. reserve held-out DESI/Pantheon-like data;
7. record failure, degeneracy or a surviving discriminating prediction.

This slice does not validate perturbations, lensing, CMB or structure growth.

## Initial deliverables

- `MF-AXIOM-001`: foundational relational pilot — **I/O**;
- `MF-PROV-001`: reconstruction provenance register — **O**;
- `M-SPEC-001`: machine-readable candidate schema;
- `M-EQUIV-001`: equivalence and redundancy register;
- `M-GATE-001`: consistency checklist;
- `M-PARAM-001`: parameter and scale provenance ledger;
- `M-OBS-001`: common observable interface;
- `M-COMP-001`: Janus/Lambda-CDM/CPL comparison matrix;
- `M-NOGO-001`: rejected or degenerate candidate registry.

Program M now contains proved reconstruction and no-go results through the
order-theoretic skeleton, plus a compiled faithful-embedding contract. It does
not yet derive a continuum geometry, a throat, Janus or any competitor; see
[`program_m_faithful_embedding_interface.md`](program_m_faithful_embedding_interface.md).
The stronger chain-time contract and its limits are recorded in
[`program_m_well_conditioned_embedding.md`](program_m_well_conditioned_embedding.md).
Third parties can run the current order-only diagnostics through
[`program_m_order_candidate_gate.md`](program_m_order_candidate_gate.md); its
compatibility status is deliberately weaker than a geometry certificate.
