# Janus Research Program

This file is the stable top-level map of the repository. It is intentionally short. The detailed current architecture, evidence matrix and blockers live in:

```text
docs/program_master_roadmap.md
```

## Scientific target

Derive the Janus geometry, field content, charge normalization and cosmological scale from explicit mathematical and physical laws, without importing an observed value of `H0`, `alpha`, a bridge radius or an equivalent hidden scale.

The positive length denoted `alpha^2` in the 2018 exact solution is called `A = alphaSquaredLength` in the current research branches.

## Evidence labels

| Code | Meaning |
| --- | --- |
| **T** | theorem or exact algebra checked in Lean |
| **X** | executable Python audit or numerical consistency test |
| **C** | conditional theorem from explicit assumptions |
| **I** | analytic/geometric theorem used as an interface |
| **N** | no-go or correction of an over-strong claim |
| **O** | open theorem or construction |

No claim may move from `C`, `I` or `O` to `T` without replacing its opaque input by an actual construction or theorem.

## Program matrix

| Program | Purpose | Current role | Head/document |
| --- | --- | --- | --- |
| **D — Fundamental geometry** | derive throat, gauge and charge data from one PT-twisted geometry | geometric seed | `JanusFormal.Branches.FundamentalGeometryD` |
| **D7 — Spectral theory** | derive heat-kernel, determinant, eta and effective-action data | quantum/spectral completion | `JanusFormal.Branches.FundamentalGeometryD7SpectralTheory` |
| **D8 — Topology and representations** | determine what the mapping torus actually forces | topology/representation audit | `JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation` |
| **D9/D10/D11** | elliptic complexes, Quillen/anomaly and natural operators | analytic/natural-operator bridge | branch-specific heads under `JanusFormal/Branches/` |
| **P — Variational principle** | select or reconstruct the Janus action | P0 no-go, P-A relative universality, P-B anomaly, P-C Helmholtz, P-D pairings | `JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple` |
| **P.E — Jets and representations** | reduce local natural operators to finite-jet equivariant evaluators and classify pairings | naturality/representation frontier | `JanusFormal.Branches.FundamentalGeometryPEJetUniversality` |
| **A — Quantum world-volume** | generate the dimensionful LL charge and stable vacuum | absolute-scale generator | `JanusFormal.Branches.WorldvolumeQuantumAlpha` |
| **B — Nonlinear bimetric junction** | derive the common action, constraints, PT charge and bridge junction | classical/geometric consistency | `JanusFormal.Branches.NonlinearBimetricJunctionAlpha` |
| **C — Charge compatibility** | identify bulk, throat, LL and bridge charge normalizations | interface between D/A/B | `JanusFormal.Branches.AlphaDeepCompletionMatrix` |
| **E — Observation** | test derived predictions against SN, BAO, CMB, lensing and structure | falsification after theory closure | branch-specific runners |

## Dependency graph

```text
D8 topology/representation audit
  -> D1 smooth mapping torus and one-sided throat
       -> D9/D10/D11 natural Fredholm/operator framework
            -> P.E finite jets and equivariant classification
                 -> P-D natural pairings
                      -> P-C Helmholtz reconstruction
                           -> P-B anomaly consistency
                                -> selected renormalized action
                                     -> A/B/C absolute-scale closure
                                          -> E observational tests
```

## Current topology correction

For the candidate

```text
J(T,rho) = (S3 x R)/((x,u) ~ (rho(x),u+T)), T != 0,
```

the translation makes the integer action fixed-point free. The current object is therefore treated as a smooth nonorientable mapping torus, not as an orbifold with a singular equatorial locus.

Its equatorial `S2 x S1` throat is expected to be one-sided. The orientation cover has two exchanged sides, while the quotient has no global side label. Consequently:

```text
cover : quotient = 2 : 1,
world A : world B = 1 : 1 under deck symmetry.
```

The expected fundamental group is `Z`, not `Z4`. Quarter holonomy can arise as a fourth-root lift of the orientation character, but its order is the order of the holonomy image, not the order of the fundamental group. Cyclic topology alone also does not select a rank-five multiplet.

## Program P / P.E summary

The current action-selection program has the following honest structure:

```text
P0   moduli geometry alone does not select an action
P-A  unique action only relative to Hessian/critical/value or a parent action
P-B  anomaly cancellation is an independent consistency filter
P-C  Helmholtz reconstructs a variational action from a suitable Euler source
P-D  remaining same-parity couplings require invariant-pairing classification
P-E  local natural operators reduce to smooth equivariant finite-jet evaluators
```

The corrected P.E theorem is:

> A regular local natural operator is locally represented by a smooth finite-jet evaluator. Under holonomic jet realization, naturality is equivalent to equivariance of that evaluator, and the evaluator is unique when realization is surjective.

This does **not** imply polynomiality, ellipticity, one global uniform order or field-content selection.

## Stable entry points

1. `README.md`
2. `PROGRAM.md`
3. `docs/program_master_roadmap.md`
4. `docs/research_dashboard.md`
5. `docs/janus_branch_registry.md`
6. `docs/program_p_variational_principle.md`
7. `docs/program_pe_jet_universality_proof.md`
8. `docs/program_pe_lemma2_naturality_equivariance.md`
9. the corresponding Lean branch head

## Stable builds

```text
lake build JanusFormal.Branches.FundamentalGeometryD
lake build JanusFormal.Branches.FundamentalGeometryD7SpectralTheory
lake build JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation
lake build JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple
lake build JanusFormal.Branches.FundamentalGeometryPEJetUniversality
```

## Current CI truth

The dedicated `Program PE jet universality` workflow has passed. The broader `Program D fundamental geometry` workflow still has integration failures, so the full branch must not yet be described as globally green.

## Repository rule

Every new proposal must record:

- program and stable ID;
- evidence level;
- inputs and dependencies;
- theorem, conditional result or no-go obtained;
- remaining geometric or physical atom;
- falsification criterion;
- Lean/Python build target.
