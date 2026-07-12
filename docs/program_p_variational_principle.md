# Program P — Variational Principle and Action Reconstruction

> Master project map: [`program_master_roadmap.md`](program_master_roadmap.md)

## Purpose

Programs D8–D11 identify the Janus topology, natural bundles, principal symbols,
elliptic complexes and determinant-line framework. They do **not** select one
physical action. Program P isolates that remaining problem:

> How can the Janus action be characterized, selected or reconstructed without
> fitting the desired radius or effective vacuum?

Program P has three principal routes:

```text
P-A  universal property / parent-bulk reduction
P-B  anomaly cancellation and discrete consistency selection
P-C  inverse calculus of variations / Helmholtz reconstruction
```

P-D and P.E then classify the invariant pairings and finite-jet equivariant
evaluators which can supply the remaining Hessian and operator data.

The routes are complementary. None is sufficient alone in its weakest form.

## Evidence labels

| Code | Meaning |
| --- | --- |
| **T** | exact algebra/theorem checked in Lean |
| **C** | conditional theorem from explicitly named inputs |
| **P** | physical or analytic derivation still open |
| **N** | no-go or correction |

## P0 — Moduli geometry does not select a potential

A metric on moduli does not select a scalar functional. A symplectic form does
not select a Hamiltonian. A Kähler-like package combines metric, complex and
symplectic structures but still leaves the moment map or potential as extra
data.

Lean:

```text
P0EFTJanusModuliGeometryNoGo.lean
```

Exact finite-dimensional witnesses prove:

```text
same metric + different potentials,
same metric + different gradients,
same symplectic form + different Hamiltonians.
```

### Verdict

```text
(Moduli, metric, symplectic form, complex structure)
  does not imply
one Janus action.
```

This removes the earlier speculative claim that a Kähler structure alone could
make the action inevitable.

---

# P-A — Relative universal property

A Hessian fixes a quadratic action only up to an affine functional. A unique
quadratic representative is obtained only after adding a critical point and a
reference value. Parent-bulk on-shell reduction is the strongest current
non-tautological source of such data, but it is canonical only relative to the
chosen parent action and boundary problem.

# P-B — Anomaly selection

PT pairing can cancel parity-odd anomaly data and constrain discrete field
content. It does not determine parity-even couplings, finite even counterterms
or a unique partition-section trivialization.

# P-C — Helmholtz reconstruction

Formal self-adjointness is the finite-dimensional Helmholtz condition. In the
quadratic model it is necessary and sufficient for Hessian realizability. PT
symmetry plus one normalization removes the affine ambiguity. The nonlinear
Janus theory still requires the complete Euler source, gauge/Noether identities,
variational cohomology and boundary/null-Lagrangian control.

# P-D and P.E

The remaining same-parity couplings are recast as invariant bilinear pairings
and equivariant finite-jet evaluators. Their full classification requires the
actual decorated SpinC/PT/Z4/BRST Janus symmetry category.

Detailed documents:

```text
docs/program_pe_invariant_pairings.md
docs/program_pe_jet_universality_proof.md
docs/program_pe_lemma2_naturality_equivariance.md
```

# Stable head

```text
lake build JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple
```

# Current verdict

```text
moduli geometry alone: insufficient;
P-A: relative canonicity;
P-B: anomaly/discrete consistency filter;
P-C: strongest inverse variational route;
P-D/P.E: classify the admissible pairings and finite-jet covariants.
```

The decisive open chain is:

```text
actual Janus category
→ adapted jet symmetry
→ equivariant evaluator classification
→ natural elliptic Euler family
→ nonlinear Helmholtz
→ anomaly and renormalization constraints
→ selected action.
```
