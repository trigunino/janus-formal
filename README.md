# Janus Formal

`janus-formal` is a research repository for the mathematical structure of Janus cosmology: global topology, Spin/Pin and gauge data, spectral operators, variational reconstruction, charge normalization and eventual observational tests.

The repository contains many **conditional theorems, no-go results and research interfaces**. It does not currently claim a complete physical theory, a unique renormalized action or a numerical no-fit value of the Janus length scale.

## Start here

Read these files in order:

1. [`PROGRAM.md`](PROGRAM.md) — stable program map;
2. [`docs/current_status.md`](docs/current_status.md) — current integration, CI and scientific status;
3. [`docs/program_master_roadmap.md`](docs/program_master_roadmap.md) — detailed dependency graph;
4. [`docs/program_p_variational_principle.md`](docs/program_p_variational_principle.md) — Program P in detail;
5. [`docs/program_pe_categorical_jet_equivalence.md`](docs/program_pe_categorical_jet_equivalence.md) — corrected categorical jet theorem and Janus groupoid obligations;
6. [`docs/program_pe_structured_jet_reduction.md`](docs/program_pe_structured_jet_reduction.md) — action-groupoid core, low-order jet normal forms and isotropy locks;
7. [`docs/program_pe_low_order_structured_background.md`](docs/program_pe_low_order_structured_background.md) — concrete chain-rule, curvature and combined `(B,F)` quotient theorems;
8. [`docs/program_pd_global_pairing_modules.md`](docs/program_pd_global_pairing_modules.md) — correction from pointwise multiplicity to global coupling modules;
9. [`docs/janus_branch_registry.md`](docs/janus_branch_registry.md) — operational Lean heads and parked branches.

## Repository layout

- `JanusFormal/` — Lean package;
- `JanusFormal/Branches/` — focused research heads and gate modules;
- `JanusFormal/Shared/` and `JanusFormal/Core.lean` — reusable definitions;
- `docs/` — program specifications, evidence matrices and research conclusions;
- `scripts/` — executable numerical/symbolic audits;
- `tests/` — Python tests for the audits;
- `src/` — supporting Python implementation.

## Evidence labels

| Label | Meaning |
| --- | --- |
| **T** | theorem or exact algebra checked in Lean |
| **X** | executable Python or symbolic audit |
| **C** | conditional theorem from named assumptions |
| **I** | analytic/geometric theorem represented by an interface |
| **N** | no-go result or correction of an over-strong claim |
| **O** | open construction or theorem |

A Lean theorem about an abstract status structure does not by itself prove that the corresponding physical input exists. The input must be constructed before a conditional result can be promoted.

## Building

The default target is deliberately lightweight:

```bash
lake build JanusFormal
```

It imports the shared core only. Build focused programs explicitly, for example:

```bash
lake build JanusFormal.Branches.FundamentalGeometryDiracSpectral
lake build JanusFormal.Branches.FundamentalGeometryPEJetUniversality
lake build JanusFormal.Branches.FundamentalGeometryPEInvariantPairings
lake build JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple
```

Do not use an all-import build as the normal workflow. The repository contains independent and historical research branches with different closure states.

## Current highest-level conclusion

The strongest architecture presently supported is:

```text
mapping-torus / one-sided-throat geometry
  -> normal-line Z2 and candidate quarter-phase lift
  -> natural bundles and elliptic-symbol families
  -> regular-local finite-jet operators
  -> action-groupoid and holonomic equivariant morphism cores
  -> concrete low-order source/gauge quotient represented by (B,F)
  -> residual tangent/normal frame action
  -> isotropy-stratified pointwise pairings
  -> invariant scalar coefficient modules
  -> Helmholtz / Noether / anomaly tests
  -> action class plus finite renormalization
  -> stable vacuum and absolute-scale question
```

The categorical equivalence is classical for ordinary natural and gauge-natural bundles. The repository now proves the formal second-order source-chain-rule quotient, the concrete abelian connection one-jet quotient by curvature, and the universal combined low-order `(B,F)` quotient. The decorated SpinC-immersion specialization still requires finite-dimensional smooth tensor models, adapted orthogonal/SpinC frames, the actual structured jet groupoid, effective descent and a higher-order jet-isomorphism theorem. Pointwise multiplicity-one pairings do not by themselves give one constant global coupling, and their ranks can jump across isotropy strata. The final variational, normalization and absolute-scale arrows also remain open in the concrete Janus theory. See `docs/current_status.md` for the precise boundary between proved algebra, executable checks and open physics.
