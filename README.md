# Janus Formal

`janus-formal` is a research repository for the mathematical structure of Janus cosmology: global topology, Spin/Pin and gauge data, spectral operators, variational reconstruction, charge normalization and eventual observational tests.

The repository contains many **conditional theorems, no-go results and research interfaces**. It does not currently claim a complete physical theory, a unique renormalized action or a numerical no-fit value of the Janus length scale.

## Start here

Read these files in order:

1. [`PROGRAM.md`](PROGRAM.md) — stable program map;
2. [`docs/current_status.md`](docs/current_status.md) — current integration, CI and scientific status;
3. [`docs/program_master_roadmap.md`](docs/program_master_roadmap.md) — detailed dependency graph;
4. [`docs/program_p_variational_principle.md`](docs/program_p_variational_principle.md) — Program P in detail;
5. [`docs/janus_branch_registry.md`](docs/janus_branch_registry.md) — operational Lean heads and parked branches.

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
lake build JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple
```

Do not use an all-import build as the normal workflow. The repository contains independent and historical research branches with different closure states.

## Current highest-level conclusion

The strongest architecture presently supported is:

```text
mapping-torus / one-sided-throat geometry
  -> normal-line Z2 and candidate quarter-phase lift
  -> natural bundles and elliptic-symbol families
  -> finite-jet equivariant classification
  -> invariant pairings and compatibility pullbacks
  -> Helmholtz / Noether / anomaly tests
  -> action class plus finite renormalization
  -> stable vacuum and absolute-scale question
```

The final three arrows remain open in the concrete Janus theory. See `docs/current_status.md` for the precise boundary between proved algebra, executable checks and open physics.
