# Janus Build Architecture

## Goal

Keep the default Lean build small, keep reusable bricks in small libraries, and
make each research branch buildable through its own head module.

## Layout

- `JanusFormal`
  - lightweight root;
  - imports only `JanusFormal.Core`;
  - use for quick sanity builds.

- `JanusFormal.Core`
  - no-Mathlib shared kernel;
  - keep only tiny common declarations here.

- `JanusFormal.Shared.*`
  - small reusable libraries;
  - each library must build independently.

- `JanusFormal.Basic`
  - compatibility layer;
  - imports `Mathlib` and `JanusFormal.Core`;
  - keep it for older modules that already depend on `Basic`.

- `JanusFormal.Branches.*`
  - one head module per branch;
  - imports only the libraries and branch-specific files needed for that branch.

See `docs/janus_branch_registry.md` for the branch list and status.

## Practice

Prefer:

```powershell
lake build JanusFormal
lake build JanusFormal.Shared.Foundation
lake build JanusFormal.Branches.AlphaBridgeStateLaw
lake build JanusFormal.Branches.NativeBAORulerContract
lake build JanusFormal.Branches.JanusEarlyTimeOrbifoldRuler
```

Do not use a global all-import build as normal workflow.

## Refactor Policy

- Keep common primitives in small shared modules such as `Core` and `Shared/*`.
- Use `Basic` only when a branch really needs `Mathlib` compatibility.
- Keep branch logic and gate files under explicit `Branches/*` heads.
- Put shared gates under `Shared/*`.
- Put diagnostic/blocked attempts under explicit branch heads too.
- Do not import diagnostic or experimental branches from the lightweight root.
- Do not grow umbrella modules that import every branch.
