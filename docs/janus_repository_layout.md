# Janus Repository Layout

## Daily Surface

- `JanusFormal.lean` is intentionally minimal.
- `JanusFormal/Core.lean` is the no-Mathlib shared kernel.
- `JanusFormal/Shared/` contains reusable shared bricks.
- `JanusFormal/Branches/` contains one public head per branch.
- `docs/janus_branch_registry.md` records branch status and blockers.
- `JanusFormal/Branches/NullPTBridgeMass.lean` is the branch head for the
  null-Sigma/PT-bridge mass attempt.
- `P0EFTJanusZ2PT67*` modules are the active chapter-6.7 regular PT-transfer
  surface route. They are exposed through the Z2/Sigma branch head because they produce
  nondegenerate `h_ab`, unit normal, local `K_ab`, and `DeltaK_PT=0`.
- `scripts/*z2_sigma*.py` and `tests/test_*z2_sigma*.py` are the active audit
  and verification surface.
- `scripts/*pt67*.py`, `src/janus_lab/z2_pt67_*.py`, and
  `tests/test_*pt67*.py` are active geometry inputs for the regular Sigma
  pipeline.
- `scripts/*null_sigma*.py`, `src/janus_lab/z2_null_sigma_*.py`, and
  `tests/test_*null_sigma*.py` are diagnostic null-branch material.

Daily validation:

```bash
python -m unittest tests.test_p0_eft_janus_z2_sigma_branch_head_audit_script
python -m unittest tests.test_p0_eft_janus_repository_layout_audit_script
lake build JanusFormal
lake build JanusFormal.Branches.Z2SigmaRegularThroat
lake build JanusFormal.Branches.NullPTBridgeMass
```

## Diagnostic And Blocked Branches

- `JanusFormal/Branches/CMBPlanckDiagnosticAttempts.lean` groups CMB/Planck diagnostic attempts.
- `JanusFormal/Branches/Z4CMBTopologyResetBlockedProgram.lean` groups the Z4/CMB solver route blocked by the topology reset.
- `JanusFormal/Branches/P0BimetricOrbifoldPrototypeProgram.lean` is a light inventory head for bimetric/orbifold prototype modules.
- `JanusFormal/Branches/P0EFTOrbifoldHolstPrototypeProgram.lean` is a light inventory head for EFT/orbifold/Holst prototype modules.
- These are real branch heads, not a separate catch-all old-attempt filesystem category.
- Their status is diagnostic/blocked unless a later branch explicitly revives one
  as active evidence with a new branch entry.
- Old Git branches `codex/sigma-plugstar-ejection-threshold-gate` and
  `codex/sigma-point-collapse-limit-gate` are ancestors of `main`; their content
  is now organized by files/facades rather than needed as active branch state.

## Shared Python Code

- `src/janus_lab/bao.py`, `bao_maps.py`, `constants.py`, `data.py`,
  `statistics.py`, and geometry/numerics helpers are common library modules.
- `src/janus_lab/z4_*.py` is diagnostic Z4/CMB infrastructure and must not be
  used as active Z2/Sigma evidence.
- `src/janus_lab/z2_pt67_*.py` is active regular-Sigma geometry.
- `src/janus_lab/z2_null_sigma_*.py` is diagnostic null-boundary geometry.

## Policy

- Do not use a global all-import build in the normal loop.
- Do not use Z4/CMB diagnostic results as active model evidence.
- Add new branch entry points under `JanusFormal/Branches/`.
- Put reusable code under `JanusFormal/Shared/`.
