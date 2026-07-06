# Janus Repository Layout

## Daily Active Surface

- `JanusFormal.lean` is intentionally minimal.
- `JanusFormal/ActiveZ2Sigma.lean` imports the active Z2/Sigma model.
- `JanusFormal/NullSigmaPTBridge.lean` is a separate diagnostic facade for the
  null-Sigma/PT-bridge attempt. It is not imported by the normal active facade.
- `P0EFTJanusZ2PT67*` modules are the active chapter-6.7 regular PT-transfer
  surface route. They live in the active facade because they produce
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
python -m unittest tests.test_p0_eft_janus_active_z2_sigma_facade_audit_script
python -m unittest tests.test_p0_eft_janus_repository_layout_audit_script
lake build JanusFormal
```

## Archives

- `JanusFormal/AllImportsArchive.lean` is an optional compile audit for all
  historical modules.
- `JanusFormal/LegacyCMB.lean` groups old CMB/Planck diagnostics.
- `scripts/*z4*.py`, `scripts/*legacy*.py`, `tests/test_*z4*.py`, and
  `tests/test_*legacy*.py` are archived diagnostics unless explicitly revived by
  a new gate.
- Old Git branches `codex/sigma-plugstar-ejection-threshold-gate` and
  `codex/sigma-point-collapse-limit-gate` are ancestors of `main`; their content
  is now organized by files/facades rather than needed as active branch state.

Optional archive validation:

```bash
lake build JanusFormal.AllImportsArchive
```

## Shared Python Code

- `src/janus_lab/bao.py`, `bao_maps.py`, `constants.py`, `data.py`,
  `statistics.py`, and geometry/numerics helpers are common library modules.
- `src/janus_lab/z4_*.py` is legacy diagnostic infrastructure and must not be
  used as active Z2/Sigma evidence.
- `src/janus_lab/z2_pt67_*.py` is active regular-Sigma geometry.
- `src/janus_lab/z2_null_sigma_*.py` is diagnostic null-boundary geometry.

## Policy

- Do not build `JanusFormal.AllImportsArchive` in the normal loop.
- Do not use archived Z4/CMB results as active model evidence.
- Add new active gates through `JanusFormal/ActiveZ2Sigma.lean`.
- Keep archival gates accessible through `JanusFormal/AllImportsArchive.lean`.
