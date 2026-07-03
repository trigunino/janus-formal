# Janus Repository Layout

## Daily Active Surface

- `JanusFormal.lean` is intentionally minimal.
- `JanusFormal/ActiveZ2Sigma.lean` imports the active Z2/Sigma model.
- `scripts/*z2_sigma*.py` and `tests/test_*z2_sigma*.py` are the active audit
  and verification surface.

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

Optional archive validation:

```bash
lake build JanusFormal.AllImportsArchive
```

## Shared Python Code

- `src/janus_lab/bao.py`, `bao_maps.py`, `constants.py`, `data.py`,
  `statistics.py`, and geometry/numerics helpers are common library modules.
- `src/janus_lab/z4_*.py` is legacy diagnostic infrastructure and must not be
  used as active Z2/Sigma evidence.

## Policy

- Do not build `JanusFormal.AllImportsArchive` in the normal loop.
- Do not use archived Z4/CMB results as active model evidence.
- Add new active gates through `JanusFormal/ActiveZ2Sigma.lean`.
- Keep archival gates accessible through `JanusFormal/AllImportsArchive.lean`.
