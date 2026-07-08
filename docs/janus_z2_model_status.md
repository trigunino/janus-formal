# Janus Z2 Model Status

This note is the current short status for the active non-CMB model branch.

## Active Core

The active geometry is:

- global projective cover: `S4 -> RP4`;
- geometric symmetry: `Z2`, not legacy `Z4`;
- resolved tunnel/throat: `Sigma`;
- PT bridge/null branch kept separate from the regular Sigma branch.

Legacy `Z4` is archived unless a real Pin/spinorial monodromy around the
throat is derived. It is not used as an assumption.

## Closed Or Usable

- Projective/tunnel topology is the clean core.
- `Z2` transport around `Sigma` is the active geometric transport.
- The published Janus exact family gives the relation
  `alpha = -2*pi*G*E_global/c^2`.
- The `Null/PT bridge` branch gives a consistent bridge-source structure if a
  LL-brane tension/state `chi_LL` is supplied.
- The published bimetric sector gives relative sector structure, but not an
  absolute density normalization by itself.

## Main Open Lock

`alpha` is not currently generated as a no-fit prediction.

It is classified as a continuous global energy/state-sector label. Equivalent
faces of the same missing input are:

- `alpha`;
- `E_global`;
- `M_bridge`;
- `chi_LL`;
- absolute FLRW density normalization.

The current repository does not derive the law that selects this value.

## Exhausted Routes

The following routes have been pushed to their current endpoint:

- regular PT67 torsionless Holst/Palatini theta: zero non-GHY trace;
- Souriau moment map: gives a global charge, not a local boundary density;
- LL-brane bridge: gives mass/radius in terms of `chi_LL`, not `chi_LL` itself;
- flux/prequantization: coherent target, but missing derived charge unit and
  primitive sector;
- minisuperspace exact orbit: blocked by noncompact `u` orbit and no finite
  boundary prescription for `V(alpha)`;
- Sigma local counterterm: no accepted local density that produces the missing
  FLRW source without extra boundary data.

## Current Verdict

The work improves Janus by making the assumptions explicit:

- the active `alpha/global-energy` branch is structurally closed;
- its absolute dimensional scale remains underdetermined;
- the active model is not a completed no-fit cosmology;
- it is a structured family of Janus/Z2 states indexed by a global charge;
- observation may select a sector, but that is not the same as deriving it;
- a stronger theory must derive the state-selection law for `alpha`.
- the active observational endpoint now uses Pantheon+ full covariance plus
  DESI DR2 BAO and still drives the Janus shape proxy to the `q0 -> 0-`
  boundary, i.e. the GR-limit edge rather than an interior Janus sector.
- the like-for-like background comparison against coarse `LCDM`/`CPL`
  baselines on the same dataset set gives a clean observational no-go for an
  interior Janus background sector.

## The Janus Cosmological Model 2024 Reference

The repo now has a paper-structured reference package for the 2024 published
Janus line.

Two branch classes are now separated explicitly:

- `paper_only`: active branch, only paper-explicit content;
- `paper_plus_cited_comparison`: inactive helper branch, includes cited
  comparison machinery kept outside the active paper-only status.
- concrete local source index:
  `docs/janus_2024_reference_branches_sources.md`.
- post-2024 extension bundle index:
  `docs/janus_extended2026_sources.md`.

- published bulk bimetric equations: present;
- paper-native two-metric FLRW equation object: present;
- paper-native `k = kbar = -1` branch: present;
- paper-native observational anchors: present (`70` direct-standard-candle
  H0 statement, `67` LCDM/CMB comparison statement, magnitude-redshift curve
  claim);
- published cited exact shape layer: present in repo but excluded from the
  active paper-only branch;
- plus-history proxy: present in repo but excluded from the active paper-only
  branch;
- published relative `5% / 95%` sector ratio: present;
- published comparison-side Janus observation reference: present in repo but
  excluded from the active paper-only branch;
- therefore `like_for_like_with_paper = false`;
- therefore `paper_explicit_only_reference_ready = true`;
- therefore `repo_implicit_closure_forbidden = true`;
- therefore `paper_structured_reference_ready = true`.
- but `strict_paper_only_reference_ready = false`.

Still not done:

- materialize a paper-native absolute density normalization object;
- materialize a paper-native two-metric background history/path;
- no active observational run has yet been executed on a strict full-bulk
  two-metric reference path.

Already active in code:

- paper branch `k = kbar = -1`;
- global conserved `E` equation;
- sector dust-density laws;
- two-metric FLRW RHS ready for a future solver path;
- common-time `x0` FLRW published equation object;
- cited exact plus-sector shape object.
- helper-only layers exist in the repo but are explicitly excluded from the
  strict paper-native reference:
  cited calibration, normalization contract, and repo-closed two-metric bulk
  history wrapper.

So the correct reading is:

- the 2024 paper reference is recreated as a reference branch;
- the 2024 paper reference now contains only objects fixed explicitly by the
  paper, with paper underdetermination left open;
- cited comparison helpers remain available in the repo, but are not counted as
  active paper-only reference content;
- the 2024 paper reference is not yet a strict paper-text-only full-bulk
  materialization;
- the 2024 paper reference is not a completed no-fit cosmology here;
- helper closures remain available in the repo but are not counted as the
  active paper reference;
- the next branch is paper-native materialization before any observational run.

## Torsionful Holst/Nieh-Yan Sigma

Do not open this as the next default branch.

Reason:

- on the active regular PT67 branch, Holst/Nieh-Yan is torsionless and gives no
  nonzero boundary density;
- a torsionful Sigma would be a real new physical sector, not a small patch;
- it can matter only if the model supplies a nonzero torsion source on Sigma:
  spin current, fermion condensate, Nieh-Yan charge, or torsionful boundary
  condition;
- without such a source, it repeats the same obstruction with more symbols.

Recommended policy:

- archive the current alpha branch as conditional/inactive;
- reopen torsionful Holst/Nieh-Yan only if a concrete torsion source or
  boundary phase space is derived from Janus/PT;
- otherwise focus on a clear public-facing model status and, separately,
  observational sector selection for `alpha`.

Current exhaustion verdict:

- `spin_current_on_sigma = false` for the active assets: the Dirac/spin route is
  physically standard, but the Janus/Sigma fermion distribution and spin
  polarization are not derived;
- `nieh_yan_charge_nonzero = false`: the active torsion pullback is zero;
- `torsionful_boundary_condition = false`: PT67 uses torsionless boundary data;
- `singular_defect_source = false` on the regular branch: the null/LL bridge is
  a separate extension and still lacks `chi_LL` selection.

Therefore `torsion_source_on_sigma = false` for the active model. This is a
relative no-go, not a universal theorem against torsion.
