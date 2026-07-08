# Janus Paper-Native SN Freeze And Gap Map

This note freezes the current paper-native supernova/acceleration reference
branch and lists, as exhaustively as possible, what is still not acceptable if
the goal is to improve the model rather than merely restate the paper.

## Freeze Status

- `paper_native_sn_acceleration_branch_frozen = true`
- `published_analytic_branch_recovered = true`
- `published_q0_branch_recovered = true`
- `official_jla_likelihood_equivalent = false`
- `published_full_statistical_pipeline_uniquely_recovered = false`
- `paper_native_sn_acceleration_branch_promotable_as_reference = true`
- `paper_native_sn_acceleration_branch_promotable_as_final_observational_model = false`

## What Is Good In The Frozen Branch

- The Janus analytic SN/acceleration layer from the paper is reconstructed.
- The published `q0 < 0` branch and `q0 = -0.087` claim are reproducible under
  a paper-like fitting procedure.
- The official JLA package and the paper-like route are now explicitly
  separated.
- The branch is therefore usable as a strict reference branch for later model
  improvement.

## Exhaustive Gap Map

### 1. Statistical Procedure Is Not Unique

- The paper does not specify a unique executable likelihood pipeline.
- The official JLA full likelihood does not reproduce the published Janus
  `q0 = -0.087`.
- The published `q0` is recovered only under a simplified paper-like procedure.
- Therefore the observational claim is not yet uniquely reproducible from the
  paper text alone.

### 2. Official JLA Equivalence Fails

- Official JLA full route:
  - `zcmb`
  - full covariance
  - SALT2/JLA nuisance structure with `DeltaM`
  does not recover the published Janus best fit.
- Therefore the frozen branch is not equivalent to the standard official JLA
  cosmology likelihood.

### 3. Redshift Convention Is Under-Specified

- The paper does not state clearly whether the fit uses `zcmb`, `zhel`, or a
  transformed redshift convention in the final regression.
- The fitted `q0` moves materially depending on that choice.

### 4. Error Model Is Under-Specified

- The paper does not define precisely whether the fit uses:
  - full correlated covariance,
  - diagonalized covariance,
  - or a reduced per-SN variance.
- The published `q0` and `chi2` are sensitive to this choice.

### 5. Host-Mass Step Treatment Is Under-Specified

- The paper’s Eq. 7 writes the standardization with `MB`, `alpha`, `beta`.
- It does not explicitly state whether the JLA host-mass step `DeltaM` is kept
  in the operational fit.
- Including or excluding `DeltaM` shifts the recovered `q0`.

### 6. Nuisance Precision / Version Ambiguity Remains

- The official JLA example values are rounded.
- Betoule `stat` vs `stat+sys` nuisance tuples are distinct.
- The paper does not lock the exact nuisance tuple used in the Janus fit.

### 7. Published Chi-Square Is Still Not Exactly Recovered

- Published claim: `chi2/d.o.f = 657/738`.
- Best paper-like reconstruction gets very close in `q0`, but not exactly the
  same `chi2`.
- So the residual mismatch is localized in the statistical pipeline, not in the
  analytic Janus formula.

### 8. The Branch Covers SN/Acceleration Only

- This frozen branch does not close:
  - BAO,
  - CMB,
  - growth,
  - lensing,
  - early-universe ruler generation.
- It is a reference branch for one published observational layer, not a full
  cosmology.

### 9. Absolute Physical Normalization Is Still Missing

- The branch does not generate a no-fit absolute background normalization from
  the Janus model.
- The historical `q0/u0` layer is a shape-level observational branch, not a
  full absolute-density closure.

### 10. Two-Metric Bulk History Is Still Not Fully Materialized

- The paper-native exact plus-sector SN proxy is active.
- A full executable two-metric bulk background path is still not fully
  materialized as a paper-only observational engine.

### 11. No Unique Native BAO Contract

- The paper-native SN branch does not provide a native BAO ruler.
- Any BAO continuation still requires separate derivation and must not be
  silently inherited from the SN layer.

### 12. No Native CMB Contract

- The paper explicitly says the CMB interpretation is future work.
- Therefore this branch must not be used to imply a validated CMB pipeline.

### 13. The Published Negative-Mass Content Split Is Not Independently Validated Here

- The `96% / 4%` content statement is a paper-native model claim.
- It is not an independently rederived observational endpoint in this branch.

### 14. Comparison With Standard Cosmology Is Procedural, Not Yet Final

- The branch can now distinguish:
  - paper-native Janus fit procedure,
  - official JLA procedure.
- But it does not yet constitute a final adjudication versus all standard
  cosmology pipelines because it is intentionally frozen at the paper-native
  layer.

### 15. The Branch Must Not Be Quietly “Improved” In Place

- Any added closure on:
  - nuisance handling,
  - covariance,
  - BAO,
  - CMB,
  - normalization,
  - topology,
  - state selection
  would create a new branch class, not an edit of this frozen one.

## Consequence For The Next Branch

The next branch should not try to defend this frozen branch. It should audit and
improve it by explicitly choosing one or more of these directions:

1. derive the exact paper-fit statistical procedure;
2. materialize the full paper-native two-metric background history;
3. add a native BAO/ruler contract;
4. add a native CMB contract;
5. derive absolute normalization from the active Janus theory rather than from
   fit-only proxies.
