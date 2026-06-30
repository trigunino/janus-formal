# Janus BAO Observable Map v1

Status: working derivation target.

Goal: define how Janus should be compared to compressed BAO observables without importing Lambda-CDM ruler assumptions silently.

## No-Fit Rule

BAO candidate maps are split into two classes:

- diagnostic maps: data-inferred shapes used only to identify what is missing;
- admissible maps: shapes derived from verified Janus source equations before comparison to DESI.

Only admissible maps can be used as evidence. Diagnostic maps such as C3/C7 are not proof.

## Verified Source Anchors

- `M18`, Eqs. 15-17: open marker relation `r = sinh(2(u0 - ue))`.
- `M18`, Eq. 14: conversion relation `(1 - 2q) = c^2/(a^2 H^2)`.
- `X2026-variable-constants`, Eq. 40: `c_hat proportional a^-1/2`, characteristic lengths proportional to `a`, characteristic times proportional to `a^(3/2)`.
- `X2026-expansion-desi`, Eqs. 27-29: source claim that the exact Janus expansion branch targets DESI-like stronger past acceleration.

## Standard BAO Compression Assumptions

Compressed BAO measurements usually report combinations such as:

- `D_M(z) / r_d`
- `D_H(z) / r_d`
- `D_V(z) / r_d`

where `r_d` is treated as a fixed comoving sound horizon calibrated in a standard early-universe framework.

These assumptions are not automatically valid in Janus if:

- the early ruler forms during a variable-constants regime;
- radial and transverse conversions depend differently on `c_hat`, `t_hat`, or length gauges;
- the negative sector changes early structure/ruler formation;
- the DESI compressed likelihood carries fiducial-model assumptions.

## Base Janus BAO Map

The current implemented base map is:

```text
u_e = u(z)
chi = 2(u0 - u_e)
r_open = sinh(chi)
D_M/r_d = scale * r_open / sqrt(1 - 2q0)
D_H/r_d = scale / E_Janus(z)
D_V/r_d = [z * (D_M/r_d)^2 * (D_H/r_d)]^(1/3)
```

Status: implemented, source-anchored, but not proven as the final BAO observable map.

## Candidate Effective-Ruler Maps

### C0: Naive Constant Ruler

```text
S_Q(z) = S0
prediction_Q = base_Q * S0
```

Interpretation: direct BAO use with one global ruler scale.

Expected use: baseline/falsification pressure.

### C1: Gauge Scalar Ruler

```text
S_Q(z) = S0 * sqrt(a) = S0 / sqrt(1+z)
```

Interpretation: minimal use of Eq. 40 through `c_hat proportional a^-1/2` and characteristic-time scaling.

Status: physically motivated toy map. Existing fit shows it is not sufficient alone.

### C2: Quantity-Dependent Gauge Ruler

```text
S_DM(z) = A_DM * f_DM(a)
S_DH(z) = A_DH * f_DH(a)
S_DV(z) = [S_DM(z)^2 S_DH(z)]^(1/3)
```

Interpretation: transverse and radial BAO may not share the same effective conversion if Janus changes length/time/speed gauges differently.

Status: preferred derivation target.

Current score status:

- C2 with `f_DM = f_DH = sqrt(a)` is too rigid.
- C2b with fitted transverse/radial powers improves over C1/C2 but remains poor.
- At fixed supernova-like `q0 = -0.087`, C2b is still very poor.

Interpretation: the BAO problem is probably not only an effective-ruler scale. The Janus map may also need a revised radial/transverse observable definition, a revised sound-horizon formation model, or a correction to the current base `D_M/D_H` interpretation.

### C3: Empirical Inverse Map

```text
S_Q(z) = A_Q + B_Q z
```

Interpretation: not a physical theory. It infers what a Janus ruler must look like if Janus is assumed true.

Status: diagnostic only.

## First Derivation Target

Derive or reject `C2` from verified Janus assumptions:

1. decide whether BAO ruler is a length, time, horizon, or mixed observable in the variable-constants regime;
2. derive transverse scaling for `D_M/r_d`;
3. derive radial scaling for `D_H/r_d`;
4. check whether `D_V` follows the geometric mean relation or needs a Janus-specific replacement;
5. compare to DESI residual inversion.

If `C2` cannot be derived, move to `C4`: rederive `D_M`, `D_H`, and `D_V` themselves in the variable-constants Janus gauge instead of multiplying the current base map by an effective ruler.

## C4: Gauge-Modified Observable Map

```text
dchi -> a(u)^p_T dchi
D_H -> a(z)^p_R / E(z)
D_M -> sinh(integral dchi_gauge)
D_V -> [z D_M^2 D_H]^(1/3)
```

Current score status:

- C4 improves slightly over C2b.
- Best grid result still prefers `q0 ~= -0.001`.
- At fixed `q0 = -0.087`, C4 remains poor.

Interpretation: modifying `D_M` and `D_H` directly is more promising than only changing the ruler, but this C4 version is still not enough. The likely missing ingredient is not a simple gauge power. Candidate next targets are:

1. redshift definition in variable-constants regime;
2. sound-horizon formation in Janus instead of fixed `r_d`;
3. compressed DESI fiducial-map assumptions;
4. covariance/full-likelihood effects beyond the current compressed file.

## C5: Redshift Remap Diagnostic

```text
1 + z_geom = (1 + z_obs)^gamma
```

Modes tested:

- `D_M` and `D_H` use `z_geom`;
- `D_V` compression uses either `z_obs` or `z_geom`.

Current score status:

- Best grid result keeps `gamma` close to 1 and prefers `q0 ~= -0.001`.
- The fit is much worse than C4.
- At fixed supernova-like `q0 = -0.087`, C5 is rejected very strongly.

Interpretation: redshift remapping alone is not the missing BAO ingredient. The next target should be `C6`: sound-horizon/ruler formation in Janus, DESI fiducial compression, or full uncompressed likelihood.

## C6: Common Sound-Horizon/Ruler Diagnostic

```text
S(z) = A * (1 + z)^p
```

Interpretation: the BAO ruler is allowed to evolve as one common effective sound-horizon scale. `p=0` is a constant `r_d` and is exactly the global BAO normalization already fitted.

Current score status:

- Constant `r_d` cannot solve the BAO shape tension.
- A common evolving ruler improves over C0/C5 but remains worse than C4.
- Best grid result still prefers `q0` close to zero.
- At fixed supernova-like `q0 = -0.087`, C6 remains poor.

Interpretation: the missing BAO ingredient is not a single common sound-horizon power. Next targets should be a quantity-dependent ruler derivation, DESI fiducial compression, or full uncompressed likelihood.

## C7: Anisotropic Linear Ruler With Derived `D_V`

```text
S_DM(z) = A_DM + B_DM z
S_DH(z) = A_DH + B_DH z
S_DV(z) = [S_DM(z)^2 S_DH(z)]^(1/3)
```

Interpretation: transverse and radial rulers are allowed different first-order evolution, but `D_V` is not fitted independently.

Current score status:

- C7 is the best constrained BAO candidate so far.
- It beats C4/C5/C6 while keeping the compressed `D_V` relation derived from `D_M` and `D_H`.
- Best grid result is near the Janus/SN branch; `q0=-0.087` remains competitive.

Interpretation: this is the current best diagnostic target, not an admissible prediction. The next task is to derive the signs and slopes of `S_DM` and `S_DH` from Janus variable-constants physics, instead of leaving them phenomenological.

## C8: Source-Gauge No-Fit Test

Rules:

- fix `q0 = -0.087` from the M18 supernova source value;
- fix powers from source gauge logic, especially X2026 Eq. 40;
- fit only one global BAO normalization because `H0*r_d` is not fixed here.

Current score status:

- Direct source-gauge candidates do not yet solve DESI BAO.
- Best no-fit candidate is common `sqrt(a)`, but it remains poor.
- Therefore C7 remains only a target pattern to derive, not a physical result.

Interpretation: no artificial rescue is accepted. We either derive the anisotropic ruler from Janus equations or mark this BAO route as unresolved.

## Failure Criteria

A candidate map is rejected or downgraded if:

- it uses too many fitted degrees of freedom;
- it improves DESI but worsens SNe or CMB without explanation;
- it cannot be traced to verified Janus equations;
- it depends on Lambda-CDM early-universe calibration while claiming to replace it.
