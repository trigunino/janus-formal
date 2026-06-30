# Janus Sigma8 Observable Map v1

Status: working derivation target.

Goal: define what can legitimately replace or compare to standard `sigma8`/`S8` in Janus without importing Lambda-CDM assumptions silently and without using numerical transforms as rescue terms.

## No-Rustine Rule

The following are diagnostics only, not evidence:

- choosing a Gaussian/lognormal/bounded transform because it reaches a desired number;
- fitting an IC amplitude after looking at the desired observable;
- claiming standard `sigma8 = 0.8` is a Janus target before deriving the observable map;
- treating a positive-density scaffold as Janus physics without source-derived justification.

Only observables derived from stated Janus assumptions can become admissible predictions.

## Standard Sigma8 Compression

Standard `sigma8` is the RMS of a matter density contrast smoothed over `8 h^-1 Mpc` spheres:

```text
sigma8 = RMS[ W_R * delta_m ], R = 8 h^-1 Mpc
```

This assumes a single effective matter density field. Janus has at least two sectors and two metric sheets, so the scalar `delta_m` must be redefined before comparison.

## Source-Backed Ingredients

This is not a derivation from zero. The local Janus library already contains these ingredients:

- `M15` / `M30`: two metric/geodesic families and Janus same-sign attraction / opposite-sign repulsion.
- `M22`: denser negative sector gives a shorter Jeans time, so negative structures form first.
- `M07`: verified-concept anchor for negative/inverse gravitational lensing, positive lensing from holes in negative-mass distributions, large-scale simulations and two-point correlation.
- `M20`: verified-concept anchor connecting negative-sector gravitational instability to CMB inhomogeneities and claiming negative-sector lensing effects.

The missing step is not inventing these ideas. It is deriving the observable map: which Janus field combination corresponds to galaxy clustering, weak lensing and the compressed standard `sigma8/S8`.

## Lensing Primitive To Derive

Source constraints:

- A negative-mass concentration produces negative/diverging lensing for positive-sector photons.
- A hole in a negative-mass distribution can mimic positive lensing.
- Therefore observed lensing cannot be mapped blindly to `delta_plus`.

Admissible first primitive:

```text
Phi_lensing_plus = metric/geodesic potential seen by positive-energy photons
source(Phi_lensing_plus) must keep both rho_plus and rho_minus_abs explicit
delta_lens_plus = ((rho_plus - rho_minus_abs) - mean(rho_plus - rho_minus_abs)) / mean(rho_plus + rho_minus_abs)
```

Implementation status: `src/janus_lab/lensing.py` implements this centered weak-field source diagnostic and periodic 2D/3D potentials for positive-sector photons.
`scripts/diagnose_lensing_sigma8_observable.py` measures `sigma8` on this field as a diagnostic, without fitting it to a survey target.

Weak projection primitive:

```text
kappa_plus_proxy(x_perp) = integral W(chi) delta_lens_plus(x_perp, chi) dchi / integral W(chi) dchi
```

Current implementation: `scripts/diagnose_weak_lensing_projection.py` uses `W=1` as a uniform line-of-sight diagnostic only.

Janus open-distance kernel diagnostic:

```text
r(z) = sinh(2 * (u0 - u(z)))
K(z_l,z_s) = r(z_l) * sinh(2 * (u(z_l) - u(z_s))) / r(z_s), for z_l < z_s
kappa_janus_kernel_proxy(x_perp) = weighted_mean_axis(delta_lens_plus, K)
```

Implementation status: `scripts/diagnose_janus_tomographic_lensing_kernel.py` computes this geometric kernel for a single source redshift.

Weak shear proxy:

```text
gamma1_hat = ((kx^2 - ky^2) / k^2) * kappa_hat
gamma2_hat = (2 kx ky / k^2) * kappa_hat
```

Implementation status: `scripts/diagnose_janus_shear_proxy.py` computes this E-mode proxy from `kappa_janus_kernel_proxy`.

Source-distribution kernel:

```text
K_dist(z_l) = integral n(z_s) K(z_l,z_s) dz_s
kappa_dist_proxy = projected(delta_lens_plus, K_dist)
gamma_dist_proxy = shear(kappa_dist_proxy)
```

Implementation status: `scripts/diagnose_janus_source_distribution_lensing.py` accepts an explicit `n(z_s)` and does not fit it.

Absolute convergence scaffold:

```text
kappa_abs_proxy = sum_i [(3/2) Omega_abs (H0/c)^2 Delta_chi_i (1+z_i) K_dist(z_i) delta_lens_plus_i]
```

Implementation status: `scripts/diagnose_janus_absolute_convergence.py` applies the standard weak-lensing prefactor to the Janus source and open-distance geometry.

Normalization audit:

```text
Janus-backed: positive photon metric sheet, signed weak-field source, M18 open marker distance.
Standard scaffold: E-mode shear relation, absolute weak-lensing prefactor.
Missing: tensor optical normalization, survey n(z_s), growth/transfer model, likelihood.
```

Implementation status: `scripts/build_lensing_normalization_audit.py` writes the current admissibility boundary.

Derivation target: `formal/axioms/lensing_tensor_derivation_target.md` lists the tensor/optical gates that must be closed before replacing this scaffold.

Rejected shortcut:

```text
S8_eff = sigma8_plus * free_correction
```

Reason: this would fit the target after the fact instead of deriving the observed lensing field.

## Candidate Janus Observables

### S0: Naive Positive-Sector Sigma8

```text
sigma8_plus = RMS[ W_R * delta_plus ]
```

Status: diagnostic only.

Failure mode: it ignores the negative sector and imports the standard matter-field interpretation.

### S1: Signed-Source Sigma8

```text
delta_signed = (rho_plus - rho_minus_abs) / mean(rho_plus + rho_minus_abs)
sigma8_signed = RMS[ W_R * delta_signed ]
```

Status: current internal diagnostic.

Use: tests the weak-field Janus source term used by the PM kernel.

Failure mode: not automatically equal to observed galaxy clustering, weak lensing `S8`, or CMB-normalized matter power.

### S2: Two-Field Structure Tuple

```text
J8 = (sigma8_plus, sigma8_minus_abs, corr(delta_plus, delta_minus_abs), sigma8_signed)
```

Status: preferred diagnostic summary until an observation map is derived.

Use: keeps the two-sector nature explicit instead of collapsing it too early into one scalar.

### S3: Visible-Tracer Sigma8

```text
sigma8_visible = RMS[ W_R * delta_visible ]
```

Status: needs-derivation.

Question: what is the relation between visible baryonic tracers and the positive-sector density field in Janus?

### S4: Lensing-Effective Sigma8 / S8

```text
delta_lensing_eff = F[g(+), g(-), rho_plus, rho_minus_abs]
sigma8_lens_plus = RMS[ W_R * delta_lens_plus ], R = 8 h^-1 Mpc
kappa_plus_proxy = projected(delta_lens_plus)
kappa_janus_kernel_proxy = projected(delta_lens_plus, K_janus_open)
gamma_janus_proxy = shear(kappa_janus_kernel_proxy)
gamma_dist_proxy = shear(projected(delta_lens_plus, K_dist))
kappa_abs_proxy = absolute_normalized(delta_lens_plus, K_dist)
S8_eff = sigma8_lens_eff * sqrt(Omega_eff / 0.3)
```

Status: partially reduced to `delta_lens_plus` as a weak-field diagnostic; still needs tensor/geodesic derivation before survey-level `S8_eff`.

Question: which metric, source combination, and light-propagation equation correspond to weak-lensing observations?

## Current Numerical Findings

These are constraints on toy IC families, not Janus predictions.

- Gaussian direct `sigma8=0.8` at `175^3` reaches the target but is density-unsafe: many cells have `delta < -1`.
- Lognormal positive-density IC reaches `sigma8 ~= 0.8`, but sector anti-correlation becomes weak.
- Bounded exact anti-correlation with `delta > -1` cannot reach `sigma8=0.8` in the tested tanh family; capacity is about `0.163`.

Interpretation: the tension is real. We should not hide it with a transform. The next derivation target is the observation map, not a new numerical rescue form.

## Failure Criteria

A `sigma8`/`S8` candidate is rejected or downgraded if:

- it does not state which field is being smoothed;
- it violates positive density where positive density is required;
- it erases the negative sector without a source-derived observation map;
- it reaches the target only by a free transform chosen after diagnostics;
- it cannot be connected to weak lensing, galaxy clustering, or CMB normalization.

## Next Derivation Target

Derive or reject a survey-level Janus weak-lensing map:

1. start from `delta_lens_plus`, not `delta_plus`;
2. validate or replace the current M18 open-distance geometric kernel;
3. replace the explicit test source distribution by a real survey `n(z_s)` only when the data source is stated;
4. add growth model only if source-derived;
5. replace the current E-mode shear proxy by the full positive-photon geodesic shear if the tensor derivation changes it;
6. replace the standard-prefactor scaffold if the tensor Janus derivation changes the normalization;
7. define `S8_eff` only after the kernel, observable field and normalization are fixed;
8. compare `J8`, `sigma8_lens_plus`, `kappa_plus_proxy`, `kappa_janus_kernel_proxy`, `gamma_janus_proxy`, `gamma_dist_proxy` and `kappa_abs_proxy` before compressing to one scalar.
