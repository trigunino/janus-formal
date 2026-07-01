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

## Survey Hard Targets

KiDS-1000 cosmic shear is now a compressed low-`S8` hard target:

- Source: KiDS-1000 cosmic shear data products / cosmology page.
- Observable: `S8 = sigma8 * sqrt(Omega_m / 0.3)`.
- Fiducial COSEBIs result: `S8 = 0.759 +0.024/-0.021`.
- Implementation: `scripts/build_kids1000_s8_target.py` writes `outputs/reports/kids1000_s8_target.json`.
- Data-product inventory: `scripts/build_kids1000_data_products_inventory.py` writes FITS HDU dimensions for `COVMAT`, `En`, `xiP/xiM`, `PeeE` and `NZ_SOURCE`.
- COSEBIs contract: `scripts/build_kids1000_cosebis_contract.py` extracts `En`, `COVMAT` and `NZ_SOURCE` into a structurally valid no-fit survey contract.
- Janus same-order vector: `scripts/build_kids1000_janus_cosebis_proxy_vector.py` writes a 300-component no-fit proxy vector in the exact KiDS `En` order.
- COSEBIs operator: `src/janus_lab/cosebis.py` implements the log-COSEBIs `T_+`, `T_-` transform from `xi_+/-` to `E_n`; `scripts/build_kids1000_cosebis_operator_report.py` records the KiDS settings `theta=[0.5,300] arcmin`, `n_max=5`, and scale-cut dimension 75.
- Limber/Hankel bridge: `src/janus_lab/weak_lensing_spectra.py` implements `P_Weyl(k,z) -> P_kappa^ij(ell) -> xi_+/-^ij(theta)`; `scripts/build_kids1000_janus_limber_xi_cosebis.py` sends a parametric Weyl scaffold through KiDS `n(z)` and the COSEBIs operator.
- Janus-Holst Weyl shape: `scripts/build_kids1000_janus_holst_weyl_cosebis.py` replaces the toy Weyl scaffold with the current Holst `mu_JH(k,a)`, torsion `Omega_T(a)` and growth `D_JH(k,a)` branch, then maps it through KiDS COSEBIs.
- Diagnostic chi-square: `scripts/build_kids1000_janus_holst_shape_chi2.py` slices the KiDS covariance to 75 modes and reports unit-amplitude plus best-single-amplitude diagnostics only.
- Residual audit: the same script writes per-mode residuals/pulls and tomographic max-bin scans; the current Janus-Holst shape is acceptable only for bin-1-only diagnostics and degrades as bins 2-5 enter.
- Nuisance audit: `scripts/build_kids1000_janus_holst_nuisance_audit.py` adds explicit diagnostic pair-bin and mode-tilt templates; the current improvement is mode-like, not a valid IA/baryon closure.
- Mode-cut audit: `scripts/build_kids1000_janus_holst_mode_cut_audit.py` scans COSEBIs `n<=1..5`; even aggressive cuts remain poor, so the issue is not only the highest retained mode.
- Eta scan: `scripts/build_kids1000_janus_holst_eta_scan.py` scans inspected `eta_holst` branches with a refitted amplitude; `eta_holst=0` improves the diagnostic shape but is not a value-slip Green-kernel closure.
- Best-eta localization: the same eta scan shows bins 1-2 can be made acceptable diagnostically, while the failure reappears when bin 3 enters and remains concentrated in mixed/high tomographic pairs.
- Tilt scan: `scripts/build_kids1000_janus_holst_tilt_scan.py` scans a Weyl spectral-index diagnostic at `eta_holst=0`; the best inspected tilt improves only marginally, so a one-parameter k-tilt is not enough.
- Source-redshift shift scan: `scripts/build_kids1000_janus_holst_nz_shift_scan.py` applies global post-hoc shifts to KiDS `n(z)` at `eta_holst=0`, tilt `0.5`; chi2 improves monotonically for large positive shifts, pointing to a geometry/tomography mismatch rather than an admissible photo-z nuisance.
- Geometry scan: `scripts/build_kids1000_janus_holst_geometry_scan.py` scans Janus `q0` in the KiDS distance kernel; opening the geometry improves only marginally, so `q0` drift alone does not explain the tomographic mismatch.
- Redshift-kernel scan: `scripts/build_kids1000_janus_holst_redshift_kernel_scan.py` multiplies the Limber integrand by post-hoc `(1+z)^p`; large negative powers improve diagnostics, indicating the current kernel likely overweights high-redshift contribution.
- Distance-kernel audit: `scripts/build_kids1000_janus_holst_distance_kernel_audit.py` exposes a named `angular_lens` efficiency kernel equivalent to the physically motivated `p=-2` case; it improves the diagnostic but does not close KiDS.
- Kernel residual audit: `scripts/build_kids1000_janus_holst_kernel_residual_audit.py` localizes named kernel variants; `angular_lens` is best, but the 2-3 tomographic pair remains the dominant failure.
- Kernel closure decision: `scripts/build_kids1000_janus_holst_kernel_closure_decision.py` freezes `eta_holst=0`, spectral index `0.5`, and `angular_lens` as a diagnostic candidate only, with explicit `do-not-promote-to-prediction`.
- Pair-2-3 audit: `scripts/build_kids1000_janus_holst_pair23_audit.py` shows the dominant pair is uniformly underpredicted, especially COSEBIs mode 1, with bin-2/bin-3 source overlap about 0.46.
- Pair-amplitude/bin-factor audits: `scripts/build_kids1000_janus_holst_pair_amplitude_audit.py` and `scripts/build_kids1000_janus_holst_bin_factor_audit.py` show a large bin-2 normalization diagnostic, but the fitted factors do not constitute a calibration, IA, or photo-z model.
- Per-bin n(z) shift audit: `scripts/build_kids1000_janus_holst_per_bin_nz_shift_audit.py` confirms bin 2 is the most sensitive post-hoc source-redshift direction; a bin-2 shift improves the diagnostic but is not an admissible photo-z nuisance fit.
- No-fit boundary: `scripts/build_kids1000_janus_holst_no_fit_boundary.py` freezes the diagnostic candidate and explicitly forbids using fitted amplitude, inspected eta/tilt, `angular_lens`, bin-2 shifts, or bin factors as prediction ingredients.
- Value-slip target: `scripts/build_kids1000_janus_holst_value_slip_kernel_target.py` converts the bin-2 symptom into a source-derived kernel target: derive `eta_slip_JH(k,a)` or an equivalent optical projection factor from the Janus-Holst Green problem, without feeding in `Z_MID_BIN2`, bin factors, or KiDS residual scalars.
- Value-slip scaffold: `src/janus_lab/value_slip.py` and `scripts/build_kids1000_janus_holst_value_slip_scaffold.py` add the non-fit code path from derivative-slip source to `Sigma_JH`, but prediction remains blocked until the Green kernel is computed from source.
- Projected Green calculation: `scripts/build_p0_eft_ds3_projected_green_calculation.py` evaluates a regulated S3 spectral response; the result is scheme-dependent and does not prove `G_Neumann^Sigma=(3/2)H`.
- Green-kernel closure checklist: `scripts/build_kids1000_janus_holst_green_kernel_closure_checklist.py` lists the blockers before `green_kernel_computed=True`: source-derived boundary conditions, finite-mode Green kernel, fixed projection/renormalization scheme, finite KiDS-grid `eta_slip_JH`, and source-selected `Q_det/Q_cross`.
- Kink-only target: `scripts/build_kids1000_janus_holst_kink_lensing_target.py` opens a safer branch that uses `Delta(partial_n(Psi-Phi))` directly as a kink/refraction source and explicitly avoids coincident Green value-slip, bin shifts, bin factors, and KiDS residual scalars.
- Kink solver scaffold: `src/janus_lab/kink_growth.py` and `scripts/build_kids1000_janus_holst_kink_solver_scaffold.py` encode the ODE mechanics where `delta` is continuous and `d delta / d ln a` receives a membrane jump, but prediction is blocked until `S_kink` and `alpha_Janus(a)` are source-derived.
- Kink source target: `src/janus_lab/kink_source.py` and `scripts/build_kids1000_janus_holst_kink_source_target.py` define the guarded `S_kink * alpha_Janus * delta` jump interface, reject KiDS/fit provenance, and remain non-predictive until the Holst junction source fixes both factors.
- Kink source closure audit: `scripts/build_p0_eft_kink_source_closure_audit.py` links the derivative-jump source, growth `S_kink` formula, and spinless-isotropic `alpha_Janus` branch; it closes the source structure but keeps prediction blocked by the Euler projection coefficient and torsion-energy normalization.
- Closure gates: `scripts/build_kids1000_physics_closure_gates.py` blocks prediction claims until amplitude, value slip, nonlinear/small-scale, IA and baryon policies are fixed before residual inspection.
- Boundary: the technical `P_Weyl -> xi_+/- -> COSEBIs -> chi2` path has a Janus-Holst shape branch; a final KiDS prediction still needs source-derived primordial amplitude, nonlinear/small-scale closure, and the open value-slip Green kernel.

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
