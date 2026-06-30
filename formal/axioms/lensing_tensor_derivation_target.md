# Janus Lensing Tensor Derivation Target

Status: derivation target, not a completed proof.

Goal: replace the current standard weak-lensing normalization scaffold with a Janus-derived optical normalization for positive-sector photons.

Evidence policy: derivation anchors for this file are `M15`/`M30` for bimetric positive geodesics and determinant-coupled field equations, `M18` for open positive-sector geometry, and `M07` only as an accepted-publication concept anchor for negative lensing. Recent 2025/2026 author documents are roadmap inputs unless independently accepted or verified.

## Starting Assumptions

- Positive-energy photons follow null geodesics of `g(+)`.
- The positive-sector weak-field source keeps both absolute densities:

```text
Delta Phi_+ = 4 pi G (rho_+ - |rho_-|)
```

- Current distance geometry uses the M18 open marker:

```text
r(z) = sinh(2 * (u0 - u(z)))
```

These ingredients are source-backed or source-derived, but they do not yet fix the survey-level convergence normalization.

## Current Scaffold To Replace

The implemented absolute convergence proxy assumes:

```text
kappa_abs_proxy =
sum_i [(3/2) Omega_abs (H0/c)^2 Delta_chi_i (1+z_i)
       D_l D_ls / D_s * delta_lens_plus_i]
```

This is the standard weak-lensing prefactor applied to the Janus source and M18-style open geometry. It is useful as a controlled diagnostic, not as a final Janus prediction.

## Tensor Derivation Gates

G1. Optical metric sheet:

```text
g(+)_{mu nu} k^mu k^nu = 0
k^alpha nabla^{(+)}_alpha k^mu = 0
```

G2. Optical tidal matrix:

```text
T^A_B = - R^{(+)}_{mu alpha nu beta}
        e_A^mu k^alpha e_B^nu k^beta
```

G3. Jacobi map:

```text
d^2 D^A_B / d lambda^2 = T^A_C D^C_B
```

G4. Janus source reduction:

```text
T^A_A  ->  C_J(a,z) * (rho_+ - |rho_-|)
```

The required result is the explicit coefficient `C_J(a,z)`, including any determinant-ratio terms from the coupled field equations.

Null contraction:

```text
G(+)_{mu nu} k^mu k^nu = R(+)_{mu nu} k^mu k^nu
```

because `g(+)_{mu nu} k^mu k^nu = 0`.

Positive-sheet source contraction:

```text
R(+)_{kk} = chi [T(+)_{kk} + B T(-)_{kk}]
B = sqrt((-g_-)/(-g_+))
```

In the dust-like equal-projection, zeroth-determinant limit:

```text
T(+)_{kk} = A rho_+
T(-)_{kk} = -A |rho_-|
B = 1
R(+)_{kk} = chi A (rho_+ - |rho_-|)
```

This is the precise condition under which the optical source matches the implemented weak-field lensing source.

Before imposing equal projection, the source is:

```text
T(+)_{kk} = A_+ rho_+
T(-)_{kk} = -A_- |rho_-|
Q_cross = A_- / A_+
R(+)_{kk} = chi A_+ [rho_+ - B Q_cross |rho_-|]
```

So `Q_cross=1` is an assumption, not a free fit. It is admissible only under an
explicit comoving/equal-projection optical limit.

Implemented code surfaces:

```text
cross_sector_optical_projection_factor(A_plus, A_minus) = A_minus / A_plus
equal_comoving_cross_projection_factor(z) = 1
```

The default numerical source uses the equal-projection limit. Any departure from
that limit must pass an explicit `cross_projection_ratio`.

Local relative-velocity path:

```text
beta_parallel = beta_vec . n_photon
Q_cross = gamma_-^2 * (1 - beta_parallel)^2
```

where `beta_parallel` is the negative-sector velocity component along the
positive photon direction in a local positive orthonormal frame. This is
implemented by `relative_velocity_cross_projection_factor` and
`relative_velocity_cross_projection_from_vectors`. Physical km/s velocities can
use `relative_velocity_cross_projection_from_velocities_km_s`. Dimensionless PM
velocities must not be passed as km/s before calibration. This path is not usable
in a survey prediction until the negative-sector velocity field is source-derived.
`diagnose_pm_state_qcross.py` applies the same bridge to a vectorized PM state
and reports negative-sector `Q_cross` statistics. It remains diagnostic until
the PM time unit and negative-sector four-velocity field are derived physically.
`diagnose_pm_qcross_lensing_source.py` then deposits the corresponding grid
source `rho_+ - Q_cross rho_-`; this is a PM diagnostic bridge, not a final
tensor optical source.
`run_pm_qcross_lensing_pipeline.py` runs this bridge through a short vectorized
PM evolution and reports the source metrics at each step.
`run_pm_qcross_absolute_shear.py` applies the absolute Janus lensing coefficients
to the final PM `Q_cross` source and computes a shear proxy. Its absolute chain
uses bounded anti-correlated Gaussian displacement IC with zero initial velocity,
so negative-sector velocities are produced by the PM evolution rather than an
imposed demo velocity pattern.
`run_pm_qcross_absolute_shear_resolution.py` compares this observable across
grid choices and records whether the tested grid reaches the sigma8/lensing
resolution requirement.
The working physical PM time calibration is now

```text
t_code = H0 * t_physical
Delta t_physical = Delta t_code / H0
v_unit = L_box / H0^-1 = H0 L_box
```

implemented by `hubble_time_gyr` and `pm_hubble_velocity_unit_km_s`.

Audit:

```text
outputs/reports/lensing_qcross_audit.md
```

Raw FLRW lapse path:

```text
u_s,eta = a_s
A_s = (u_s.k_+)^2
Q_cross = A_- / A_+ = (a_-/a_+)^2
```

This is only an algebraic path. It must not be combined with the M20
`a_-/a_+ ~= 1/100` scale-ratio claim until the time gauge and density-volume
mapping are derived.

Numeric warning:

```text
outputs/reports/lensing_scale_ratio_warning.md
```

Direct insertion would give `Q_det=1e-8`, `Q_cross=1e-4`, or stacked
`W_-=1e-12`. These are not Janus predictions; they are forbidden shortcut
values unless the metric gauge, volume convention and source-density mapping are
derived from the field equations.

First-order determinant bookkeeping:

```text
sqrt((-g_-)/(-g_+)) =
1 + (epsilon/2) * (tr_-(gamma_-) - tr_+(gamma_+)) + O(epsilon^2)
```

Homogeneous FLRW determinant ratio:

```text
g_+ proportional -a_+^8 * det(spatial)
g_- proportional -a_-^8 * det(spatial)
B = sqrt((-g_-)/(-g_+)) = (a_-/a_+)^4
```

Source/gauge warning:

```text
M20 gives a_-/a_+ ~= 1/100 from the CMB-imprint scale argument.
M30 uses sqrt(|g_bar|/|g|) ~= 1 in the Newtonian approximation.
```

These statements cannot be combined naively. Until the metric-volume convention
for the optical source is derived, `Q_det` must remain open and `(a_-/a_+)^4`
must not be inserted as a lensing amplitude.

Current convention audit:

```text
outputs/reports/lensing_qdet_convention_audit.md
```

Accepted current numerical convention: `B=1` only as the Newtonian
effective-density convention. This keeps existing PM/lensing diagnostics
consistent with M30 Eq. 124 but does not close the tensor normalization.
In code this is exposed as:

```text
negative_density_convention = "positive_effective"
```

The alternate mode:

```text
negative_density_convention = "negative_proper"
```

applies `B` explicitly and must only be used when the input density is a
negative-sector proper density rather than a positive-sector effective source.

Positive-sheet source with determinant ratio:

```text
R(+)_{kk} proportional rho_+ - B |rho_-|
```

The current source `rho_+ - |rho_-|` is recovered only for `B=1`.

First-order unresolved correction:

```text
R(+)_{kk} =
chi A [rho_+ - |rho_-|
       - (epsilon/2) |rho_-| (tr_-(gamma_-) - tr_+(gamma_+))]
```

if equal optical projections are kept but the determinant ratio is expanded to first order.

Implementation status: `scripts/check_symbolic_formulas.py` checks the null contraction, the signed-density limit, the scalar determinant-ratio expansion, and the FLRW determinant factor. `positive_photon_lensing_source_grid_with_determinant_ratio` exposes `rho_+ - B|rho_-|`. The missing physics is the source-derived law for `B(x,z)`.

Standard scaffold coefficient currently used in code:

```text
4 pi G rho0 / c^2
= 4 pi G [3 H0^2 Omega_abs / (8 pi G)] / c^2
= (3/2) Omega_abs (H0/c)^2
```

Implementation status: `standard_weak_lensing_prefactor` exposes the base term.
`janus_tensor_lensing_prefactor` exposes the non-fit factorization
`C_J=C_std Q_source Q_det Q_cross Q_proj Q_dist`. Current working branch uses
the positive-effective density convention for `Q_det`, velocity-derived
`Q_cross` in the PM source, positive geodesic/Jacobi `Q_proj=1+z`, and M18 open
distance coefficients. Janus still has to prove any non-unity tensor factors
globally before a survey-level `S8_eff` claim.

Positive FLRW null-geodesic projection:

For the positive-sector FLRW optical metric in conformal form,

```text
ds_+^2 = a(eta)^2 [d eta^2 - d chi^2 - S_k(chi)^2 d Omega^2]
```

radial null geodesics obey:

```text
d chi / d eta = 1
k^eta proportional a^-2
E = -u.k proportional a k^eta proportional a^-1
E(z)/E0 = 1/a = 1+z
```

Therefore the raw Ricci-focusing projection is:

```text
A(z)/A0 = (u.k)^2/(u0.k0)^2 = (1+z)^2
```

This is the positive-geodesic result. It is not identical to the final standard convergence integrand factor.

Jacobi reduction to comoving distance:

```text
rho_phys / rho0 = a^-3
(u.k)^2 / (u0.k0)^2 = a^-2
(d lambda / d chi)^2 / today = a^4

a^-3 * a^-2 * a^4 = a^-1 = 1+z
```

So, under the positive FLRW optical ansatz and standard Jacobi distance-variable reduction:

```text
Q_proj,std(z) = 1/a(z) = 1 + z
```

Accepted working result: `positive_flrw_photon_energy_factor`, `positive_flrw_ricci_projection_factor`, and `positive_flrw_jacobi_reduced_projection_factor` expose this derivation. It is valid for the current positive-geodesic M18 optical ansatz and should be re-opened only if a peer-reviewed Janus optical metric changes the affine-to-comoving reduction.

Admissible Janus coefficient decomposition:

```text
C_J(a,z) = C_std * Q_source * Q_det * Q_cross * Q_proj * Q_dist
```

with the more explicit unresolved source side:

```text
source_J = rho_+ - Q_det * Q_cross * |rho_-|
```

Code consolidation:

```text
W_- = negative_sector_lensing_weight_factor(...)
source_J = rho_+ - W_- |rho_-|
```

Effective-density absorption:

```text
rho_-^eff = Q_det rho_-^proper
rho_source = rho_+ - Q_cross rho_-^eff
```

Thus `Q_det` is not lost in the `positive_effective` branch; it has been moved
into the definition of the negative density supplied to the positive-sector
source. The remaining open question in that branch is `Q_cross`.

Derivation branch map:

```text
outputs/reports/lensing_qdet_qcross_derivation_map.md
```

No factor may be tuned to data. Each factor must be derived or fixed by an explicit survey input before `S8_eff`.

G5. Distance normalization:

```text
D_l, D_s, D_ls
```

For the positive M18 open-FLRW optical ansatz:

```text
chi(z) = 2 * (u0 - u(z))
S_k(chi) = sinh(chi)
R0 = c / [H0 * sqrt(1 - 2q0)]
D_M(z) = R0 * sinh(chi(z))
D_A(z) = D_M(z) / (1+z)
D_A(z_l,z_s) = R0 * sinh(chi_s - chi_l) / (1+z_s)
```

The angular lensing kernel and comoving kernel obey:

```text
D_A,l * D_A,ls / D_A,s
= [D_M,l/(1+z_l)] * [D_M,ls/(1+z_s)] / [D_M,s/(1+z_s)]
= (1/(1+z_l)) * D_M,l * D_M,ls / D_M,s
```

So the current M18 distance kernel is the comoving optical kernel:

```text
K_M18 = D_M,l * D_M,ls / D_M,s
```

Accepted working result: `janus_open_angular_diameter_distance_mpc`, `janus_open_angular_diameter_distance_between_mpc`, `janus_open_comoving_lensing_distance_kernel_mpc`, and `janus_open_angular_lensing_distance_kernel_mpc` expose this relation for the current M18 positive optical geometry.

G6. Weak shear relation:

```text
gamma = operator(kappa)
```

may remain the standard E-mode relation only if the Janus optical derivation reduces to the same 2D screen geometry.

## Admissibility Rule

`S8_eff` is not admissible until G1-G6 are closed and a stated survey source distribution plus covariance are used.

## Immediate Work

1. Resolve the `Q_det` metric-volume convention beyond the current `positive_effective` weak-field convention.
2. Derive or constrain `Q_cross` from the relative positive/negative sector four-velocities via the `L_minus_to_plus` tetrad/covector map; the code now exposes the equal-projection limit but does not prove it globally.
3. Prove or reject non-unity factors in `C_J=C_std Q_source Q_det Q_cross Q_proj Q_dist`.
4. Replace diagnostic PM initial states/source distributions by source-derived ICs and declared survey `n(z)`.
5. Add observed data vector, covariance, mask/window treatment, and no-fit comparison rule before any `S8_eff` claim.

## Coupled Field Equation Gate

The coupled-field-equation layer must close before the optical source is final:

```text
G_plus = chi * coupled_source_plus(g_plus, g_minus, T_plus, T_minus)
G_minus = chi * coupled_source_minus(g_minus, g_plus, T_minus, T_plus)
nabla_plus.G_plus = 0
nabla_minus.G_minus = 0
```

The determinant ratio is therefore not just an amplitude:

```text
B_plus = sqrt(-g_minus / -g_plus)
B_minus = sqrt(-g_plus / -g_minus)
B_plus * B_minus = 1
```

The stationarity/symmetric-copy limit may set `B_plus=B_minus=1`, but the
instationary asymmetric case must satisfy both Bianchi constraints. Current PM
diagnostics implement only the weak-field sign structure and explicit
determinant-density branches.

Bianchi closure target:

```text
outputs/reports/bianchi_closure_target.md
outputs/reports/interaction_tensor_attempt_audit.md
```

Accepted until closure: weak-field PM/lensing diagnostics only. Blocked until
closure: exact tensor lensing normalization and survey-level `S8_eff`.
4. Keep `Q_proj=1+z` and the M18 open optical kernel as accepted working results unless a peer-reviewed Janus optical geometry supersedes them.
5. Define survey-facing `S8_eff` only with explicit source-redshift distribution, masks/noise/covariance, and the derived prefactor.
