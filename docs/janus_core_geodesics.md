# Janus Core: Geodesics And Signed Masses

This note tracks the core Janus mechanism that was not covered by the first expansion/BAO traceability pass.

## Scope

The expansion code currently uses only the homogeneous cosmology consequences of Janus. The separate weak-field signed-sector layer now implements point-source, pairwise, periodic Poisson-grid 2D/3D, particle-mesh 2D/3D and comoving PM 2D/3D prototype diagnostics, but it does not yet implement:

- geodesic integration in the two metrics;
- local Schwarzschild-like positive/negative mass fields;
- calibrated Vlasov-Poisson galaxy dynamics or production cosmological N-body dynamics;
- lensing through negative-mass regions.

Those are core Janus claims and must be tracked separately from BAO/SNe.

## Source Hierarchy

| Source | Role |
|---|---|
| `M15` | Lagrangian derivation of two coupled field equations; first clean trace of the interaction laws in this project. |
| `M22` | Consistency overview, large-scale structure, Jeans time asymmetry, Vlasov-Poisson consequences. |
| `M30` / `X2025-bimetric-hal` | 2024/2025 bimetric formulation, geodesic separation, Newtonian approximation, interaction laws, dipole repeller. |
| `M31` / `X2025-symplectic-hal` | Janus symplectic group, torsors, symmetry basis for energy/momentum/charge transformations. |
| `X2025-kinetic-galactic` | Kinetic theory / Vlasov-Poisson route for galactic dynamics. |

## Single-Metric Failure

The standard one-metric attempt puts positive and negative sources in one Einstein equation:

```text
G_mu_nu = chi [T_mu_nu^(+) + T_mu_nu^(-)]
```

In this setup, the negative-mass field gives one geodesic family for all test particles. The result is the Bondi runaway problem:

- positive mass attracts both signs;
- negative mass repels both signs;
- a `+m / -m` pair accelerates together.

Sources:

- `M15`, Eqs. 1-3 and discussion of Bondi runaway.
- `M30`, Eqs. 75-79 and surrounding text.

Status: documented as the failure mode Janus is designed to avoid.

## Bimetric Replacement

Janus replaces the one-metric picture with two metrics:

```text
g_mu_nu^(+) : geodesics for positive masses and positive-energy photons
g_mu_nu^(-) : geodesics for negative masses and negative-energy photons
```

Core statement:

- positive masses follow non-null geodesics of `g(+)`;
- positive-energy photons follow null geodesics of `g(+)`;
- negative masses follow non-null geodesics of `g(-)`;
- negative-energy photons follow null geodesics of `g(-)`.

Sources:

- `M15`, text after Eq. 6.
- `M30`, section 9 introduction to the pair of metrics and distinct geodesics.

Status: not implemented in code yet.

## Coupled Field Equations

The 2015 formulation gives, schematically:

```text
G_mu_nu^(+) = chi [T_mu_nu^(+) + sqrt(-g(-) / -g(+)) T_mu_nu^(-)]
G_mu_nu^(-) = -chi [sqrt(-g(+) / -g(-)) T_mu_nu^(+) + T_mu_nu^(-)]
```

Sources:

- `M15`, Eqs. 4a-4b.
- `M15`, Eq. 5 for signs of densities and pressures.
- `M15`, Eq. 6 for double Newtonian approximation.

The 2024/2025 paper restates a mixed-notation stationary form:

```text
G_mu^nu = chi [T_mu^nu + b^2 Tbar_mu^nu]
Gbar_mu^nu = -chi [T_mu^nu + bbar^2 Tbar_mu^nu]
```

Sources:

- `M30`, Eqs. 105a-105b and Eq. 106.

Status: documented, not implemented as a tensor engine.

## Interaction Laws

The double Newtonian approximation gives:

```text
same sign masses attract
opposite sign masses repel
```

The implemented sign bookkeeping is:

```text
sigma_source = +1 for positive density, -1 for negative density
tau_test_metric = +1 for g(+), -1 for g(-)
coupling = tau_test_metric * sigma_source
```

So the Newtonian-limit coupling matrix is:

| test metric / source density | positive source | negative source |
|---|---:|---:|
| `g(+)` followed by positive sector | `+1` attraction | `-1` repulsion |
| `g(-)` followed by negative sector | `-1` repulsion | `+1` attraction |

With absolute densities `rho_+ >= 0` and `|rho_-| >= 0`, the weak-field Poisson source terms implemented here are:

```text
Delta Phi_+ = 4 pi G (rho_+ - |rho_-|)
Delta Phi_- = 4 pi G (-rho_+ + |rho_-|)
```

This is the normalized point-source convention used by `point_source_potential` and `point_source_acceleration`.

More explicitly:

| Source mass | Test mass | Janus interaction |
|---|---|---|
| positive | positive | attraction |
| negative | negative | attraction |
| positive | negative | repulsion |
| negative | positive | repulsion |

This removes the Bondi runaway by assigning distinct geodesic families to the two signs.

Sources:

- `M15`, after Eq. 6.
- `M30`, after Eqs. 105-106.

Status: implemented as a minimal Newtonian-limit kernel in `src/janus_lab/signed_sector.py`, checked by `scripts/check_symbolic_formulas.py`, and mirrored in `formal/lean/JanusBasic.lean`. This covers sign matrix, weak-field Poisson RHS, point-source potential, and acceleration. This is not a tensor engine or geodesic integrator.

The pairwise dynamic layer also exposes kinetic, potential and total energy helpers. In this convention:

- same-sector potential energy is negative;
- opposite-sector potential energy is positive;
- short leapfrog runs keep small numerical energy drift.

## Large-Scale Consequences

Under the common Janus assumption that the negative sector is denser after decoupling:

```text
|rho(-)| > rho(+) => t_J(-) << t_J(+)
```

Negative matter clusters first, then repels positive matter into walls, filaments, and nodes around void-like regions.

Sources:

- `M22`, Eq. 1 and surrounding text.
- `M15`, discussion after interaction laws.

Status: qualitative in current project; only pairwise, periodic Poisson-grid 2D/3D, particle-mesh 2D/3D and comoving PM 2D/3D prototype diagnostics are implemented, not calibrated large-scale N-body or Vlasov-Poisson evolution.

## Galactic Dynamics Route

The current 2025 kinetic-theory paper is relevant for the "dark matter replacement" claim, but it is not yet wired into code.

Key pieces:

- Vlasov equation in residual velocity variables;
- Poisson equation for the Newtonian potential;
- velocity ellipsoid construction;
- asymptotic velocity plateau compatible with flat rotation curves.

Sources:

- `X2025-kinetic-galactic`, Poisson Eq. 11 and later construction.

Status: not implemented.

## Required Next Implementation

A minimal interaction module now exposes:

```text
Sector = positive | negative
metric_for(sector)
source_coupling(source_sector, test_sector)
newtonian_acceleration(source_sector, test_sector, r_vector, mass_abs)
weak_field_energy(bodies)
leapfrog_step(bodies, dt)
```

Expected behavior:

- same signs: attraction;
- opposite signs: repulsion;
- no runaway pair behavior.

Implemented surface:

- `src/janus_lab/signed_sector.py`
- `src/janus_lab/poisson.py`
- `src/janus_lab/particle_mesh.py`
- `src/janus_lab/particle_mesh_3d.py`
- `src/janus_lab/particle_mesh_3d_vectorized.py`
- `src/janus_lab/cosmological_pm.py`
- `src/janus_lab/cosmological_pm_3d.py`
- `src/janus_lab/field_statistics.py`
- `src/janus_lab/initial_conditions.py`
- `src/janus_lab/physical_units.py`
- `tests/test_signed_sector.py`
- `tests/test_particle_mesh.py`
- `scripts/simulate_two_sector_pairs.py`
- `scripts/simulate_two_sector_poisson_grid.py`
- `scripts/simulate_two_sector_poisson_grid_3d.py`
- `scripts/simulate_two_sector_particle_mesh.py`
- `scripts/simulate_two_sector_particle_mesh_3d.py`
- `scripts/benchmark_vectorized_pm_3d.py`
- `scripts/benchmark_vectorized_pm_3d_progressive.py`
- `scripts/run_vectorized_pm_3d_short_stability.py`
- `scripts/diagnose_particle_mesh_resolution.py`
- `scripts/simulate_two_sector_segregation.py`
- `scripts/analyze_segregation_fields.py`
- `scripts/diagnose_segregation_robustness.py`
- `scripts/compare_segregation_controls.py`
- `scripts/diagnose_control_robustness.py`
- `scripts/simulate_cosmological_pm_prototype.py`
- `scripts/simulate_cosmological_pm_3d_prototype.py`
- `scripts/diagnose_cosmological_pm_robustness.py`
- `scripts/generate_gaussian_initial_conditions.py`
- `scripts/simulate_cosmological_pm_gaussian_ic.py`
- `scripts/generate_gaussian_initial_conditions_3d.py`
- `scripts/simulate_cosmological_pm_3d_gaussian_ic.py`
- `scripts/diagnose_gaussian_ic_seed_robustness.py`
- `scripts/analyze_cosmological_pm_power_observables.py`
- `scripts/analyze_cosmological_pm_3d_power_observables.py`
- `scripts/diagnose_cosmological_pm_3d_power_robustness.py`
- `scripts/calibrate_physical_pm_box.py`
- `scripts/analyze_cosmological_pm_3d_physical_power.py`
- `scripts/diagnose_sigma8_resolution_requirements.py`
- `scripts/generate_sigma8_normalized_ic_3d.py`
- `scripts/generate_lognormal_sigma8_ic_3d.py`
- `scripts/diagnose_bounded_anticorrelated_sigma8_ic_3d.py`
- `scripts/build_sigma8_observable_map_report.py`

Remaining work:

1. verify the Poisson normalization directly against the relevant M15/M30 PDF lines, not only the curated register;
2. implement geodesic integration in `g(+)` and `g(-)`;
3. extend from pairwise/grid Poisson/particle-mesh/segregation/comoving-PM/Gaussian-IC-2D/Gaussian-IC-3D/power-observable/physical-scale diagnostics to Vlasov-Poisson or N-body dynamics for large-scale structure;
4. connect the two-sector dynamics to BAO/ruler formation without fitted rescue terms.
