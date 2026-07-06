# Source Traceability

This file links implemented formulas and working hypotheses to local source IDs.

Status labels:

- `implemented`: formula is represented in code.
- `phenomenological`: fitted or inferred from data, not derived from Janus theory yet.
- `needs-derivation`: concept is plausible under Janus, but not yet mathematically derived in the codebase.
- `needs-verification`: extraction or equation numbering must be checked against the original PDF.
- `verified-source`: formula or concept has been checked against `docs/verified_formula_register.md`.
- `partially-implemented`: a narrow code surface exists, but the full physical object is not implemented.
- `source-derived`: derived in this project from verified source anchors; not quoted as a standalone source equation.
- `accepted-working`: accepted as valid for the current derivation because it follows from reviewed/published source anchors and explicit local algebra; still not observational proof.
- `prototype`: executable numerical scaffold, useful for controlled diagnostics but not yet a calibrated physical solver.

Evidence priority for lensing derivations: `M15`/`M30` for bimetric geodesics and determinant-coupled field equations, `M18` for the positive open-distance geometry, `M07` as an accepted-publication concept anchor for negative lensing, and `M20` as a concept anchor only. Recent 2025/2026 author documents are roadmap inputs unless independently accepted or verified.

Accepted/journal source register: `docs/accepted_journal_sources.md`.

## Implemented Formulas

| Code surface | Formula / assumption | Source ID | Status | Notes |
|---|---|---|---|---|
| `janus_distance_modulus_proxy` | `m = 5 log10[z + z^2(1-q0)/(1+q0 z + sqrt(1+2q0z))] + cst` | `M18`, Eq. 5 | implemented, verified-source | SN relation from D'Agostini & Petit 2018. Current code fits nuisance offset separately. |
| `janus_q0_from_u0` | `q0 = -1 / (2 sinh(u0)^2)` | `M18`, Eq. 3 / 13 | implemented, verified-source | Used to connect SN parameter `q0` and parametric expansion coordinate `u0`. |
| `JanusExpansion._shape` | `a(u) proportional cosh(u)^2` | `M18`, Eq. 2 / 10; `X2026-expansion-desi` | implemented, verified-source | The absolute alpha normalization cancels in code; only the `cosh^2(u)` shape is used. |
| `JanusExpansion.e` | `H(z)/H0` from parametric `a(u), t(u)` | `M18`, Eq. 10 / 12 / 13 | implemented, verified-source | Derived from `a(u)` and `t(u)`; constant factors cancel in the normalized ratio. |
| `janus_bao_prediction` | Open-geometry marker `r = sinh(2(u0-u_e))` | `M18`, Eq. 15 / 16 / 17 | implemented, verified-source | Used as the current Janus BAO base observable. |
| `janus_bao_prediction` | `a0/r_d = c/(H0 r_d sqrt(1-2q0))` | `M18`, Eq. 14 | implemented, verified-source | Converts open marker distance into `D_M/r_d` under the current BAO interpretation. |
| Active Z2/Sigma source separation | `M18` supplies FLRW/SNe/open-distance formulas but not Sigma throat/collar `h_ab,K_ab` | `M18`; chapter-6.7 source is `X2025-technical-book` / local Janus reference extract | source-separation | Use M18 for expansion observables only. Do not cite it as evidence for PT67 regular surface geometry or Sigma boundary data. |
| `infer_janus_bao_ruler.py` / C7 | Quantity-dependent BAO effective ruler | DESI DR2 data + Janus base model | phenomenological | Strong diagnostic only. Not evidence until derived. |
| `score_bao_c8_source_gauge_no_fit.py` | No-fit source-gauge BAO candidates | `M18`, `X2026-variable-constants` Eq. 40 | needs-derivation | Fixes `q0` and gauge exponents from sources; only global BAO normalization is fitted. Direct source-gauge candidates remain insufficient. |
| `signed_sector.py` | Newtonian sign matrix and weak-field Poisson RHS | `M15`, Eq. 5 and after Eq. 6; `M30`, after Eq. 106 | implemented, source-derived | Signs are verified-source; compact Poisson RHS is derived here using standard Newtonian normalization. Minimal kernel only; not a tensor/geodesic solver. |
| `quantum_sector.py` | Nonrelativistic two-sector Schrodinger and periodic Schrodinger-Poisson scaffold with positive kinetic mass and Janus-signed gravitational potential | `M15`/`M30` sign kernel + standard Schrodinger/Poisson scaffold | prototype, working-derivation | Encodes bimetric sector separation as block-diagonal Hamiltonians and conjugate self-consistent potentials. No Dirac/QFT negative-energy solver and no quantum-sector source verification yet. |
| `check_symbolic_formulas.py` determinant-ratio expansion | `sqrt((-g_-)/(-g_+)) = 1 + epsilon(trace_- - trace_+)/2 + O(epsilon^2)` | `M15`, Eqs. 4a-4b determinant factors | working-derivation | Algebraic first-order bookkeeping only. Needed before deriving optical focusing, but not itself a lensing prediction. |
| `flrw_metric_determinant_ratio_factor` / determinant-weighted lensing source | `B=sqrt(-g_-/-g_+)=(a_-/a_+)^4`; source `rho_+ - B|rho_-|` | M15 determinant factors + FLRW optical ansatz; M20 Eq. 10; M30 Eq. 124 | working-derivation | Isolates `Q_det` without fitting it. M20 gives `a_-/a_+ ~= 1/100`, but M30 uses determinant ratio `~=1` in the Newtonian approximation. Do not insert `(a_-/a_+)^4` until the compatible metric-volume/gauge convention is derived. |
| `positive_photon_lensing_source_grid_with_density_convention` | `negative_proper`: `rho_+ - B rho_-`; `positive_effective`: `rho_+ - rho_-^eff` | M15 determinant roots + M30 Newtonian effective-density convention | implemented, working-derivation | Makes the `Q_det` density convention explicit. Default is `positive_effective`, matching existing diagnostics and avoiding double application of `B`. |
| `positive_effective_negative_density` | `rho_-^eff = Q_det rho_-^proper` | M15 determinant-root source term | implemented, working-derivation | Shows how the effective-density branch absorbs `Q_det`; remaining optical uncertainty is then `Q_cross`. |
| `positive_photon_lensing_source_grid_with_density_convention` with `cross_projection_ratio` | `positive_effective`: `rho_+ - Q_cross rho_-^eff`; `negative_proper`: `rho_+ - B Q_cross rho_-` | M15/M30 positive photon contraction target | implemented, working-derivation | Makes `Q_cross` explicit in code. Default `Q_cross=1` is only the equal-projection limit. |
| `negative_sector_lensing_weight_factor` | `W_-=Q_cross` for `positive_effective`; `W_-=Q_det Q_cross` for `negative_proper` | M15 determinant roots + M15/M30 projection target | implemented, working-derivation | Single code surface for the negative-density weight. Provenance guard rejects raw scale, `det4_metric`, or `weight3_dust` ratios as optical amplitudes. Raw FLRW stacking is a warning path, not a prediction. |
| `check_symbolic_formulas.py` null optical contraction | `G_kk = R_kk` for `g_kk=0`; signed-density source limit under equal optical projection and `B=1` | `M15`, Eqs. 4a-4b + positive photon `g(+)` geodesic anchor | working-derivation | Shows the exact assumptions needed for optical focusing to reduce to `rho_+ - |rho_-|`. The coefficient and determinant correction remain to be derived. |
| `cross_sector_optical_projection_factor` / `equal_comoving_cross_projection_factor` | `Q_cross=A_-/A_+`; equal-projection FLRW limit gives `Q_cross=1` | M15/M30 positive photon contraction target + local symbolic algebra | implemented, working-derivation | Prevents silently assuming that the negative-sector stress projection equals the positive one. |
| `relative_velocity_cross_projection_factor` / `relative_velocity_cross_projection_from_vectors` / `relative_velocity_cross_projection_from_velocities_km_s` | local orthonormal `Q_cross=gamma_-^2(1-beta_parallel)^2`, with `beta_parallel=beta_vec.n_photon` | M15/M30 positive photon contraction target + local SR projection algebra | implemented, working-derivation | Gives a concrete non-fit path for `Q_cross`; still needs a source-derived negative-sector velocity field before survey use. PM dimensionless velocities must be physically calibrated before using the km/s helper. |
| `check_symbolic_formulas.py` raw FLRW lapse cross factor | coordinate-rest covariant projection gives `Q_cross=(a_-/a_+)^2` | FLRW projection algebra only | working-derivation | Algebraic warning path only. Do not combine with M20 scale ratio until the metric-volume and time-gauge conventions are derived. |
| `check_symbolic_formulas.py` raw FLRW negative weight stack | `Q_det Q_cross=(a_-/a_+)^6` | FLRW determinant plus lapse algebra only | working-derivation | Shows why naive stacking of M20 scale ratio is not admissible. |
| `standard_weak_lensing_prefactor` | `(3/2)Omega_abs(H0/c)^2 = 4 pi G rho0/c^2` | standard FLRW weak-lensing normalization | prototype | Exposes the standard coefficient as a replaceable scaffold. Not Janus-derived until `C_J(a,z)` and optical distances are derived. |
| `janus_tensor_lensing_prefactor` | `C_J=C_std Q_source Q_det Q_cross Q_proj Q_dist` | tensor normalization factor map | working-derivation | No fitted scalar correction. Current unity branch matches `C_std`; non-unity factors must be supplied from source-derived derivations. |
| `positive_flrw_photon_energy_factor` / `positive_flrw_ricci_projection_factor` | positive FLRW null geodesic gives `E/E0=1+z` and raw `(u.k)^2` scaling `(1+z)^2` | `M15`/`M30` positive photon `g(+)` geodesic anchor + M18 optical ansatz | accepted-working | Actual positive-geodesic derivation of the raw Ricci projection. |
| `positive_flrw_jacobi_reduced_projection_factor` | `a^-3 * a^-2 * a^4 = a^-1 = 1+z` | `M15`/`M30` positive geodesics + M18 positive FLRW optical ansatz + Jacobi affine-to-comoving reduction | accepted-working | Accepted for the current derivation. Re-open only if a reviewed Janus optical metric changes affine-distance conversion. |
| `standard_dust_lensing_projection_factor` | final standard convergence integrand factor `Q_proj,std=1/a=1+z` | standard dust weak-lensing projection | prototype | Backward-compatible exposed scaffold matching the derived FLRW/Jacobi factor under current assumptions. |
| `janus_open_angular_diameter_distance_mpc` / `janus_open_comoving_lensing_distance_kernel_mpc` | `D_M=R0 sinh(chi)`, `D_A=D_M/(1+z)`, `K=D_M,l D_M,ls/D_M,s` | M18 open marker distance + positive FLRW optical ansatz | accepted-working | Accepted for the current derivation as the M18 positive optical kernel. Re-open only if a reviewed Janus optical geometry supersedes M18. |
| `simulate_two_sector_pairs.py` | pairwise weak-field dynamics from signed-sector accelerations | `M15`, Eq. 6; `M30`, after Eq. 106 | implemented, source-derived | Diagnostic only: same-sector pair approaches, opposite-sector pair separates, and short leapfrog energy drift is small. Not a cosmological simulation. |
| `poisson.py` / `simulate_two_sector_poisson_grid.py` | periodic weak-field Poisson grid for positive/negative absolute densities | `M15`, Eq. 6; `M30`, after Eq. 106 | implemented, source-derived | Diagnostic only: mean-subtracted periodic boundary, conjugate sector potentials and accelerations. Not a tensor solver, Vlasov solver, or cosmological N-body simulation. |
| `solve_periodic_poisson_3d` / `simulate_two_sector_poisson_grid_3d.py` | periodic 3D weak-field Poisson grid for positive/negative densities | `M15`, Eq. 6; `M30`, after Eq. 106 | implemented, source-derived | 3D grid diagnostic only. Precondition for 3D PM, not yet 3D particle evolution or calibrated N-body. |
| `particle_mesh.py` / `simulate_two_sector_particle_mesh.py` | CIC particle-mesh evolution using the two-sector Poisson fields | `M15`, Eq. 6; `M30`, after Eq. 106 | implemented, source-derived | Diagnostic only: periodic box, CIC deposit/interpolation, weak-field leapfrog. Not a relativistic tensor solver or production cosmological N-body code. |
| `particle_mesh_3d.py` / `simulate_two_sector_particle_mesh_3d.py` | CIC 3D particle-mesh evolution using the two-sector Poisson fields | `M15`, Eq. 6; `M30`, after Eq. 106 | implemented, source-derived | 3D diagnostic only: periodic box, CIC deposit/interpolation, weak-field leapfrog. Not yet calibrated cosmological N-body. |
| `particle_mesh_3d_vectorized.py` / `benchmark_vectorized_pm_3d.py` / `benchmark_vectorized_pm_3d_progressive.py` / `run_vectorized_pm_3d_short_stability.py` | vectorized CIC 3D PM backend for large grids | same PM sign kernel as `particle_mesh_3d.py` | implemented, source-derived | Replaces Python object loops with NumPy arrays. Benchmark on this PC: 64^3 two-sector acceleration step about 0.44 s; 175^3 two-sector short 3-step run about 78 s and finite. |
| `diagnose_particle_mesh_resolution.py` | PM sign stability under grid refinement | `particle_mesh.py` diagnostic | implemented | Numerical guard only: checks attraction/repulsion signs at 16/32/64 grids. Not a calibration or observational fit. |
| `simulate_two_sector_segregation.py` | short multi-particle PM segregation diagnostic | `particle_mesh.py` diagnostic | implemented | Numerical mechanism check only: same-sector compaction and cross-sector separation. Not a cosmological simulation or observational evidence. |
| `field_statistics.py` / `analyze_segregation_fields.py` | density contrast, sector correlation and signed 2D/3D power diagnostics | PM density outputs | implemented | Internal simulation diagnostics only. No survey comparison, no fitted cosmological parameter, no independent Janus proof. |
| `diagnose_segregation_robustness.py` | segregation sign robustness across grid/time-step choices | PM diagnostics | implemented | Numerical robustness only: checks that selected internal metrics keep the same sign over 9 deterministic runs. Not a physical calibration. |
| `compare_segregation_controls.py` | Janus vs all-attractive/frozen labelled-blob controls | PM diagnostics | implemented | Numerical control only: isolates the sign effect. The all-attractive case is a baseline, not a Janus source claim. |
| `diagnose_control_robustness.py` | Janus vs all-attractive sign control across grid/time-step choices | PM diagnostics | implemented | Numerical control robustness only: 18 deterministic internal runs. Not observational validation. |
| `cosmological_pm.py` / `simulate_cosmological_pm_prototype.py` | comoving PM wrapper with Janus background expansion | `M18` expansion through `JanusExpansion`; PM sign kernel | prototype | Uses `a=0.5 -> 1` and `E(z)` from the coded Janus expansion. Numerical gravity scale and Hubble drag are prototype parameters, not fitted cosmological claims. |
| `cosmological_pm_3d.py` / `simulate_cosmological_pm_3d_prototype.py` | 3D comoving PM wrapper with Janus background expansion | `M18` expansion through `JanusExpansion`; 3D PM sign kernel | prototype | 3D pair diagnostic with Janus background. Numerical gravity scale and Hubble drag are prototype parameters, not calibrated N-body. |
| `diagnose_cosmological_pm_robustness.py` | comoving PM robustness across grid/time-step choices | `cosmological_pm.py` diagnostic | prototype | Numerical robustness only: 9 internal runs with fixed Janus background. Not calibrated N-body or observational validation. |
| `initial_conditions.py` / `generate_gaussian_initial_conditions.py` / `generate_gaussian_initial_conditions_3d.py` | reproducible Gaussian two-sector IC scaffold in 2D/3D | numerical IC prototype | prototype | Anti-correlated sector fields with controlled seed/RMS/spectral index. Not CMB-normalized and no transfer function yet. |
| `simulate_cosmological_pm_gaussian_ic.py` | comoving PM run from Gaussian two-sector IC | IC prototype + Janus background + PM kernel | prototype | Internal growth diagnostic only. Uses explicit numerical displacement/gravity scales; not calibrated to observations. |
| `simulate_cosmological_pm_3d_gaussian_ic.py` | 3D comoving PM run from Gaussian two-sector IC | IC prototype + Janus background + 3D PM kernel | prototype | Internal 3D growth diagnostic only on a small grid. Uses explicit numerical displacement/gravity scales; not calibrated to observations. |
| `diagnose_gaussian_ic_seed_robustness.py` | Gaussian-IC comoving PM seed robustness | IC prototype + PM diagnostics | prototype | Numerical robustness only across 5 random seeds. Still no CMB normalization or transfer-function calibration. |
| `analyze_cosmological_pm_power_observables.py` | internal positive/negative/signed band-power observables | Gaussian-IC PM outputs | prototype | Exports initial/final radial `P(k)` bands and growth ratios. No physical units, survey window, transfer function or CMB normalization yet. |
| `analyze_cosmological_pm_3d_power_observables.py` | internal 3D positive/negative/signed band-power observables | 3D Gaussian-IC PM outputs | prototype | Exports initial/final radial 3D `P(k)` bands and growth ratios. Small-grid diagnostic only; no physical units, survey window, transfer function or CMB normalization yet. |
| `diagnose_cosmological_pm_3d_power_robustness.py` | 3D signed band-power robustness across seeds and small grids | 3D Gaussian-IC PM outputs | prototype | Numerical robustness only. Current diagnostic passes 6/6 cases for total and low-k signed-power growth; still no physical units or survey calibration. |
| `physical_units.py` / `calibrate_physical_pm_box.py` | Mpc/Msun/H0 scale calibration for PM boxes | standard critical-density normalization | prototype | Adds physical scale bookkeeping only. Current example maps the 8^3 PM prototype to a 1000 Mpc box with 125 Mpc cells; dynamics remain dimensionless. |
| `hubble_time_gyr` / `pm_hubble_velocity_unit_km_s` | PM code time unit `H0^-1`; velocity unit `box_size_mpc / H0^-1 = H0 L` | dimensionless PM equation uses `E(a)=H/H0` | working-calibration | Non-fit physical time calibration for PM diagnostics. |
| `pm_dimensionless_velocities_to_km_s` / `diagnose_qcross_velocity_calibration.py` | `v_unit = box_size_mpc / time_unit_gyr`; `Q_cross` from calibrated km/s velocities | physical PM calibration scaffold + local Q_cross algebra | prototype | Explicit bridge. Default production diagnostics should use the `H0^-1` calibration unless a different physical time unit is stated. |
| `diagnose_pm_state_qcross.py` | vectorized PM negative-sector velocities -> calibrated km/s -> local `Q_cross` stats | PM state scaffold + local Q_cross algebra | diagnostic | No fit and no survey prediction. Valid after explicit `box_size_mpc` and `time_unit_gyr`; default pipeline uses `H0^-1`. |
| `diagnose_pm_qcross_lensing_source.py` | CIC source grid `rho_+ - Q_cross rho_-` from PM state velocities | PM state scaffold + local Q_cross algebra | diagnostic | First grid-level bridge from velocity-derived `Q_cross` to positive-photon source. Still not tensor-complete or survey-calibrated. |
| `run_pm_qcross_lensing_pipeline.py` | short vectorized PM evolution with per-step velocity-derived `Q_cross` source metrics | PM vectorized backend + local Q_cross algebra | diagnostic | Fast end-to-end diagnostic chain using `H0^-1` by default. Does not close survey likelihood or prove global tensor factors. |
| `run_pm_qcross_absolute_shear.py` | bounded anti-correlated Gaussian displacement IC -> evolved PM `rho_+ - Q_cross rho_-` -> Janus absolute coefficients -> kappa/shear diagnostic | PM `Q_cross` source + `janus_absolute_lensing_coefficients` | diagnostic | Removes the old demo velocity pattern from the absolute observable chain. Still no source-derived transfer function, survey covariance or likelihood. |
| `run_pm_qcross_absolute_shear_resolution.py` | multi-grid convergence check for absolute PM `Q_cross` shear | absolute shear diagnostic + physical grid requirement | diagnostic | Replaces single-grid-only reporting with explicit convergence metrics and flags whether the sigma8 radius grid requirement is met. Uses fixed-total particle mass for controlled grid convergence unless `fixed-particle` is explicitly selected. |
| `build_pm_band_limited_shear_convergence.py` | fixed-physical-k band convergence audit for PM `Q_cross` absolute shear | `run_pm_qcross_absolute_shear_resolution.py` spectra | diagnostic | Avoids treating total shear RMS as convergence. Reports which common Fourier bands are stable without fitting a correction. |
| `build_pm_convergence_family_comparison.py` | compares bounded-Gaussian and analytic-multimode PM shear convergence reports | PM band-limited convergence reports | diagnostic | Marks controlled numerical convergence only for analytic-multimode with fixed total mass. Does not close Janus IC physics or tensor/survey blockers. |
| `analytic_multimode_field_3d` in `run_pm_qcross_absolute_shear.py` | same continuous IC sampled on each grid for convergence diagnostics | numerical convergence control | diagnostic | Removes random-realization mismatch from grid convergence tests. Current stable analytic scan reaches 128^3 with subluminal velocities; not a physical Janus transfer function. |
| `diagnose_pm_relativistic_velocity_stability.py` | grid/amplitude scan enforcing `v<c` before `Q_cross` | PM velocity calibration + local Q_cross algebra | diagnostic | Records invalid runs instead of silently clamping velocities. Displacement scale is a prototype stability setting, not an observational fit. |
| `build_pm_time_lensing_normalization_calibration.py` | working calibration: PM time `H0^-1`, velocity unit `H0 L`, and factorized lensing `C_J` | PM equation scale + tensor normalization map + M18 open coefficients | working-calibration | Closes the current non-fit calibration layer. Still not a survey likelihood or proof of the global tensor branch. |
| `analyze_cosmological_pm_3d_physical_power.py` | physical-scale 3D band powers with `k` in `1/Mpc` and mean `P(k)` in `Mpc^3` | 3D Gaussian-IC PM outputs + physical scale calibration | prototype | Unit conversion of existing dimensionless outputs only. Not yet physical N-body, not CMB-normalized, not survey-calibrated. |
| `diagnose_sigma8_resolution_requirements.py` | resolution requirement before `sigma8` normalization | physical scale calibration | prototype | Shows current 8^3 / 1000 Mpc box cannot resolve `8 h^-1 Mpc`; at least 175^3 cells per sector are required for 2 cells per sigma8 radius. |
| `generate_sigma8_normalized_ic_3d.py` | 175^3 Gaussian contrast field normalized on `8 h^-1 Mpc` | Gaussian IC prototype + physical scale calibration | prototype | Achieves target `sigma8=0.8`, but direct Gaussian density use is unsafe for the tested seed: about 41.7% of cells have `delta < -1`; density-safe sigma8 is only about 0.0318 without a better transfer/lognormal prescription. |
| `generate_lognormal_sigma8_ic_3d.py` | positive-density 175^3 lognormal two-sector IC normalized near `sigma8=0.8` | lognormal IC prototype + physical scale calibration | prototype | Density-safe and resolved; positive sigma8 `0.800051`, negative sigma8 `0.803561`. Sector correlation is weak (`-0.04`) and overdensity maxima are very large, so this is a technical positive-density scaffold, not a final Janus transfer function. |
| `diagnose_bounded_anticorrelated_sigma8_ic_3d.py` | density-safe exact anti-correlated bounded IC capacity | bounded IC prototype + physical scale calibration | prototype | Preserves `delta_-=-delta_+` and `delta>-1`, but max attainable sigma8 in tested tanh family is only `0.163`, below target `0.8`. This exposes the IC design constraint. |
| `lensing.py` / `diagnose_lensing_source_map.py` | positive-sector weak-field lensing source diagnostic | M15/M30 positive metric source signs + M07/M20 lensing concept anchors | prototype | Implements `delta_lens_plus = ((rho_plus-rho_minus_abs)-mean(rho_plus-rho_minus_abs))/mean(rho_plus+rho_minus_abs)`. Confirms negative-mass concentration gives negative/diverging source and negative-mass holes give positive lensing source. Not a shear/convergence prediction or tensor ray tracer. |
| `weak_field_weyl_screen_tidal_components_2d` | screen Hessian split: `kappa=1/2(Phi_xx+Phi_yy)`, `gamma1=1/2(Phi_xx-Phi_yy)`, `gamma2=Phi_xy` | standard weak-field optical/tidal split + current metric-potential closure gate | diagnostic | Executable Weyl/shear operator for a declared weak-field metric potential. Does not derive that potential from Janus `delta G_plus[h_plus]` and is not a prediction by itself. |
| `positive_photon_weak_field_weyl_components_2d` | weak-field source-to-Weyl diagnostic: `rho_eff_plus -> Phi_lens_plus -> kappa,gamma1,gamma2` | M15/M30 weak-field signed source + Poisson diagnostic + Weyl operator | diagnostic | Rejects fit provenance such as `shear_fit` and `sigma8_fit`. Keeps `prediction_ready=false` until the metric potential is derived from Janus field equations. |
| `diagnose_restricted_metric_weyl_chain.py` | restricted comoving-scalar Weyl diagnostic with `restricted_metric_ready=true`, `prediction_ready=false` | comoving scalar zero-`Pi` closure candidate + weak-field Weyl source chain | diagnostic | Runs two controlled maps, negative cluster and negative hole, with Weyl trace-free statistics. This is the first metric-ready restricted branch, not a survey or tensor-lensing prediction. |
| `diagnose_lensing_sigma8_observable.py` | `sigma8` measured on the positive-sector weak-lensing source | `lensing.py` + physical scale calibration + current IC families | prototype | Computes `sigma8_lens_plus` for lognormal and bounded anti-correlated IC diagnostics. No fit, no survey likelihood, no claim of final `S8_eff`. |
| `diagnose_weak_lensing_projection.py` | uniform 2D projection of `delta_lens_plus` into `kappa_plus_proxy` | `lensing.py` + 2D projected power diagnostics | prototype | Computes a normalized line-of-sight mean and projected 2D power proxy. Uses uniform `W=1`; no Janus tomographic kernel, no shear estimator, no survey likelihood. |
| `janus_open_lensing_geometry_kernel` / `diagnose_janus_tomographic_lensing_kernel.py` | Janus open-distance geometric lensing kernel | M18 open marker distance `r=sinh(2(u0-u_e))` + `delta_lens_plus` | prototype | Uses `K=r_l*r_ls/r_s` for a single source redshift and projects `delta_lens_plus`. No source-redshift distribution, growth model, shear estimator or survey likelihood. |
| `shear_from_convergence_proxy_2d` / `diagnose_janus_shear_proxy.py` | E-mode shear proxy from Janus convergence proxy | standard weak-lensing Fourier relation + Janus `kappa_janus_kernel_proxy` | prototype | Computes `gamma1/gamma2` from projected convergence. No shape noise, mask, redshift distribution, absolute convergence normalization or likelihood. |
| `janus_source_distribution_lensing_weights` / `diagnose_janus_source_distribution_lensing.py` | Janus lensing projection integrated over explicit source-redshift distribution | M18 open marker distance + user-stated `n(z_s)` + shear proxy | prototype | Computes `K_dist=sum n(z_s)K(z_l,z_s)` and shear proxy. Default distribution is a diagnostic input, not survey-derived and not fitted. |
| `janus_absolute_lensing_coefficients` / `diagnose_janus_absolute_convergence.py` | absolute convergence normalization scaffold | standard weak-lensing prefactor + M18 open-distance geometry + Janus `delta_lens_plus` | prototype | Computes `(3/2)Omega_abs(H0/c)^2 Delta_chi(1+z)D_lD_ls/D_s` coefficients. This is a scaffold pending tensor-level Janus normalization, not a final `S8_eff`. |
| `negative_mass_sphere_reduced_deflection_profile` / `negative_mass_sphere_annular_dimming_map` / `diagnose_dipole_repeller_negative_lens.py` | normalized dipole-repeller negative-lensing profile/map: zero center, maximum at object radius, exterior `1/b` decay | `X2025-technical-book`, Sect. XI | diagnostic | Shape-only observable target for annular dimming. No absolute mass/radius, no survey normalization, no `S8_eff` claim. |
| `build_lensing_normalization_audit.py` | audit of Janus weak-lensing normalization dependencies | M15/M30/M18/M07/M20 plus current lensing prototypes | working-derivation | Separates source-backed pieces from standard weak-lensing scaffolds and lists blockers before `S8_eff` can be claimed. |
| `build_lensing_normalization_audit.py` prefactor decomposition | `C_J(a,z)=C_std*Q_source*Q_det*Q_cross*Q_proj*Q_dist` | current tensor derivation target | working-derivation | Forbids fitting a scalar correction. Each factor must be source-derived before replacing the standard-prefactor scaffold. |
| `build_lensing_qdet_convention_audit.py` | explicit convention audit for `Q_det` | M15 determinant roots; M20 Eq. 10; M30 Eq. 124 | working-derivation | Allows only `B=1` as the current Newtonian effective-density convention. Blocks naive insertion of M20 `(a_-/a_+)^4` until optical volume/density mapping is derived. |
| `build_qdet_metric_volume_target.py` | `Q_det` branch target: `positive_effective`, `negative_proper`, forbidden raw FLRW insertion | M15 determinant roots + current Q_det audit | working-derivation | Marks `positive_effective` as diagnostic convention and `negative_proper` as derivation target; does not close tensor lensing. |
| `build_qdet_density_measure_target.py` | density-measure target for `Q_det`: `rho_minus_eff=B_plus rho_minus_proper`, no double counting with `Q_cross` | M15 determinant-coupled field equations; M30 Newtonian effective-density limit | working-derivation | Makes `Q_det` a density/volume factor only. Forbids multiplying a positive-effective density by `B_plus` again or using raw `(a_minus/a_plus)^4` as an optical amplitude. |
| `build_coupled_field_equations_audit.py` | two metrics, coupled source signs, determinant-ratio layer, Bianchi closure blockers | M15/M30 plus didactic coupled-field web page | working-audit | Treats the 2023 web article as orientation only. Confirms the next tensor target is determinant-density mapping plus Bianchi-compatible mixed stress tensors. |
| `build_lensing_qcross_audit.py` | explicit convention audit for `Q_cross` | M15/M30 positive photon contraction target + FLRW projection algebra + tetrad-map target | working-derivation | Allows `Q_cross=1` only as current equal-projection convention. Defines the `L_minus_to_plus` tetrad/covector map as target and blocks fitted or naive scale-ratio projection factors. |
| `build_qcross_four_velocity_target.py` | `Q_cross` target: equal projection, local velocity bridge, missing global four-velocity closure, PM usage conditions | M15/M30 positive photon contraction target + local velocity algebra | working-derivation | Keeps `Q_cross` explicit until covariant negative-sector stress projection along positive null rays is derived. |
| `build_qcross_covariant_projection_target.py` | covariant target `Q_cross=A_minus/A_plus` with `A_s=(u_s.k_plus)^2` after a declared cross-sector map | M15/M30 optical stress contraction target | working-derivation | Reduces the local velocity bridge to an invariant contraction problem. The cross-sector map `M_minus_to_plus` is still missing, so tensor lensing remains open. |
| `build_qcross_tetrad_map_target.py` | tetrad-map target `u_minus_to_plus^A=L_minus_to_plus^A_B u_minus^B`, `Q_cross=A_minus/A_plus` | Q_cross covariant projection target plus local orthonormal velocity reduction | working-derivation | Names the local Lorentz map required before using velocity-derived `Q_cross` as physics. A nontrivial `L_minus_to_plus` must induce the `M_minus_to_plus/K_plus` transport used by Bianchi closure. |
| `build_qcross_flrw_comoving_tetrad_branch.py` | aligned FLRW comoving tetrads give `L_minus_to_plus=I`, `A_minus=A_plus=E^2`, hence `Q_cross=1` | Q_cross tetrad-map target plus FLRW orthonormal tetrad algebra | source-derived branch | Closes the homogeneous comoving tetrad branch only. Coordinate covector lapse/scale powers remain warning paths, not optical amplitudes. Perturbed/global `L_minus_to_plus` is still open. |
| `build_qcross_geometric_tetrad_map_derivation.py` | raw solder map `L_geom_minus_to_plus^A_B=e_plus^A_mu E_minus_B^mu` and Lorentz-compatibility residual | tetrad algebra for local sector identification | working-derivation | Derives the geometric `GL(4)` map, but forbids identifying it with admissible optical `L_minus_to_plus` unless `L_geom^T eta L_geom=eta` is proved. |
| `build_qcross_noncomoving_boost_branch.py` | local Lorentz boost branch `Q_cross=gamma^2(1-beta_vec.n)^2`, with order-2 expansion | Q_cross tetrad-map target plus local Lorentz algebra | source-derived branch | Closes the local non-comoving boost algebra. It still requires a source-derived `beta_vec` and Bianchi-compatible stress transport before survey use. |
| `build_lensing_qdet_qcross_derivation_map.py` | branch map for `effective_newtonian`, `effective_with_projection`, `proper_density_full`, and forbidden raw scale insert | Q_det/Q_cross audits plus tetrad-map target | working-derivation | Makes the derivation choices explicit before changing code defaults or reporting observables; projection branches now require `u_minus_to_plus` through `L_minus_to_plus`. |
| `build_lensing_scale_ratio_warning.py` | numeric warning against direct use of M20 `a_-/a_+ ~= 1/100` as a lensing amplitude | M20 Eq. 10 + Q_det/Q_cross audit algebra | working-derivation | Shows raw `Q_det=1e-8` and stacked `W_-=1e-12`; these are warning values, not predictions. |
| `build_lensing_prefactor_audit.py` | separates `C_std`, `rho_abs0`, `rho_source`, and `Omega_eff` | standard weak-lensing normalization + Janus source decomposition | working-derivation | Blocks treating `Omega_abs` or an inferred `Omega_eff` as evidence before tensor normalization and survey likelihood are fixed. |
| `build_lensing_readiness_report.py` | aggregate readiness gates for `Q_det`, `Q_cross`, absolute prefactor and `S8_eff` | current audit reports | working-derivation | Machine-readable red-light report before any final Janus weak-lensing `S8_eff` claim. |
| `build_p0_stueckelberg_metric_potential_closure_contract.py` | four-part contract for promoting Poisson diagnostics to metric potential: linearized field equation, gauge, slip, source identity | M15/M30 coupled sources + standard weak-field perturbation bookkeeping | working-derivation | Defines the proof obligations before using `Phi_lens_plus` as a Janus metric potential. All conditions remain open. |
| `build_p0_stueckelberg_linearized_field_equation_branch.py` | symbolic normalization branch: `delta G00_plus=2 Delta Psi_plus` gives `Delta Psi_plus=4 pi G rho_eff_plus` when `chi=8 pi G` | M15/M30 weak-field signed source + symbolic GR normalization check | working-derivation | Checks normalization only. Does not derive Janus gauge, slip, or the full `delta S00_plus` source identity. |
| `build_p0_stueckelberg_gauge_slip_branch.py` | scalar weak-field branch: `Phi_lens=(Phi+Psi)/2`, with `Phi=Psi` only when anisotropic stress vanishes | standard scalar perturbation bookkeeping + Janus pressure/Pi blockers | working-derivation | Controls the zero-`Pi` diagnostic case and blocks use when transported `Pi_minus_to_plus` or cross-sector stress is unknown. |
| `build_p0_stueckelberg_source_identity_branch.py` | comoving scalar source identity: comoving perfect-fluid `T00` reduces to density when `Pi00=0` | standard stress tensor decomposition + M15/M30 signed effective-density branch | working-derivation | Admits `delta S00_plus -> rho_plus-rho_minus_eff` only for the comoving scalar branch with declared `Q_det/Q_cross`. Non-comoving velocities and general pressure/Pi remain open. |
| `build_p0_stueckelberg_metric_potential_promotion_gate.py` | aggregate gate for promoting weak-field Poisson potential to Janus metric potential | linearized/gauge-slip/source-identity branches | working-audit | Reads branch decisions and keeps promotion blocked until Janus field equation, slip, and source identity are derived. Prevents confusing a diagnostic Poisson potential with a closed metric perturbation. |
| `build_prediction_claim_gate.py` | central claim-level gate: diagnostic vs prediction-ready | lensing readiness, scaffold roadmap, observable-chain audit, survey interface | working-audit | Prevents any diagnostic numerical output from being labelled a prediction while Bianchi, `Q_det`, `Q_cross`, IC, convergence or survey blockers remain open. |
| `build_bianchi_closure_target.py` | `D_plus.S_plus=0`, `D_minus.S_minus=0`; weak-field branches accepted only as diagnostics | M15 Eqs. 4a-4b; M30 Sect. 12-14 | working-derivation | Keeps the exact mixed-stress-tensor closure separate from PM/lensing diagnostics. Blocks survey-level tensor lensing until both divergences are derived. |
| `build_interaction_tensor_attempt_audit.py` | 2025 FLRW/stationary interaction-tensor attempts, determinant reinterpretation, dipole-repeller induced geometry | `X2025-technical-book`, Sect. VIII-XII | roadmap-source | Useful target source, but not treated as peer-reviewed proof. Confirms exact mixed `K` tensor is still not closed. |
| `build_source_freshness_audit.py` | latest-source check against `jp-petit.org/papers/cosmo`; adds `X2026-questionable-black-holes` and `X2026-complex-reality` | JPP papers index, checked 2026-06-21 | working-audit | Confirms these new sources are compact-object/symmetry roadmap inputs and do not close the Bianchi/Q_det/Q_cross lensing blockers. |
| `build_temporary_scaffolds_audit.py` | explicit list of temporary scaffolds and required replacements | current PM/lensing diagnostic stack | working-audit | Prevents diagnostic layers from being mistaken for proof. Marks `H0^-1` time calibration and factorized `C_J` as keepable working layers. |
| `build_remaining_scaffolds_roadmap.py` | coordination roadmap for Bianchi, Q_det, Q_cross, IC, survey and shear-screen tracks | current scaffold/readiness audits | working-audit | Makes parallel work explicit while preserving the no-fit rule and final-claim blockers. |
| `build_observable_chain_consistency_audit.py` | consistency check between absolute PM-Qcross observable output and resolution-convergence report | current PM absolute-shear reports | working-audit | Flags when the absolute run reaches 175^3 but the convergence report does not cover that grid. |
| `build_bianchi_mixed_stress_residual_target.py` | explicit residuals `R_plus^mu`, `R_minus^mu` for mixed-stress closure | M15 Eqs. 4a-4b; M30 Sect. 12-14 and Eqs. 105a-105b | working-derivation | Reduces the Bianchi scaffold to equations that must vanish. Does not supply `K_plus/K_minus`; tensor lensing remains blocked. |
| `build_bianchi_ansatz_audit.py` | audit of candidate `K_plus/K_minus` ansatz branches and failure modes | M15/M30 Bianchi closure targets plus local `Q_det/Q_cross` reports | working-audit | Rejects naive copied-stress closure for generic tensor lensing and identifies the mixed-transport construction as the required target. |
| `build_bianchi_mixed_transport_map_target.py` | explicit target for sector-to-sector tensor transport maps `M_minus_to_plus` and `M_plus_to_minus` | M15/M30 coupled metrics plus Bianchi mixed-stress residual target | working-derivation | Names the missing transport-map object needed before setting both residuals to zero. Forbids naive copied stress, raw scale-ratio amplitudes, and `Q_det/Q_cross` merging. |
| `build_bianchi_flrw_dust_transport_branch.py` | special FLRW dust scalar-transport branch: `weight3_dust_plus=det4_metric_plus transport3_dust_plus proportional (a_minus/a_plus)^3` and symmetric negative branch | Bianchi residual target plus FLRW dust continuity | source-derived branch | Closes only the homogeneous dust scalar case. If `det4_metric_plus=(a_minus/a_plus)^4`, then `transport3_dust_plus proportional (a_minus/a_plus)^-1`; do not double-count `Q_det`. It is not a generic tensor map or a lensing amplitude. |
| `build_bianchi_flrw_lapse_volume_audit.py` | FLRW determinant audit: `det4_metric_plus=(N_minus a_minus^3)/(N_plus a_plus^3)` | FLRW metric determinant algebra plus Bianchi dust branch | working-audit | Separates lapse, spatial volume, and dust transport. The quartic scale ratio requires a lapse-ratio convention and is not a lensing amplitude. |
| `build_bianchi_flrw_perfect_fluid_transport_branch.py` | special FLRW perfect-fluid scalar branch with explicit `det4_metric_*`, `transport_pf_*`, and declared `w_cross_plus/w_cross_minus` | Bianchi residual target plus FLRW perfect-fluid continuity | working-derivation | Generalizes the dust branch to pressure terms. It is a branch condition, not a closure, because effective cross equations of state and anisotropic stress transport remain undeclared. |
| `build_bianchi_anisotropic_stress_transport_target.py` | tensor target for transporting `Pi_s^{mu nu}` without scalar reduction | Bianchi residual target plus perfect-fluid/stress split | working-derivation | Separates anisotropic stress from dust/perfect-fluid scalar branches. It forbids replacing `Pi_s^{mu nu}` by a density factor or hiding it inside `Q_cross`. |
| `build_janus_ic_source_targets.py` | IC target split: keep PM `H0^-1` calibration, block missing transfer/growth/amplitude/velocity derivations | PM calibration and current IC diagnostics | working-audit | Forbids replacing Janus IC physics with Gaussian/lognormal/bounded field tuning or sigma8 rescaling. |
| `build_janus_linear_ic_equations_target.py` | weak-field linear two-sector target for `T_J`, `D_J`, velocity and amplitude | M15/M30 Newtonian sign kernel; M18 expansion; PM H0^-1 calibration | working-derivation | Makes IC replacement actionable through continuity/Euler/Poisson target equations. Does not derive the final transfer function or amplitude normalization. |
| `build_janus_linear_growth_modes.py` | weak-field eigenmode target: neutral `delta_sum` and signed-source `delta_diff` modes | linear IC equations target plus M15/M30 signed source | working-derivation | Reduces the two-sector linear system into actionable growth modes while keeping `A_J`, `T_J(k)`, and Q_det branch choices open. |
| `build_janus_linear_growth_propagator.py` | no-fit RK4 diagnostic propagator for declared weak-field growth-mode eigenvalues under Janus `E_J(a)` | linear growth modes target; M18 expansion API | diagnostic | Integrates null/source modes for declared `Omega_plus/Omega_minus` inputs. Does not derive `T_J(k)`, `A_J`, or production ICs. |
| `build_janus_linear_ic_background_operator_target.py` | source-provenance gate for `Omega_plus(a)`, `Omega_minus_eff(a)`, and `M(a)` before production ICs | M18 expansion; M15/M30 signed source; Q_det density-measure target | working-derivation | Keeps constant-Omega propagation diagnostic until sector background functions are source-derived. Blocks `A_J` and transfer substitutions. |
| `build_survey_data_contract.py` | machine-readable no-fit survey data contract validator | survey likelihood interface and no-fit comparison rule | implemented-interface | Validates required survey fields, covariance shape/positive-definiteness, mask/window declaration, and `n_fit_parameters=0`. Structural readiness only; not evidence. |
| `fixed_prediction_chi_square` / `build_survey_likelihood_interface_report.py` | fixed-prediction Gaussian likelihood interface with full covariance validation | no-fit survey comparison rule | implemented-interface | Interface only. Refuses malformed covariance; no survey evidence until real observed vector and covariance are supplied. |
| `formal/axioms/lensing_tensor_derivation_target.md` | tensor/optical derivation gates for Janus weak lensing | M15/M30 coupled metrics + current lensing audit | working-derivation | Defines the exact missing derivation before the standard convergence prefactor can be replaced by a Janus-normalized `S8_eff`. |
| `formal/axioms/sigma8_observable_map.md` / `build_sigma8_observable_map_report.py` | Janus `sigma8/S8` observable map and no-rustine rule | M15/M22 verified anchors + M07/M20 verified-concept anchors + current PM diagnostics | working-derivation | Separates naive positive-sector, signed-source, two-field tuple, visible-tracer and lensing-effective candidates. Existing sources give ingredients; the weak-lensing / galaxy-clustering observable map is still the derivation target. Explicitly forbids treating IC transforms as evidence. |

## Working Hypotheses

| Hypothesis | Source / motivation | Status | Next requirement |
|---|---|---|---|
| DESI BAO mismatch may indicate a non-standard Janus BAO ruler rather than immediate falsification. | `X2026-variable-constants`, DESI residual inversion | needs-derivation | Derive `D_M/r_d`, `D_H/r_d`, `D_V/r_d` in Janus without Lambda-CDM ruler assumptions. |
| Effective BAO correction has an exponent close to `sqrt(a) = (1+z)^-1/2`. | `infer_janus_bao_ruler.py`; `X2026-variable-constants`, Eq. 40 | phenomenological | Eq. 40 gives `c_hat proportional 1/sqrt(a)`; need a derivation connecting this to BAO observables. |
| `q0 ~= -0.087` remains competitive when allowing a simple anisotropic BAO correction. | `M18` SN value and C7 diagnostic | phenomenological | Derive the anisotropy before making any physical claim; then cross-validate on independent BAO data. |

## Core Geodesic And Signed-Mass Mechanism

These are central Janus formulas and claims. They were absent from the first traceability pass because that pass focused on expansion/SNe/BAO only.

| Surface | Formula / assumption | Source ID | Status | Notes |
|---|---|---|---|---|
| Single-metric failure mode | `G = chi [T(+) + T(-)]` gives one geodesic family for both signs | `M15`, Eqs. 1-3; `M30`, Eqs. 75-79 | verified-source | Produces Bondi runaway; this is the failure Janus avoids. |
| Bondi force law | acceleration depends on active gravitational mass sign in one-metric GR | `M15`, Eqs. 2-3 | verified-source | Positive masses attract everything; negative masses repel everything. |
| Two geodesic families | positive masses/geons follow `g(+)`; negative masses/geons follow `g(-)` | `M15`, text after Eq. 6; `M30`, Sect. 9 | verified-source, partially-implemented | `signed_sector.metric_sheet_for` tracks sector-to-metric assignment; no geodesic integrator yet. |
| Coupled field equations | `G(+) = chi [T(+) + sqrt(-g(-)/-g(+)) T(-)]`; `G(-) = -chi [sqrt(-g(+)/-g(-)) T(+) + T(-)]` | `M15`, Eqs. 4a-4b | verified-source, not-implemented | Tensor-level model, not currently represented in code. |
| Matter tensor signs | `rho(+)>0, p(+)>0`; `rho(-)<0, p(-)<0` | `M15`, Eq. 5 | verified-source | Needed for Newtonian-limit signs. |
| Double Newtonian approximation | expand `g(+)` and `g(-)` around Lorentz metrics | `M15`, Eq. 6 | verified-source | Leads to the Janus interaction laws. |
| Janus interaction laws | same signs attract; opposite signs repel | `M15`, Eq. 5 and after Eq. 6; `M30`, after Eqs. 105-106 | verified-source, implemented | Implemented through density/equation sign product and Poisson RHS in `signed_sector.py`, with tests for the four sector pairings and anti-runaway behavior. |
| 2024/2025 mixed stationary form | `G = chi[T + b^2 Tbar]`; `Gbar = -chi[T + bbar^2 Tbar]` | `M30`, Eqs. 105a-105b | verified-source | Later formulation to reconcile with Bianchi identities and weak-field behavior. |
| Local GR recovery | where one mass sector is absent, first equation reduces to Einstein 1915 locally | `M30`, after Eq. 106 | documented | Explains compatibility with Mercury/light-deflection/local GR tests in the Janus claim. |
| Large-scale negative sector clustering | `|rho(-)| > rho(+) => t_J(-) << t_J(+)` | `M22`, Eq. 1 | verified-source, not-implemented | Basis for voids/filaments and early structure narrative. |
| Galactic kinetic model | Vlasov + Poisson construction for galaxy dynamics | `X2025-kinetic-galactic`, Eq. 11 and later sections | verified-source, not-implemented | Candidate for a later rules/solver module. |
| Symmetry basis | Janus symplectic group acts on torsors; energy/momentum/charge transformations classified by group action | `M31` / `X2025-symplectic-hal` | verified-source, needs-extraction | Needs a dedicated math summary. |

## Source Cards For Current Expansion Work

### M18 - Supernovae Type Ia Constraints

Use level: peer-reviewed source for current SN and open-distance formulas.

Important equations:

- Eq. 5: bolometric magnitude-redshift relation with one shape parameter `q0`.
- Eq. 6: reported best fit `q0 = -0.087 +/- 0.015` on 740 SNe.
- Eq. 10: parametric solution `a(u)` and `t(u)`.
- Eq. 13: `q = -1 / (2 sinh(u)^2)`.
- Eq. 14: `1 - 2q = c^2 / (a^2 H^2)`.
- Eq. 17: open marker distance `r = sinh(2u0 - 2ue)`.
- Eq. 20 / 21: mapping from `q0, z` to `u0, ue`.

Current implementation status: used directly in `models.py` and `bao.py`.

### X2026-variable-constants - Alternative To Inflation

Use level: author document / preprint-like source. Useful for hypothesis generation, not yet independent evidence.

Important equations:

- Eq. 28 / 30: metric gauge condition and `t_hat proportional a^(3/2)`.
- Eq. 31 / 33: horizon scaling argument.
- Eq. 40: gauge relationships, including `c_hat proportional 1/sqrt(a)`, `h_hat proportional a^(3/2)`, `G_hat proportional 1/a`, `e_hat proportional sqrt(a)`, `m_hat proportional a`, `mu0_hat proportional a`.
- Text after Eq. 40: characteristic lengths vary as `a`; characteristic times vary as `a^(3/2)`.

Current implementation status: not implemented as physical law. Used to motivate the BAO `sqrt(a)` hypothesis only.

### X2026-expansion-desi - Expansion And DESI

Use level: author document / preprint-like source. Useful for current target problem.

Important content:

- Claims the Janus exact expansion solution is qualitatively compatible with DESI's preference for stronger past acceleration.
- Restates the coupled-field-equation context and negative-energy dominance.
- Gives the FLRW metric setup and energy-conservation compatibility condition around Eqs. 25-30.

Current implementation status: used as roadmap only. The actual coded parametric formulas currently trace more cleanly to M18.

### M15 - Coupled Field Equations

Use level: peer-reviewed source for the bimetric coupled-field-equation formulation used in the older Janus model.

Important equations:

- Eq. 1: standard Einstein equation.
- Eqs. 2-3: Bondi/Newtonian one-metric acceleration and runaway setup.
- Eqs. 4a-4b: two coupled field equations.
- Eq. 5: signs of `rho` and `p` in both sectors.
- Eq. 6: double Newtonian approximation around Lorentz metrics.
- After Eq. 6: interaction laws: same signs attract, opposite signs repel.

Current implementation status: not implemented. This is the main source for a future signed-gravity/geodesic module.

### M30 / X2025-bimetric-hal - Bimetric Sakharov Model

Use level: peer-reviewed 2024 EPJC article plus local HAL mirror.

Important content:

- Sections 7-9: one-metric negative-mass failure and bimetric replacement.
- Eqs. 75-79: single-field equation and positive/negative Schwarzschild-like metrics used to show the runaway problem.
- Section 9: two metrics and two geodesic families.
- Eqs. 105a-105b: mixed-notation coupled equations in stationary conditions.
- Eq. 106 and following text: Newtonian approximation and interaction laws.

Current implementation status: documented only. This should be the main modern source for geodesics and signed-sector behavior.

### M31 / X2025-symplectic-hal - Janus Symplectic Group

Use level: peer-reviewed mathematical source for symmetry classification.

Important content:

- Action on torsors of the Janus symplectic group.
- Charge symmetry and matter-antimatter duality.
- Energy/momentum/charge interpretation through group action.

Current implementation status: indexed only. Needs a dedicated extraction pass before using it as a formal dependency in code.

## Immediate Gaps

1. Exact equation numbers are still missing for some non-implemented hypotheses.
2. The 2026 expansion PDF is a document-author source, not the same evidential level as the peer-reviewed 2024/2025 papers.
3. The BAO ruler correction has too much freedom unless derived from constants-variable physics.
4. Pantheon+ is still diagonal-only in the quick score.
5. The CMB paper `M20` has not yet been reconciled with Planck/ACT constraints.
6. The signed-mass Newtonian-limit sign/Poisson-2D/Poisson-3D/pairwise/grid/particle-mesh-2D/particle-mesh-3D/comoving-PM-2D/comoving-PM-3D/Gaussian-IC-2D/Gaussian-IC-3D kernel and minimal physical scale bookkeeping are implemented; full geodesic/tensor dynamics and physically unitful N-body evolution are not.
7. `sigma8` normalization is blocked on current small grids, but the vectorized PM backend now runs the minimum 175^3 two-sector grid on this PC for a short finite multi-step test.
8. Naive Gaussian `sigma8=0.8` ICs at 175^3 are not directly physical density ICs because many cells fall below `delta=-1`; a transfer-function/lognormal/positive-density prescription is needed before production runs.
9. The lognormal positive-density scaffold fixes `delta > -1` but weakens sector anti-correlation and produces large tails; a Janus-derived IC prescription is still needed.
10. Exact anti-correlation plus positive density plus `sigma8=0.8` cannot all be met by the tested bounded `tanh` scaffold; target capacity tops out near `sigma8=0.163`.
