# Janus Bi-Sector Boltzmann Backend Note

## Scope

This note is an architecture target, not a physics result. It records why the
current mono-metric CAMB/EFT path should remain diagnostic until a derived
Janus-orbifold Z4-projected perturbation system exists.

## Current CAMB/EFT Diagnostic

CAMB assumes one metric sector with standard photon-baryon visibility,
recombination and source projection machinery. Local hooks can test effective
source functions, modified background histories, or EFT-like parameter
deformations. Those tests are useful for falsifying narrow approximations, but
they do not validate or exclude the full Janus-orbifold model unless the
bi-sector equations reduce rigorously to those effective hooks.

Treat existing CAMB CMB failures as `CAMB-EFT diagnostic` results:

- they constrain the mono-metric approximation used in the hook;
- they do not close the unified Janus/Z4 field-equation problem;
- they must not be reported as final Planck exclusion of Janus.

## Future Bi-Sector Backend

A prediction-ready backend must start from the unified Janus/Z4 geometric
equation, project its positive/visible and negative/mirror sector variables,
then project observables seen by positive-energy photons. It may later target
CAMB, CLASS/hi_class, or a dedicated prototype, but the first deliverable is
the equation set and consistency checks.

Minimal backend boundary:

- background expansion and sector densities are inputs derived from Janus
  sources, not tuned CMB fit functions;
- scalar perturbations carry explicit sector labels as Z4 projections, not as
  independently postulated metrics;
- cross-sector stress, metric and photon projections are named variables
  derived from the unified source, not hidden constants or fictive forces;
- the GR/LambdaCDM limit is recovered when Janus couplings are set to zero or
  when the mirror sector decouples by construction.

## TODO Checklist

- [x] Add the formal linearized unified Z4 equation interface and prove the
  conditional transport lemma: if the master equation and normalized projection
  are supplied, sector couplings descend from projection, never from postulated
  interaction forces.
- [ ] Derive the explicit tensor operator of the unified Z4 equation from the
  Janus action. The current Lean module is an interface/transport proof, not
  the full action-level derivation.
- [ ] Define the determinant/cross-sector source factors, including
  `sqrt(-g_minus / -g_plus)` and `sqrt(-g_plus / -g_minus)`, with a declared
  density-measure convention.
- [ ] State Bianchi closure conditions:
  `nabla_plus_mu S_plus^{mu nu} = 0` and
  `nabla_minus_mu S_minus^{mu nu} = 0`, or the precise residuals still open.
- [ ] Choose gauge variables for scalar perturbations in each sector:
  `{Phi_plus, Psi_plus, delta_plus, theta_plus, Pi_plus}` and
  `{Phi_minus, Psi_minus, delta_minus, theta_minus, Pi_minus}`.
- [ ] Derive continuity and Euler equations for both sectors, including
  pressure, anisotropic stress and any membrane/orbifold transfer terms.
- [ ] Specify the orbifold/membrane junction at `a_sigma = 2/3`: matching
  variables, conserved quantities and allowed discontinuities.
- [ ] Define the photon observable map for positive-energy photons:
  visibility source, Weyl/lensing potential, Sachs-Wolfe terms and whether
  negative-sector stress enters through `Q_det`, `Q_cross`, a transport tensor,
  or a derived equivalent.
- [ ] Derive the BAO sound-ruler path: which metric controls photon-baryon
  acoustic propagation, what sets `r_d`, and how this differs from importing
  LambdaCDM `r_d`.
- [ ] Provide the zero-coupling regression target: background, perturbations,
  lensing and acoustic scales reduce to the selected GR/LambdaCDM baseline.
- [ ] Add numerical sanity gates before Planck comparison: constraint
  conservation, stability through `a_sigma`, finite transfer functions, and
  reproducible proxy observables (`theta_*`, `r_d`, Weyl/lensing proxy, TT
  peak-shift proxy).
- [x] Separate diagnostic Gaussian visibility from calibrated optical-depth
  visibility. CMB gates must use the calibrated physical visibility path, not
  the older proxy source.
- [x] Add a multipole LOS projection scaffold with spherical-Bessel kernels and
  explicit SW/Doppler/ISW components. This remains a proxy until the derived
  conformal-time mapping and source functions are supplied.
- [x] Add a conformal-distance mapping from the prototype background. The
  remaining projection scale between dimensionless `k` and physical multipoles
  is still explicitly marked as proxy-only.
- [x] Add a TE/EE polarization proxy from the local photon quadrupole history.
  This is not a Planck polarization solver until the Thomson source and gauge
  normalization are derived.
- [x] Add a solver-scaffold readiness score and adapter contract. Current
  scaffold status is above the 95% infrastructure threshold while physical
  Planck prediction readiness remains explicitly below threshold.
- [x] Promote the prototype from bi-sector scaffold to auditable Z4-projected
  metric-sector state: both projected `phi/psi` sectors are explicit,
  Newtonian-gauge residuals and membrane density-jump conservation are tracked,
  and the Z4 projection guard forbids interpreting them as independently
  dynamical metrics.
- [x] Add the formal `Janus Z4 CMB Solver` Lean wrapper. It separates
  Z4 architecture readiness from physical Planck readiness, so a complete
  scaffold cannot accidentally imply a validated CMB likelihood.

## Backend Decision Rule

If the derived Z4 projection collapses to a single effective metric with closed
source functions, CAMB/CLASS hooks can become more than diagnostics. If it
requires multiple projected metric-sector variables with nontrivial
transport/projection maps, the final validation backend must expose those
projected degrees of freedom directly before any CMB, BAO or growth result is
called prediction-ready.
