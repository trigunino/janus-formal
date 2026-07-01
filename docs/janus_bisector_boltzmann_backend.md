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
- [x] Derive the rank-one determinant-coupled source operator from the
  published coupled field equations. With reciprocal determinant weights, the
  source matrix has zero determinant and both sector equations descend from the
  single master source `T_plus + B*T_minus`.
- [ ] Define the determinant/cross-sector source factors, including
  `sqrt(-g_minus / -g_plus)` and `sqrt(-g_plus / -g_minus)`, with a declared
  density-measure convention.
- [ ] State Bianchi closure conditions:
  `nabla_plus_mu S_plus^{mu nu} = 0` and
  `nabla_minus_mu S_minus^{mu nu} = 0`, or the precise residuals still open.
- [ ] Choose gauge variables for scalar perturbations in each sector:
  `{Phi_plus, Psi_plus, delta_plus, theta_plus, Pi_plus}` and
  `{Phi_minus, Psi_minus, delta_minus, theta_minus, Pi_minus}`.
- [x] Add a scalar perturbation scaffold sourced by the rank-one Z4 master
  source, including background, Poisson and zero-coupling regression targets.
- [x] Add background and scalar-closure targets: Friedmann, continuity,
  momentum and slip equations are now explicit Z4 master-source obligations.
- [x] Add the background Bianchi identity check: differentiating Friedmann and
  applying master-source continuity recovers the Raychaudhuri equation without
  introducing an extra background fluid.
- [x] Add background action derivation: the normalized Z4 Einstein-Palatini
  sector fixes the Friedmann coefficient `8*pi*G/3` and closes the background
  coefficient lock.
- [x] Add scalar conservation identity bookkeeping: master `delta/theta/force`
  variables reduce to the single-sector limit without a fictitious cross-metric
  force.
- [x] Add scalar action derivation: Poisson, momentum and slip coefficients
  are tied to the normalized Z4 action, closing the scalar metric-sector lock.
- [ ] Derive continuity and Euler equations for both sectors, including
  pressure, anisotropic stress and any membrane/orbifold transfer terms.
- [x] Add the photon-baryon hierarchy target equations and make their
  coefficients explicit obligations of the Z4 source/action derivation.
- [x] Add photon-baryon source closure: projected Z4 `Phi/Psi` sources and
  antisymmetric Thomson drag are algebraically checked, while non-proxy
  Boltzmann execution remains open.
- [x] Add photon-baryon integrator target: a finite RK trajectory with projected
  Z4 metric sources and Thomson drag is tested, while calibrated Boltzmann
  hierarchy execution remains open.
- [x] Add photon-baryon non-proxy closure: physical `c_s^2`, baryon loading,
  Thomson drag balance and projected Z4 metric forcing are checked without a
  CMB fit proxy.
- [x] Add the physical recombination visibility target
  `tau_dot = a*n_e*sigma_T`, `g = tau_dot*exp(-tau)` and keep `x_e(a)` as the
  explicit non-proxy recombination input.
- [x] Add visibility normalization closure: the optical-depth/visibility path
  now has a unit-normalized kernel check and keeps the physical `x_e(a)` solve
  separate.
- [x] Add visibility non-proxy closure: bounded ionization history, positive
  recombination coefficients and optical-depth normalization provide the
  physical visibility input for the Z4 hierarchy.
- [x] Add hierarchy coefficient and ionization-history closure targets:
  `c_s^2`, baryon loading, Thomson drag, Peebles `x_e(a)` and baryon
  temperature are now explicit source/action obligations.
- [x] Add the stationary Peebles equilibrium solution for `x_e`: the physical
  positive root is checked algebraically and can feed visibility diagnostics,
  while the full time-dependent recombination solve remains open.
- [x] Add an ionization ODE solver target: a bounded proxy `x_e(a)` history and
  visibility-from-history path are tested, while calibrated Z4 recombination
  coefficients remain required for the physical non-proxy solve.
- [x] Add recombination coefficient closure: detailed balance fixes `beta` from
  the Saha equilibrium root and closes the Peebles equilibrium residual, while
  Z4 microphysical calibration remains required.
- [x] Add non-proxy output contracts for line-of-sight sources, Weyl/lensing
  sources and direct Planck adapter columns. These are interface contracts, not
  executed likelihood claims.
- [x] Add line-of-sight integrator target: a finite visibility/SW/ISW proxy
  integral is checked before any k/ell-resolved Planck transfer claim.
- [x] Add Planck spectrum export gate: `ell, cl_tt, cl_te, cl_ee, cl_pp`
  columns, monotone ell grid and finite values are checked before any direct
  likelihood claim is allowed.
- [x] Add Planck likelihood dry-run target: residual vector, positive diagonal
  covariance and finite chi2 are checked on proxy spectra without executing the
  official Planck likelihood.
- [x] Add Planck adapter ready closure: spectrum columns, ell grid, finite
  spectra, covariance contract and dry-run chi2 are validated. Official Planck
  likelihood execution is still not claimed by this closure.
- [x] Add CMB spectrum assembly target: finite proxy `TT/TE/EE/PP` spectra are
  exported in the Planck adapter shape before physical transfer-function
  spectra are claimed.
- [x] Add Weyl/lensing integrator target: a finite projected-Weyl kernel
  integral is checked before any `C_phi_phi` or Planck lensing likelihood claim.
- [x] Add the massless-neutrino hierarchy target, including quadrupole
  anisotropic stress as an explicit Z4 slip/lensing input.
- [x] Add neutrino free-streaming closure: the collisionless recursion and a
  finite-tail target have zero symbolic residual, while physical Boltzmann and
  Planck readiness stay false.
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
- [x] Add explicit Lean gates for action-variation closure and non-proxy CMB
  obligations, so "architecture installed" cannot be confused with "Planck
  prediction ready".
- [x] Add the action-variation matching target: the concrete Janus action must
  vary to `EL_plus = chi*(T_plus+B*T_minus)` and
  `EL_minus = -chi*B^-1*(T_plus+B*T_minus)`.
- [x] Close the linearized source-action variation:
  `L_source = chi*(h_plus-B^-1*h_minus)*(T_plus+B*T_minus)` varies to the
  determinant-coupled rank-one source operator. The nonlinear action remains
  open.
- [x] Add determinant-measure variation bookkeeping:
  `delta log B = (tr_minus-tr_plus)/2` and reciprocal consistency for `B^-1`.
  These terms are tracked but not yet inserted into the full nonlinear action.
- [x] Add boundary-variation closure bookkeeping: the linearized bulk boundary
  residual and determinant residual cancel against a single Z4 membrane
  counterterm. This still does not close the nonlinear action variation.
- [x] Add the full-action assembly target: source, determinant, boundary and
  gauge pieces are staged together, with the remaining nonlinear
  Euler-Lagrange residual exposed as `R_nl_plus/R_nl_minus`.
- [x] Add nonlinear residual factorization: the two residual channels reduce to
  one determinant-weighted obstruction `O_nl`, so the final action lock is
  `O_nl = 0` rather than two unrelated conditions.
- [x] Add obstruction Ward-identity target: `O_nl` is rewritten as
  `div_J_Z4 - A_Z4`; the final action lock is now the nonlinear gauge
  derivation of `div_J_Z4 = 0` and `A_Z4 = 0`.
- [x] Add anomaly-cancellation target: `A_Z4` is split into bulk, boundary
  and measure channels; the algebraic anomaly residual cancels, leaving
  nonlinear Z4 current conservation as the remaining action-level lock.
- [x] Add full action Ward closure: determinant-weighted Z4 current
  conservation combines with anomaly cancellation to set `O_nl = 0`. This
  closes the action-level obstruction, not the physical CMB hierarchy.
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
