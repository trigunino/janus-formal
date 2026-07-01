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
- [x] Add native Z4 CMB transfer solver: LOS/k/ell integration with spherical
  Bessel projection, visibility-weighted sources and primordial power now
  exports finite TT/TE/EE/PP spectra without the legacy CAMB fork.
- [x] Add Cobaya native provider/channel gate: `JanusZ4NativeBoltzmann` exposes
  `get_Cl`, and a custom Cobaya likelihood decomposes TT/TE/EE/PP chi2 channels.
  This is a technical Cobaya bridge, not an official Planck likelihood pass.
- [x] Add Planck-like channel decomposition for the native Z4 provider:
  high-l TT/TE/EE, lowE and lensing proxy channels are separated without using
  compressed LCDM parameters or the legacy CAMB fork. This remains a pre-clik
  diagnostic until the official Planck likelihood consumes the provider.
- [x] Add official Planck/Cobaya gates for native Z4 spectra where local
  likelihood data are available: low-l TT/EE, lensing, high-l TT and high-l
  TTTEEE execute without compressed LCDM parameters. Current native spectra are
  rejected; separate high-l TE/EE clik packages are unavailable locally.
- [x] Add shape-only diagnostic for the native Z4 spectra. The current dominant
  shape failure is high-l TE, followed by the first TT peak, EE and lensing.
  Adding finite-width visibility, Silk damping and lensing smoothing improves
  official high-l/lensing chi2 by orders of magnitude, but Planck still rejects
  the branch.
- [x] Add internal unit calibration and acoustic-time correction. The current
  official Planck verdict remains rejected, but the active native Z4 path now
  improves high-l TTTEEE to about `3.37e7` and lensing to about `3.05e3`.
  The remaining blocker is shape physics: missing TT power near the acoustic
  peak region and incorrect TE phase/source normalization.
- [x] Replace purely trigonometric acoustic sources with a stable minimal
  coupled photon-baryon source integrator. This improves the official high-l
  TTTEEE verdict further to about `1.6e6`, and the internal proxy shows TE is
  no longer the dominant channel. The remaining blockers are high-l TT shape,
  low-l TT rejection and lensing normalization/shape.
- [x] Split the Weyl/lensing source from the acoustic potential source. This is
  now represented explicitly in the native Z4 solver, but the official lensing
  chi2 remains around `1.08e4`. The next required change is a real
  `C_L^{phi phi}` projection kernel and normalization, not another acoustic
  source tweak.
- [x] Add an official Planck lensing amplitude diagnostic. Scaling only the
  native Z4 `C_L^{phi phi}` amplitude from `1e-4` to `1e2` does not solve the
  lensing gate; the current amplitude is already the best point in that scan.
  This isolates the blocker to the shape/projection kernel rather than a single
  missing multiplicative factor.
- [x] Densify the low/mid-ell grid and calibrate `C_L^{phi phi}` on a median
  `80 <= L <= 400` anchor instead of a low-L interpolation spike. This improves
  the official lensing chi2 to about `3.0e3` and high-l TTTEEE to about
  `4.3e5`. The branch is still rejected, but the remaining error is now a
  resolvable physical-shape problem rather than a broken adapter or a single
  amplitude factor.
- [x] Replace the polarization source with a minimal tight-coupling shear
  source from `v_b` and `dv_b/deta`. This slightly improves the internal
  proxy (`~56.8` to `~56.0`) and official lensing (`~3.0e3` to `~2.45e3`), but
  worsens official high-l TTTEEE (`~4.3e5` to `~5.3e5`). The result is kept as
  a diagnostic source model, not as an accepted CMB solution.
- [x] Add a peak/damping diagnostic that separates TT peak phase, TE zero-phase,
  EE peak phase and high-l TT damping slope. This turns the Planck rejection
  into explicit acoustic-source obligations instead of a single opaque chi2.
  Current output exposes large TT/EE peak mismatches, overly steep high-l TT
  damping and no TE zero crossing in the tested range.
- [x] Add a polarization-source scan comparing the active tight-coupling shear
  source, a minimal quadrupole hierarchy candidate and hybrid mixtures. The
  quadrupole branch restores TE zero crossings and improves lowE proxy, while
  the active shear branch remains the safer official-gate default. The hybrid
  scan shows this is not a simple mixing-weight problem; the quadrupole phase
  and normalization need a derived hierarchy.
- [x] Replace the scalar E-mode projection with the spin-2 E-mode kernel
  `sqrt((l+2)(l+1)l(l-1)) j_l(x)/x^2`. This is a physical projection
  correction, not a fit. Current official gate improves high-l TTTEEE from
  about `5.3e5` to about `4.6e5` and lowE from about `434` to about `412`, while
  Planck remains rejected.
- [x] Add an official E-mode projection-scale scan. Reducing the E projection
  scale to `0.4` improves high-l TTTEEE further to about `4.3e5`, but this is
  treated as a diagnostic normalization scan only. The active physical spin-2
  scale is restored to `1.0`; the remaining blocker is still source phase and
  hierarchy closure.
- [x] Add a low-l TT source-component diagnostic. The current low-l TT source is
  dominated by Sachs-Wolfe auto-power (`~70%`) with substantial ISW auto-power
  (`~23%`) and large destructive interference. This isolates the low-l TT
  failure to SW/ISW/source-interference physics rather than the TE/EE
  polarization branch.
- [x] Add a scalar-source scan over the Z4 potential horizon scale. Larger
  scales reduce the lowTT shape proxy slightly (`~4.36` to `~4.21` chi2/dof),
  but worsen high-l TT peak/damping proxies. This shows the SW/ISW issue is not
  solved by a scalar-potential scale tweak; the scalar source must be derived so
  low-l and high-l TT improve together.
- [x] Add the CMB/Z4 diagnostic master report. It audits the public-shape
  comparison, dominant pulls, shape-only gate, official Planck gates, lack of
  compressed LCDM parameters, visibility/Silk/lensing pieces, final verdict and
  remaining locks in one reproducible artifact.
- [x] Add physical closure audits for the three remaining CMB/Z4 blockers:
  polarization hierarchy, scalar SW/ISW closure and Weyl lensing projection.
  These are symbolic scaffolds only; all three physical-ready flags remain
  false until the Z4 action/geodesic coefficients are derived.
- [x] Strengthen those audits with coefficient-level algebraic targets:
  polarization closes at `c_q=1, c_v=0, c_z4=0`, Weyl lensing closes at
  `b_G=1, b_W=1, b_D=0, b_X=0`, and scalar SW/ISW now records the conditional
  `a_S=0, a_B=1` target while leaving `a_P/a_M` to action variation.
- [x] Add upstream action transport for the CMB/Z4 closure triad:
  `coefficientsFromFullZ4Action`, `scalarActionDerivedReady` and
  `sourceCoefficientsDerived` now transport the coefficient targets into the
  internal physical-closure triad. This does not claim an observational Planck
  pass; the official gate remains false.
- [x] Add a post-internal-closure Planck decomposition report. It separates the
  now-closed internal coefficient triad from the remaining observational shape
  failures and prioritizes a derived acoustic/polarization phase kernel before
  any further fitting-style scans.
- [x] Add the acoustic/polarization phase-kernel scaffold. It isolates
  monopole, Doppler, quadrupole, E-mode and Z4-free polarization variables and
  reduces the next physical lock to the tight-coupling identity
  `Theta2 = k*vb/tau_dot`, without changing the numerical solver.
- [x] Add the tight-coupling quadrupole identity audit. In the leak-free
  quadrupole equation, the dominant Thomson limit gives
  `Theta2 = k*vb/tau_dot` and feeds the phase-kernel residual. This is a
  symbolic closure only; spectra are not updated by this audit.
- [x] Add a branch-only phase-kernel application diagnostic. It applies
  `Theta2 = k*vb/tau_dot` to separate before/after spectra paths, including a
  visibility/Silk-damped branch with conserved normalization. It measures TE
  zero crossings, high-l TE shape, TT peak phase and EE shape, and records an
  integration verdict without changing the native solver or claiming Planck.
- [x] Add a Z4 parity/Holst polarization mixer diagnostic. It decomposes the
  source into even/odd parity channels and projects the odd channel by
  `cos(alpha_H)`. The current branch finds viable TE+EE candidates, with the
  best diagnostic point at `alpha_H = pi/2`, meaning the odd channel is rotated
  out of visible E-mode rather than added directly.
- [x] Add a membrane tetrad-transport diagnostic. It treats the polarization
  change as post-source Janus memory at `a_sigma=2/3`, applies the Z4
  quarter-turn `alpha_H=pi/2` to the odd polarization channel, improves TE and
  EE together, and leaves TT peak phase unchanged. This is still branch-only
  until official gates are rerun.
- [x] Add a fixed-geometry CMB idea screen. Without continuous fit factors,
  E/B-hidden conservation passes, Weyl mirror projection weakly improves
  lensing shape, and SW/ISW membrane memory fails its low-l TT guard.
- [x] Add a controlled geometric solver branch that combines E/B-hidden
  membrane transport and Weyl mirror projection. Shape diagnostics improve TE,
  EE and lensing while leaving TT and lowTT unchanged; this branch is ready for
  official-gate execution but is not itself a Planck validation.
- [x] Add a negative-sector primordial imprint diagnostic using the local Janus
  CMB-paper hypothesis that negative-sector structure can seed visible CMB
  fluctuations. The diagnostic keeps the scale ratio `100` and light-speed
  ratio `10` fixed, uses no continuous fit factor, and finds `jeans_blue` as the
  only promotable TT candidate that does not damage TE/EE. This is still a
  branch-only screen, not a Planck validation.
- [x] Integrate the controlled geometric branch with the fixed `jeans_blue`
  negative-sector imprint and export Planck-adapter spectra to `ell=2508`.
  The dedicated official-gate run rejects this integrated branch
  (`highl_TTTEEE ~4.09e5`, `highl_TT ~3.49e5`, low-l TT infinite). The imprint
  is therefore a useful TT-shape diagnostic, not the CMB solution.
- [x] Add the CMB failure map. It converts the integrated-branch Planck
  rejection into four derivation obligations: TT acoustic source/damping,
  low-l SW/ISW regularization, Weyl lensing projection kernel, and the
  polarization visibility/phase guard. This is now the active CMB to-do map.
- [x] Derive the leading TT acoustic source and low-l SW/ISW hidden-sector
  regularization. The symbolic result separates the visible and negative-sector
  acoustic sources and proves zero residual for hidden ISW cancellation and
  super-horizon SW compensation. This has not yet been inserted into the active
  solver.
- [x] Test the derived TT/SW-ISW terms in a controlled solver branch. The branch
  is finite and slightly improves shape proxies, but the dedicated official
  Planck gate worsens relative to the integrated imprint branch
  (`highl_TTTEEE ~4.09e5`, `highl_TT ~3.49e5`, low-l TT still infinite). The
  leading-order hidden-source insertion is therefore insufficient.
- [x] Derive and test mirror-even Weyl / TT clock transport. The symbolic guards
  close, but the controlled branch worsens low-l TT while only weakly improving
  the first TT peak; it is not safe for an official gate. Isolated source
  insertion is not the missing CMB mechanism.
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
- [x] Add the native GR-baseline gate. The solver now has a direct
  Z4-off/negative-sector-off/torsion-off integrity audit for finite sources,
  finite spectra, positive auto-spectra and normalized visibility. This is a
  regression target, not a Planck validation.
- [x] Add the observable oscilloscope. Active Z4 branches must expose SW,
  early-ISW, Weyl/lensing and `mu/Sigma/eta` diagnostics before any official
  CMB gate is interpreted.
- [x] Add the mirror/recombination roadmap. The next physical block must keep
  plus/minus photon-baryon states, separate visibility histories and Z4
  projection at the observable-source level; early collapse to `rho_eff` is
  explicitly forbidden.

## Backend Decision Rule

If the derived Z4 projection collapses to a single effective metric with closed
source functions, CAMB/CLASS hooks can become more than diagnostics. If it
requires multiple projected metric-sector variables with nontrivial
transport/projection maps, the final validation backend must expose those
projected degrees of freedom directly before any CMB, BAO or growth result is
called prediction-ready.

## Native GR Reference Gate

Before any further Z4 correction, the native solver must pass its GR-off
baseline check against a standard GR Boltzmann solver.

Current gate: `p0_eft_janus_z4_native_gr_reference_gate.json`.

Verdict: failed.

- Reference solver: `CAMB`.
- Z4 sector: off.
- Negative sector: off.
- Torsion: off.
- Shape-only amplitude fit: enabled per channel.
- Native GR matches standard GR: `false`.
- Z4 corrections allowed: `false`.
- TT first peak shift: `20`.
- high-TT chi2/dof: `229.0182013456774`.
- high-TE chi2/dof: `1295.8879821882795`.
- high-EE chi2/dof: `252.02176544373862`.
- lensing chi2/dof: `205.8213931365132`.

This means Planck rejection is not yet evidence about Janus/Z4 physics. The
native GR CMB engine itself must first reproduce a standard GR spectrum.

## Native GR Decomposition Gate

Current gate: `p0_eft_janus_z4_native_gr_decomposition_gate.json`.

Purpose: localize which GR block fails before any Z4 physics is interpreted.

Required decomposition:

- interface sanity: units, `Dl`/`Cl`, ell indexing, TE sign;
- background geometry: `zstar`, `zdrag`, `rstar`, `rdrag`, `D_M`, `theta_s`,
  `ell_A`;
- visibility: normalization, peak and width;
- fixed-k native sources: `S_T`, `S_E`, `S_ISW`, Weyl proxy;
- unlensed/proxy TT/TE/EE bands;
- lensing/phiphi split marker.

Blocking rule: no Janus/Z4 correction, torsion tuning or physical Planck
interpretation until this native GR decomposition gate is repaired.

## Native GR Acoustic Repair Scan

Current gate: `p0_eft_janus_z4_native_gr_acoustic_repair_scan.json`.

This tests the cheapest possible repair first: an ell/projection warp of the
native GR spectra against CAMB. If that fails, the mismatch is not just an
acoustic angular-scale error; the native LOS/source engine itself must be
repaired.

Current outcome: projection-only repair is insufficient. The next solver task is
the native GR source engine: TT monopole/Doppler/SW/ISW, TE phase, polarization
source and visibility transport.

## GR Backend Policy

Current policy: `p0_eft_janus_z4_gr_backend_policy.json`.

Until the native source engine reproduces CAMB in GR/Z4-off mode, CAMB is the
strict GR reference backend. Native spectra remain useful for diagnostics, but
not for physical Planck interpretation. Z4 corrections stay blocked unless they
are implemented as controlled deviations around a verified GR baseline.

Operational rule: the default Cobaya provider path is the CAMB-GR baseline
export. The old toy native LOS spectra can still be loaded explicitly for
diagnostics, but they are not the default Planck baseline.

## CAMB GR Baseline Export

Current export: `p0_eft_janus_z4_camb_gr_baseline_spectra.csv`.

The strict GR/Z4-off CAMB spectrum is now exported in the same native schema
(`ell`, `cl_tt`, `cl_te`, `cl_ee`, `cl_pp`). This gives the CMB pipeline a
verified GR baseline while preserving the block on the toy LOS source engine.

Current reduction gate: `p0_eft_janus_z4_gr_baseline_reduction_gate.json`.

Outcome: the dominant TT/TE mismatch is removed on the CAMB-backed baseline
path. This does not repair the toy native source engine; it establishes the
correct baseline around which future controlled Janus/Z4 deviations must be
implemented.

## Controlled Z4 Deviation Gate

Current gate: `p0_eft_janus_z4_controlled_deviation_gate.json`.

Allowed backend taxonomy:

- `camb_gr_safe_baseline`: Planck allowed.
- `native_toy_los_debug`: Planck forbidden.
- `camb_gr_plus_z4_delta`: Planck allowed only after delta gates pass.

Required invariants:

- `lambda_Z4 = 0` reproduces CAMB-GR in the native schema.
- raw toy LOS spectra never reach Planck.
- every Z4 correction is tagged by channel:
  `delta_weyl_lensing_kernel`, `delta_sw_isw_source`,
  `delta_acoustic_phase`, `delta_polarization_source`,
  `delta_background_projection`, `delta_hidden_sector_stress`.
- spectrum-level deltas are debug-only unless source/transfer coherence is
  proven.

## Weyl/Lensing Delta Gate

Current gate: `p0_eft_janus_z4_weyl_lensing_delta_gate.json`.

This is the first nonzero internal Z4 delta gate. It is deliberately limited to
the Weyl/lensing kernel:

- unlensed primary `TT/TE/EE` must remain unchanged;
- only `C_L^phiphi` may respond;
- convention is explicitly `C_L^phiphi`, not deflection power and not
  `L^4 C_L^phiphi`;
- small-lambda response must be finite, continuous and keep auto-spectra
  positive;
- official nonzero-Z4 Planck likelihood remains disabled until a separate
  remapping/eligibility gate exists.

## Lensed Remapping Response Gate

Current gate: `p0_eft_janus_z4_lensed_remapping_response_gate.json`.

This gate propagates the Weyl/lensing `C_L^phiphi` response through a controlled
lensed remapping diagnostic:

- input primary spectra are CAMB-GR unlensed/baseline spectra;
- the only nonzero input delta is the Weyl/lensing `phiphi` response;
- unlensed `TT/TE/EE` must remain unchanged;
- lensed `TT/TE/EE` responses must be finite and continuous;
- TT/EE peak positions and TE zero crossings must not jump for small lambda;
- a uniform `phiphi` amplitude delta is currently screened by the normalized
  smoothing diagnostic, so an observable lensing effect requires a shape delta
  or a more physical remapping kernel;
- nonzero-Z4 official Planck execution still requires a separate eligibility
  gate.

## Previous Objective: CMB Primordial Imprint Lock (completed internally)

**Goal:** derive the primordial CMB imprint for Janus-Z4 from a single
consistent action-to-projection chain, then only after that rerun official
Planck gates.

### 1) Acoustic source + SW/ISW kernel (hard lock)
- Derive TT source split from the full Z4 action: monopole + Doppler + ISW +
  ordinary/non-ordinary SW channels.
- Derive a single `Phi`/`Psi` source map used by both positive and mirror photon
  sectors.
- Enforce low-ℓ SW/ISW regularization so the integrated Sachs-Wolfe tail is
  finite at recombination crossing.

### 2) Polarization/tight-coupling + visibility lock
- Derive tight-coupling identity for quadrupole in the Z4-mirror setting,
  including the parity/transport projector from membrane passage.
- Couple physical visibility `g(η)` to the action-derived baryon-photon collision
  kernel (`tau_dot`) instead of proxy fitting factors.
- Enforce one phase-map for `TT/TE/EE` from recombination to line-of-sight.

### 3) Weyl/lensing + membrane transport kernel (hard lock)
- Derive the Weyl source and LOS projection kernel in the same sector basis used
  by `phi/psi` transport, including mirror-evanescent projection.
- Derive lensing transfer with a non-local kernel that is consistent with the
  same negative-sector/positive-sector junction used in the visibility model.
- Close consistency test: TT/EE/TE phase and lensing shape must move together
  under this kernel; if one channel shifts alone, reject the branch.

### Execution checklist
- Add symbolic derivations for all three blocks (one theorem per block + one
  composed lock theorem).
- Keep official Planck likelihood gates off during derivation; only run once all 3
  locks are closed.
- If any block cannot be derived, the correct status is an explicit `status =
  InProgress`, not a numerical scan result.

### Current status
- Internal lock report: `p0_eft_janus_z4_primordial_imprint_lock.json`.
- Current internal status: all three blocks are ready for a non-compressed
  official Planck gate.
- Official non-compressed Planck gate has now been rerun on native Z4 spectra.
  It is rejected:
  - low-l EE chi2: `411.7839883108354`;
  - lensing chi2: `2467.356660959575`;
  - high-l TT chi2: `368244.04651235015`;
  - high-l TTTEEE chi2: `464491.57901370607`;
  - low-l TT: rejected/non-finite;
  - high-l TE/EE standalone clik files: unavailable locally.
- This means the internal CMB locks are no longer the blocker. The blocker is
  now physical solver quality: native Z4 spectra are not observationally viable
  against Planck.
