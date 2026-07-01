# TODO - Janus Orbifold Validation

## Current verdict

- Formal topology scaffold: closed.
- Late-time growth / SDSS-eBOSS branch: viable as EFT diagnostic.
- BAO `r_d`: requires a real pre-drag background contraction.
- CMB Planck: mono-metric CAMB hooks tested so far are not enough.
- Therefore: do not claim full no-fit cosmology yet.

## Priority 1 - Define the bi-sector model

- [x] Write the first minimal linear Janus-orbifold prototype with two sectors:
  - visible/positive sector;
  - mirror/negative sector;
  - coupling matrix between density, velocity and potentials;
  - membrane/orbifold junction at `a_sigma = 2/3`;
  - observable photon projection.
- [x] State and test the GR/LambdaCDM limit when Janus couplings go to zero.
- [ ] State which metric controls:
  - background expansion `H(a)`;
  - photon-baryon acoustic perturbations;
  - lensing Weyl potential;
  - BAO ruler `r_d`.

## Priority 2 - Build a minimal Janus-Boltzmann prototype

- [x] Create a small Python prototype, separate from CAMB:
  - background ODE;
  - two-sector scalar perturbations;
  - photon observable projection;
  - no recombination complexity at first.
- [x] Verify first numerical sanity gates:
  - recovers LambdaCDM in the zero-coupling limit;
  - conserves total constraint equations;
  - stable through the membrane crossing.
- [x] Compare only proxy observables first:
  - `theta_*`;
  - `r_d`;
  - Weyl/lensing proxy;
  - TT peak-shift proxy.

## Priority 3 - Decide backend strategy

- [ ] If the prototype reduces to effective single-sector source functions, keep CAMB/CLASS hooks.
- [ ] If it needs two dynamical metric sectors, stop treating CAMB as final validation.
- [ ] Evaluate CLASS/hi_class as the next backend before any from-scratch full solver.
- [ ] Keep CAMB fork as a diagnostic baseline only.

## Priority 4 - Observational gates

- [ ] Re-run SDSS/eBOSS `f_sigma8` only after the bi-sector equations are fixed.
- [ ] Re-run DESI BAO with the derived `r_d`, not a fitted ruler.
- [ ] Re-run Planck only after the same equations drive:
  - background;
  - perturbations;
  - lensing;
  - visibility/recombination assumptions.

## Priority 5 - Documentation locks

- [ ] Mark old mono-metric CMB hook failures as "CAMB-EFT tests", not Janus exclusion.
- [ ] Keep `full_cosmology_prediction_ready_no_fit = False` until Planck + BAO + growth pass under one derived bi-sector model.
- [x] Add a short architecture note explaining why Janus-orbifold may require a bi-sector Boltzmann backend.
