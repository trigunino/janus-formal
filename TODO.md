# TODO - Janus Orbifold Validation

## Current verdict

- Formal topology scaffold: closed.
- Late-time growth / SDSS-eBOSS branch: viable as EFT diagnostic.
- BAO `r_d`: requires a real pre-drag background contraction.
- CMB Planck: native Z4 gate executed after primordial-imprint lock; current
  spectra are rejected by Planck.
- Native GR baseline: fails against CAMB shape-only reference, so Z4 corrections
  are premature until the GR acoustic/recombination/lensing engine is fixed.
- Native GR decomposition: required now; Planck rejection is suspended as a
  physical Janus/Z4 verdict until this baseline is repaired.
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

- [x] Add native GR vs CAMB reference gate.
- [x] Add native GR decomposition gate:
  - interface sanity;
  - acoustic background geometry;
  - visibility;
  - fixed-k source diagnostics;
  - unlensed TT/TE/EE bands;
  - lensing/phiphi split marker.
- [ ] Fix native GR baseline before any new Z4 physics:
  - high-TT chi2/dof against CAMB is too high;
  - TE phase/shape is wrong;
  - EE and lensing shapes are wrong;
  - first TT peak is shifted by more than the allowed tolerance.
- [x] Test whether projection/acoustic warping alone can repair native GR:
  - result: insufficient;
  - source/LOS engine repair is required before Z4.
- [x] Add GR backend policy:
  - CAMB is the strict GR reference backend while native GR is broken;
  - native Planck interpretation remains blocked;
  - Z4 corrections remain blocked unless implemented as controlled deviations
    around a verified GR baseline.
- [x] Export CAMB GR baseline in the native spectra schema:
  - this provides a safe GR/Z4-off baseline;
  - dominant TT/TE mismatch is reduced on the baseline path;
  - the toy native source engine remains explicitly unrepaired.
- [x] Route default Cobaya provider to the safe CAMB-GR baseline:
  - toy native LOS spectra are now explicit diagnostics only;
  - Planck default path no longer uses the broken toy baseline.
- [x] Add controlled Z4 deviation gate:
  - `lambda_Z4 = 0` reproduces CAMB-GR roundtrip;
  - raw native toy LOS spectra are forbidden for Planck;
  - all deltas must be tagged by physical channel;
  - spectrum-level deltas are debug-only unless source/transfer coherence is proven.
- [x] Add first nonzero internal delta gate: Weyl/lensing kernel:
  - unlensed TT/TE/EE unchanged;
  - `C_L^phiphi` convention checked;
  - small-lambda response finite and continuous;
  - nonzero Z4 remains not Planck-eligible until remapping/eligibility gates exist.
- [x] Add lensed remapping response gate:
  - CAMB-GR unlensed input plus Z4 `phiphi` delta;
  - unlensed primary remains unchanged;
  - lensed TT/TE/EE response is finite and continuous;
  - acoustic peak/TE-zero jumps are blocked;
  - current response is screened as a uniform phiphi-amplitude delta;
  - observable lensing requires a shape delta or more physical remapping kernel;
  - nonzero Z4 still needs a separate Planck eligibility gate.
- [x] Add the CMB primordial imprint lock:
  - TT acoustic source + SW/ISW;
  - Theta2 + physical visibility transport;
  - Weyl/lensing membrane projection.
- [x] Close the internal CMB primordial imprint lock without running Planck:
  - all block statuses true in `p0_eft_janus_z4_primordial_imprint_lock.json`;
  - next allowed action is the official non-compressed Planck gate.
- [ ] Re-run SDSS/eBOSS `f_sigma8` only after the bi-sector equations are fixed.
- [ ] Re-run DESI BAO with the derived `r_d`, not a fitted ruler.
- [x] Re-run Planck after the internal primordial-imprint lock:
  - background;
  - perturbations;
  - lensing;
  - visibility/recombination assumptions.
- [ ] Fix the post-lock Planck rejection:
  - current Planck gates consume the safe CAMB-GR baseline provider;
  - native Z4 spectra are not used by default;
  - toy native source engine remains blocked;
  - high-l TE/EE standalone clik files are unavailable locally.

## Priority 5 - Documentation locks

- [ ] Mark old mono-metric CMB hook failures as "CAMB-EFT tests", not Janus exclusion.
- [ ] Keep `full_cosmology_prediction_ready_no_fit = False` until Planck + BAO + growth pass under one derived bi-sector model.
- [x] Add a short architecture note explaining why Janus-orbifold may require a bi-sector Boltzmann backend.
