# X2022-hal-acceleration-cosmic-expansion - Janus, the only cosmological model that explains the acceleration of cosmic expansion

## Metadata

- Year: 2022
- Axis: expansion
- Source level: HAL precursor / bridge source; do not use it over the journal anchors when `M15`, `M18`, or `M30` already fix the same point
- PDF: `data\raw\janus_library\X2022-hal-acceleration-cosmic-expansion_janus-the-only-cosmological-model-that-explains-the-acceleration-of-cosmic-expan.pdf`
- Text extract: `data\raw\janus_library_text\X2022-hal-acceleration-cosmic-expansion_janus-the-only-cosmological-model-that-explains-the-acceleration-of-cosmic-expan.txt`
- Extraction status: ok
- HAL status visible in PDF text: submitted 2022-11-17, revised 2023-02-17

## Logic Of Thought

This document is a bridge source. It packages, in one place:

- the one-metric negative-mass failure;
- the Janus coupled two-metric equations;
- the FLRW reduction with global signed-energy conservation;
- the exact open Janus expansion solution;
- the supernova magnitude-redshift fit and age estimate.

Use it to track how the expansion claim is assembled historically. For executable or formal reuse, keep `M15` as primary for coupled equations, `M18` for the SN/open-expansion formulas, and `M30` for the later bimetric formulation.

Tags: `expansion`, `signed_mass_sector`, `sn_fit`, `negative_energy`

## Formula And Equation Anchors

Curated anchors checked against the local PDF:

- Eq. (11): Hossenfelder-like sign-flipped bimetric setup.
- Eq. (12): Janus coupled field equations with determinant-ratio factors and opposite sign in the second equation.
- Eq. (19): `E = rho(+) c(+)^2 a(+)^3 + rho(-) c(-)^2 a(-)^3 = Cst`.
- Eqs. (20a)-(20b): dust-era exact acceleration equations for the positive and negative sectors.
- Eqs. (22)-(23): `a(+)(u) = alpha^2 cosh^2(u)`, `t(+)(u) = alpha^2/c(+) * (1 + sinh(2u)/2 + u)`.
- Eq. (24): `q = -1 / (2 sinh^2(u))`.
- Eq. (25): bolometric magnitude-redshift law.
- Eq. (26): best-fit `q0 = -0.087 +/- 0.015`.
- Eq. (28): best-fit age claim `T0 = 1.07/H0 = 15.0 Gyr`.
- Appendix B Eq. (20): `T0.H0 = -2q0(1 - 2q0)^(-3/2) * (argsh(-1/(2q0)) - sqrt(1 - 2q0)/(2q0))`.

Paper-native explicit claims:

- `k+ = k- = -1` on the hyperbolic FLRW branch used here.
- the universe content is stated as `96%` invisible negative mass and `4%` positive mass.

## Core Ideas / Cues

Keyword signals from the extract: `negative mass`, `Schwarzschild`, `redshift`, `dark energy`, `dark matter`, `supernova`.

Useful content split:

- Sections I-IV: Bondi/runaway failure in one-metric GR, then transition to the two-metric Janus construction.
- Section V: actual cosmology payload - FLRW ansatz, signed-energy conservation, exact expansion branch, SN fit, age, and matter-content interpretation.
- Appendix A: stationary/matter compatibility discussion; explicitly says the coupled system is intended to remain compatible only under a Newtonian-approximation regime in that analysis.
- Appendix B: redshift, distance, magnitude, and age derivations.

## Observational Hooks

Directly reusable:

- supernova-only magnitude-redshift relation;
- `q0 = -0.087 +/- 0.015`;
- best-fit age claim `15.0 Gyr`;
- qualitative replacement of dark matter and dark energy by one negative-mass sector.

Not provided here as executable observable machinery:

- no BAO ruler derivation;
- no CMB likelihood path;
- no survey-covariance implementation beyond the SN fit discussion.

## Verification Notes

What this source adds relative to the rest of the library:

- it is the cleanest single precursor that combines the `M15`-type coupled equations with the `M18`-type expansion/SN formulas;
- it does not supersede `M15`, `M18`, or `M30` as primary anchors;
- it is useful for tracing the paper-native claim that acceleration comes from negative-energy dominance without introducing `Lambda`.

Manual status: checked precursor card. Safe to cite as a bridge source; do not promote it above the journal anchors for the same formulas.
