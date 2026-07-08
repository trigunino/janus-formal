# Verified Formula Register

Verification date: 2026-06-19.

Method: direct checks against the local PDF text extracts generated from `data/raw/janus_library/*.pdf`. A row marked `verified` means the formula or claim was located in the local source with its equation number or nearby section. A row marked `verified-concept` means the source text confirms the conceptual anchor, but it is not a single equation.

## Verified Anchors

| Source | Anchor | Verification | Notes |
|---|---|---|---|
| `M15` | Bondi one-metric force law, Eqs. 1-3 | verified | The paper gives Einstein's equation, Bondi's Newtonian acceleration, then states the runaway consequence for positive/negative masses. |
| `M15` | Coupled equations, Eqs. 4a-4b | verified | PDF text contains both coupled equations with the determinant-ratio factors and opposite sign in the second equation. |
| `M15` | Tensor signs, Eq. 5 | verified | PDF text states `rho(+)>0, p(+)>0` and `rho(-)<0, p(-)<0`. |
| `M15` | Double Newtonian approximation, Eq. 6 | verified | PDF text gives expansions of `g(+)` and `g(-)` around Lorentz metrics. |
| `M15` | Janus interaction laws | verified | Section 4 states same signs attract and opposite signs repel. |
| `M15` | Two geodesic families | verified | Text states positive-energy photons/positive masses follow one metric geodesic system and negative-energy photons/negative masses the other. |
| `M07` | Inverse / negative gravitational lensing | verified-concept | Abstract and Sect. 3 state inverse gravitational lensing and negative lensing from antipodal/negative mass. Treat as a concept anchor until equations are curated from the PDF. |
| `M07` | Negative-mass hole gives positive lensing | verified-concept | Sect. 3 states that a hole in a negative-mass distribution produces a positive gravitational lensing effect. This is central for any Janus weak-lensing map. |
| `M07` | Large-scale two-sector simulations and two-point correlation | verified-concept | Sect. 2 discusses 2D simulations, two-point correlation, and the need for larger 3D simulations before observational comparison. |
| `M07` | Publication status | verified-source-claim | Local text extract states received 14 July 1994, accepted 7 February 1995, and Kluwer Academic Publishers. Use as accepted-publication concept anchor, not as an equation anchor until formulas are curated. |
| `M18` | SN magnitude-redshift proxy, Eq. 5 | verified | PDF text gives the `5 log10[...] + cst` bolometric magnitude relation. |
| `M18` | `q0 = -0.087 +/- 0.015`, Eq. 6 | verified | PDF text states this value from the Betoule et al. SN data fit. |
| `M18` | Exact expansion `a(u)`, `t(u)`, Eq. 10 | verified | Appendix text gives `a(u) = alpha^2 cosh^2(u)` and `t(u)` with `sinh(2u)/2 + u`. |
| `M18` | `q = -1/(2 sinh^2(u))`, Eq. 13 | verified | PDF text gives the deceleration relation. |
| `M18` | `(1 - 2q) = c^2/(a^2 H^2)`, Eq. 14 | verified | PDF text gives this conversion relation. |
| `M18` | Open marker distance, Eqs. 15-17 | verified | PDF text gives `l = 2u0 - 2ue`, `l = argsh(r)`, and `r = sinh(2u0 - 2ue)`. |
| `M18` | `u0`, `ue` mappings, Eqs. 20-21 | verified | PDF text gives the `argch/argsh` mappings from `q0` and `z`. |
| `X2022-hal-acceleration-cosmic-expansion` | Coupled equations, Eq. 12 | verified | HAL precursor restates the determinant-ratio Janus coupled equations and opposite sign in the second equation. Use `M15` as the cleaner journal anchor. |
| `X2022-hal-acceleration-cosmic-expansion` | Global signed-energy conservation, Eq. 19 | verified | PDF text gives `rho(+) c(+)^2 a(+)^3 + rho(-) c(-)^2 a(-)^3 = Cst`. |
| `X2022-hal-acceleration-cosmic-expansion` | Exact expansion `a(u)`, `t(u)`, Eqs. 22-23 | verified | PDF text gives `a(+)(u) = alpha^2 cosh^2(u)` and `t(+)(u)` with `1 + sinh(2u)/2 + u`. This is the same expansion branch later isolated in `M18`. |
| `X2022-hal-acceleration-cosmic-expansion` | `q = -1/(2 sinh^2(u))`, Eq. 24 | verified | PDF text gives the deceleration relation on the open Janus branch. |
| `X2022-hal-acceleration-cosmic-expansion` | SN magnitude-redshift proxy, Eq. 25 | verified | PDF text gives the bolometric magnitude relation. |
| `X2022-hal-acceleration-cosmic-expansion` | `q0 = -0.087 +/- 0.015`, Eq. 26 | verified | PDF text gives the same SN fit value as the later journal source `M18`. |
| `X2022-hal-acceleration-cosmic-expansion` | Best-fit age claim, Eq. 28 | verified | PDF text states `T0 = 1.07/H0 = 15.0 Gyr` for the preferred fit. |
| `X2022-hal-acceleration-cosmic-expansion` | Negative-mass content split | verified-concept | Section V states `96%` invisible negative mass and `4%` positive mass. Treat as a paper-native model claim, not as an independently validated observational result. |
| `M22` | Negative sector shorter Jeans time, Eq. 1 | verified | PDF text states greater negative density implies `t_J(-) << t_J(+)`; OCR of rho symbols is imperfect but the surrounding sentence is clear. |
| `M20` | Negative-sector CMB imprint | verified-concept | Text states gravitational instability in the negative sector leaves an imprint in the positive sector corresponding to CMB inhomogeneities. |
| `M20` | Negative lensing and galaxy/cluster lensing claim | verified-concept | Introduction claims observed gravitational lensing is mainly due to negative matter around galaxies/clusters, and that negative lensing can weaken high-redshift galaxy light. |
| `M20` | Scale-factor ratio from CMB imprint, Eq. 10 | verified | Text gives `a(-)/a(+) ~= 1/100` as an order-of-magnitude scale-factor ratio. This is not yet a determinant-ratio lensing amplitude. |
| `M30` | Single-field signed-mass failure, Eqs. 75-79 | verified | PDF text gives the one-metric equation, positive/negative Schwarzschild-like metrics, and single-family-geodesic runaway conclusion. |
| `M30` | Distinct geodesics in bimetric Janus | verified-concept | Introduction and Sect. 9 state positive/negative masses evolve on distinct geodesics/metrics. |
| `M30` | Mixed stationary coupled equations, Eqs. 105a-105b | verified | PDF text gives the mixed equations with constants `b^2` and `bar b^2`. |
| `M30` | Newtonian terms, Eq. 106 | verified | PDF text gives the non-zero tensor terms used in the Newtonian approximation. |
| `M30` | Determinant ratio in Newtonian approximation, Eq. 124 | verified | Text states the determinant ratio is considered almost unity in the Newtonian approximation. This blocks naive use of M20 `a(-)/a(+)` as `Q_det`. |
| `M30` | Interaction laws after Eq. 106 | verified | PDF text states same signs attract and opposite signs repel, eliminating runaway. |
| `M31` | Janus symplectic group action on torsors | verified-concept | Abstract states the group action on the dual of the Lie algebra, called torsors. |
| `M31` | Energy, momentum, charge interpretation | verified-concept | Introduction links energy to time translations, momentum to spatial translations, and charge to the added fifth-dimensional scalar. |
| `X2025-kinetic-galactic` | Vlasov/collisionless Boltzmann equation, Eq. 9 | verified | PDF text gives the compact collisionless equation. |
| `X2025-kinetic-galactic` | Poisson equation, Eq. 11 | verified | PDF text gives `Delta Psi = 4 pi G rho`. |
| `X2025-kinetic-galactic` | Galaxy velocity plateau claim | verified-concept | Abstract states the velocity tends toward a remote plateau consistent with observational data. |
| `X2026-variable-constants` | `m_hat proportional a`, Eq. 19 | verified | PDF text derives the mass gauge from Einstein-constant invariance. |
| `X2026-variable-constants` | `c_hat proportional a^-1/2`, Eq. 21 | verified | PDF text derives this from energy conservation. |
| `X2026-variable-constants` | `G_hat proportional a^-1`, Eq. 24 | verified | PDF text derives this from Einstein-constant invariance. |
| `X2026-variable-constants` | `t_hat proportional a^(3/2)`, Eq. 30 | verified | PDF text derives this from Lorentz/metric gauge invariance. |
| `X2026-variable-constants` | Final gauge set, Eq. 40 | verified | PDF text groups `c_hat`, `h_hat`, `G_hat`, `e_hat`, `m_hat`, `t_hat`, and `mu0_hat` against `a`. |
| `X2026-variable-constants` | Characteristic lengths/times | verified | Text after Eq. 40 states lengths vary as `a` and times as `a^(3/2)`. |
| `X2026-expansion-desi` | DESI-oriented expansion claim | verified-source-claim | Abstract states the Janus exact expansion law is consistent with recent DESI observations and stronger past acceleration. This verifies the source claim, not independent correctness. |
| `X2026-expansion-desi` | Energy condition and exact solution, Eqs. 27-29 | verified | PDF text gives the global energy condition and the two exact acceleration equations. |
| `X2025-bimetric-hal` | Bimetric Sakharov model | mirror-verified | Local HAL text mirrors the M30 bimetric work; use `M30` as primary anchor. |
| `X2025-symplectic-hal` | Janus symplectic group | mirror-verified | Local HAL text mirrors the M31 symmetry work; use `M31` as primary anchor. |

## Not Yet Verified As Exact Formulas

| Source | Item | Reason |
|---|---|---|
| `M26` | Time-reversal operator details | PDF text extraction is weak/empty. Use the PDF visually before extracting formulas. |
| Auto-indexed source cards | Non-curated snippets | These are navigation aids only until promoted into this register. |
