# Janus Axioms Draft

Status: working formalization, not a final theory.

## Source Discipline

- Every axiom must trace to `docs/verified_formula_register.md`.
- A source claim is not observational proof.
- A derived claim must state its assumptions before being compared to data.

## Axiom J1: Two Sectors

There are two gravitational sectors:

- positive mass/energy sector;
- negative mass/energy sector.

Source anchors: `M15`, `M30`.

## Axiom J2: Two Metrics / Two Geodesic Families

Positive mass entities and positive-energy photons follow geodesics of one metric.
Negative mass entities and negative-energy photons follow geodesics of the conjugate metric.

Source anchors: `M15`, `M30`.

## Axiom J3: Coupled Field Equations

The two metrics are coupled by field equations with opposite sector signs and determinant-ratio factors.

Source anchor: `M15`, Eqs. 4a-4b.

## Axiom J4: Newtonian Interaction Limit

In the double Newtonian approximation:

- same signs attract;
- opposite signs repel.

Equivalent sign bookkeeping:

```text
coupling(source, test) = density_sign(source) * metric_equation_sign(test)
density_sign(+) = +1
density_sign(-) = -1
metric_equation_sign(g+) = +1
metric_equation_sign(g-) = -1
```

Weak-field Poisson source terms using absolute densities:

```text
Delta Phi_+ = 4 pi G (rho_+ - |rho_-|)
Delta Phi_- = 4 pi G (-rho_+ + |rho_-|)
```

Source anchors: `M15`, Eq. 6 and Sect. 4; `M30`, after Eq. 106.

## Axiom J5: Exact Expansion Branch

For the positive sector dust-era branch used in current expansion work:

- `a(u) proportional cosh(u)^2`;
- `t(u)` is proportional to `1 + sinh(2u)/2 + u`;
- `q = -1/(2 sinh(u)^2)`.

Source anchor: `M18`, Eqs. 10 and 13.

## Axiom J6: Open Distance Marker

For the same branch, the open marker distance is:

`r = sinh(2(u0 - ue))`.

Source anchor: `M18`, Eqs. 15-17.

## Axiom J7: Variable-Constants Gauge

In the variable-constants regime:

- `c_hat proportional a^-1/2`;
- `h_hat proportional a^(3/2)`;
- `G_hat proportional a^-1`;
- `e_hat proportional a^(1/2)`;
- `m_hat proportional a`;
- `t_hat proportional a^(3/2)`;
- `mu0_hat proportional a`.

Source anchor: `X2026-variable-constants`, Eq. 40.

## First Proof Targets

1. Derive `q = -1/(2 sinh(u)^2)` from the parametric expansion.
2. Verify the gauge invariants implied by Eq. 40.
3. Formalize same-sign attraction/opposite-sign repulsion as the Newtonian limit of the bimetric equations.
4. Derive an observable BAO ruler map without importing Lambda-CDM assumptions.
5. Derive the positive-photon weak-lensing normalization before defining `S8_eff`.
