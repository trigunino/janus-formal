# Janus Asymptotic / Null Boundary Symmetry Branch

## Target

Use infinite-dimensional boundary symmetry machinery to attack the blocker left
by the finite CP1/TQFT quantum-first branch:

`no boundary mass/energy operator`.

Candidate tools:

- BMS / extended BMS symmetry;
- Bondi mass and supertranslation charges;
- Newman-Penrose null tetrad and asymptotic charges;
- Wald-Zoupas / covariant phase space charges on null boundaries.

## Bibliography Anchors

- BMS group: asymptotic symmetries and Bondi charges at null infinity.
- Wald-Zoupas: covariant charges and flux balance at null infinity.
- Null-boundary covariant phase space: Hamiltonians exist only after boundary
  conditions and null-generator normalization are fixed.
- Newman-Penrose formalism: natural language for null boundaries and mass
  aspects.

Representative references used for orientation:

- [Lectures on the BMS group and related topics](https://link.springer.com/article/10.1140/epjc/s10052-025-15091-z)
- [Covariant phase space with null boundaries](https://arxiv.org/abs/2008.10551)
- [Brown-York charges at null boundaries](https://www.researchgate.net/publication/357742909_Brown-York_charges_at_null_boundaries)
- [Wald-Zoupas prescription at null infinity](https://ui.adsabs.harvard.edu/abs/2022CQGra..39h5002G/abstract)

## Result

This is the right class of machinery if Janus can supply a real null/asymptotic
boundary. It gives the kind of object we need: a surface charge with an energy
generator.

But the current Janus core does not yet provide:

- an asymptotically flat null infinity for BMS;
- or an active internal null bridge with fixed boundary conditions;
- or a normalized null/time generator;
- or an integrable Janus surface charge;
- or sector quantization of that charge.

## Conditional Bridge

If a valid charge `Q_boundary` is derived:

```text
M_bridge = Q_boundary / c^2
alpha_m = -2*pi*G*M_bridge/c^2
R_s = 2*G*M_bridge/c^2
chi_LL = -1/(8*pi*R_s)
```

## Verdict

`final_branch_status = best_next_framework_but_missing_Janus_null_boundary_data`.

This branch improves the diagnosis: the finite quantum route lacked energy;
BMS/NP/covariant phase space is exactly about energy charges. It still cannot
predict `alpha` until Janus supplies the actual null/asymptotic boundary data.
