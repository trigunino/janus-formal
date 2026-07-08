# Janus Complex Reality Combined Phase-Space Candidate

## Candidate

Combine the three retained candidates instead of selecting one prematurely:

```text
CP1 spinor/frame fiber
  over active throat S2
  with aroundSigma holonomy constraint
```

Interpretation:

- active throat `S2`: physical Janus/Sigma support;
- `CP1`: compact quantum boundary fiber with known KKS period;
- `aroundSigma`: global tunnel holonomy/monodromy constraint.

## Why It May Help

The individual candidates each miss one structural piece:

- `S2` has support but may lack nonzero KKS density;
- `CP1` has quantization but lacks Janus anchoring;
- `aroundSigma` has tunnel topology but only one cycle.

The combined candidate can pair them:

- support from `S2`;
- quantization from `CP1`;
- sector selection from `aroundSigma` holonomy.

## Current Status

This is a coherent combined candidate, not yet a derivation.

Required next:

1. derive `CP1` as a boundary spinor/frame fiber from Janus/PT;
2. derive action of `aroundSigma` holonomy on that `CP1`;
3. prove the combined two-cycle has nonzero KKS period;
4. derive the map from period/sector to `alpha_m`.

## First Derivation Pass

- `CP1` from local boundary spinor line:
  mathematically ready as `P(C^2) = CP1`, but not globally Janus/PT-derived.
- `aroundSigma -> CP1`:
  central spin lift acts trivially on `CP1`; useful noncentral projective
  action would require a derived spin/Pin holonomy around `aroundSigma`.
- combined KKS period:
  symbolic period is nonzero if `j != 0`, with
  `Integral_CP1 Omega_j = 4*pi*j`; Janus-derived nonzero period remains blocked
  by missing global CP1 derivation, holonomy action, and sector selection.

Noncentral spin-lift search:

- central lift `psi -> -psi`: admissible, but trivial on `CP1`;
- noncentral pi-rotation: useful in principle, but requires a derived
  Pin/spin holonomy axis around `aroundSigma`;
- current status: not derived.

## Verdict

The combined candidate survives mathematically:

```text
Integral_CP1 Omega_j = 4*pi*j
```

is nonzero if `j != 0`.

It does not yet survive as a Janus-derived alpha law. The remaining blockers are
global spinor/Pin projection, noncentral `aroundSigma` lift, sector selection,
and `alpha` map.
