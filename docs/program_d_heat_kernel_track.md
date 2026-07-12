# Program D — Heat Kernel, Spectral Action and Renormalization Track

## Research question

Can the monopole/Pin-Z4 geometry of the Janus throat derive a complete quantum
effective action that selects the circle modulus and ultimately the absolute
scale, rather than merely reproducing the conditional relations

```text
q_LL = lambda_S2 / 8,
A = L?
```

This track separates three logically different objects:

1. **local heat-kernel coefficients** — UV divergences and local counterterms;
2. **nonlocal winding/holonomy terms** — global circle and Pin/Z4 information;
3. **finite renormalization data** — the scheme-dependent local coefficients
   that must be fixed by a microscopic law.

## Primary literature anchor

D. V. Vassilevich, *Heat kernel expansion: user's manual*,
`arXiv:hep-th/0306138`, collects the universal coefficients for Laplace-type
operators and their relation to one-loop divergences, anomalies and effective
actions. Program D uses this framework but keeps the actual Janus SpinC/Pin
operator construction as an explicit open theorem.

## H1 — Product-throat local invariants

For

```text
Sigma = S2_L x S1_(L*T),
```

the algebraic local invariants are

```text
Vol                         = 4*pi*L^3*T,
integral R                  = 8*pi*L*T,
integral R^2                = 16*pi*T/L,
integral |Ric|^2            = 8*pi*T/L,
integral |Riem|^2           = 16*pi*T/L,
integral F_{mu nu}F^{mu nu}= 2*pi*n^2*T/L
```

in the declared monopole convention. Every displayed integrated local invariant
is linear in `T`.

Lean:

```text
P0EFTJanusProductThroatLocalInvariants.lean
P0EFTJanusLocalHeatKernelScaling.lean
```

## H2 — Candidate Dirac Seeley–DeWitt coefficients

Omitting the common factor `(4*pi)^(-3/2)`, the standard complex rank-two Dirac
candidate gives

```text
a0_red = 8*pi*L^3*T,
a2_red = -(4*pi/3)*L*T,
a4_red = 2*pi*(5*n^2-1)*T/(15*L).
```

For a primitive monopole `n^2=1`,

```text
a4_red = 8*pi*T/(15*L) > 0.
```

These formulas are an explicit convention-dependent candidate. They must be
checked against the globally constructed Janus SpinC/Pin Dirac square and its
gauge-charge normalization before promotion to a physical theorem.

Lean:

```text
P0EFTJanusDiracSeeleyDeWittCandidate.lean
```

## H3 — Local spectral-action no-go

A local truncation through `a4` has the form

```text
S_local(T) = T * C_local(L, Lambda, moments, n).
```

Consequently exactly one of the following occurs:

```text
C_local > 0  -> strict increase in T,
C_local < 0  -> strict decrease in T,
C_local = 0  -> exact flat direction.
```

There is no isolated local minimum. This remains true for any finite list of
local heat-kernel coefficients on the direct product while the local densities
are independent of the circle coordinate.

Lean:

```text
P0EFTJanusTruncatedSpectralActionNoGo.lean
```

### Conclusion

Local Seeley–DeWitt data are necessary to renormalize the theory, but they do
not by themselves select the circle modulus.

## H4 — Poisson/winding separation

The twisted circle heat trace is represented by

```text
sum_n exp[-t*(2*pi*(n+a)/beta)^2]
 = beta/sqrt(4*pi*t)
   * sum_w exp[-beta^2*w^2/(4*t)] * exp(2*pi*i*w*a).
```

The `w=0` term is local and independent of holonomy. Holonomy occurs only in the
nonzero windings.

For antiperiodic holonomy `a=1/2`, the first winding has weight `-1` and
suppression

```text
exp[-beta^2/(4*t)].
```

For quarter holonomy `a=1/4`, the `w=1` weight vanishes and the first nonzero
term is `w=2`, with weight `-1` and stronger suppression

```text
exp[-beta^2/t].
```

Thus the Pin-Z4 holonomy is invisible to all local UV coefficients and begins
later in the winding expansion than the antiperiodic sector.

Lean and executable audit:

```text
P0EFTJanusCircleHeatKernelWinding.lean
scripts/audit_janus_heat_kernel_effective_action.py
```

## H5 — PT pairing

For a one-fold spectral action written as

```text
Gamma = Gamma_even[D^2] + Gamma_odd[eta(D)],
```

PT acts by

```text
Gamma_even -> Gamma_even,
Gamma_odd  -> -Gamma_odd.
```

The pair therefore gives

```text
Gamma_pair,even = 2*Gamma_even,
Gamma_pair,odd  = 0.
```

PT cancels the eta/anomaly phase but doubles:

- the parity-even determinant magnitude;
- the local heat-kernel coefficients;
- every finite parity-even counterterm;
- any parity-even runaway slope.

Lean:

```text
P0EFTJanusPairedSpectralActionDecomposition.lean
```

## H6 — Finite-counterterm degeneracy

Combine a positive local slope `c` with the exact-quarter nonlocal determinant.
With

```text
y = exp(2*x) > 1,
```

the stationarity equation is

```text
c*(y+1)=2*w.
```

For any chosen target `y>1`, the coefficient

```text
c_target = 2*w/(y+1)
```

satisfies

```text
0 < c_target < w
```

and produces a locally stable stationary point at that target.

Therefore every desired modulus can be fitted by a finite local coefficient.
Moreover, if the same target is stationary in two schemes, the two finite
coefficients must be equal. Any nonzero finite scheme shift moves the target.

Lean:

```text
P0EFTJanusHeatKernelCountertermScheme.lean
P0EFTJanusRenormalizationSchemeNoGo.lean
```

### Conclusion

A minimum generated by choosing a finite counterterm is not a prediction. The
finite coefficient must be derived from a microscopic matching condition,
symmetry or target-independent renormalization principle.

## Current theorem matrix

| Claim | Status |
| --- | --- |
| local coefficients scale linearly with `T` | proved algebraically |
| displayed product-throat curvature/monopole integrals | proved algebraically |
| candidate reduced Dirac `a0,a2,a4` formulas | conditional on standard operator convention |
| finite local spectral action has no isolated `T` minimum | proved |
| flat holonomy absent from local coefficients | encoded by winding separation; analytic Poisson theorem still to formalize |
| quarter holonomy starts at winding two | proved algebraically |
| PT cancels eta and doubles even action | proved algebraically |
| finite counterterm can fit any target modulus | proved |
| target invariant under nonzero scheme shift | impossible; proved |
| physical renormalized effective action | open |
| absolute scale | open |

## Next analytic sequence

1. Construct the global monopole-twisted SpinC/Pin Dirac operator on the actual
   throat.
2. Verify the Lichnerowicz endomorphism and bundle-curvature conventions.
3. Derive the exact heat trace and Poisson resummation, including multiplicities.
4. Compute the zeta determinant and APS/Hurwitz eta invariant.
5. Classify all allowed local counterterms under PT, gauge and world-volume
   symmetries.
6. Derive a target-independent microscopic condition fixing their finite parts.
7. Only then minimize the complete renormalized action and test whether its
   vacuum preserves the conditional `q_LL=lambda_S2/8` and `A=L` lock.

## Verdict

```text
LOCAL HEAT KERNEL:
  necessary, explicit, but cannot stabilize T alone.

NONLOCAL Z4 WINDINGS:
  geometrically distinctive, but UV suppressed and monotone in the pure sector.

FINITE LOCAL + NONLOCAL:
  can stabilize, but is non-predictive unless the finite coefficient is derived.

PROGRAM-D FRONTIER:
  construct the actual operator and a scheme-independent renormalized action.
```
