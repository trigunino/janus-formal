# Program D7 — Spectral Theory Conclusion

## Research question

Can the monopole/Pin-Z4 geometry of the Janus throat determine the complete
renormalized effective action, stabilize the circle modulus and generate the
absolute length denoted `A = alphaSquaredLength` without importing an observed
cosmological radius?

## Stable decomposition

Program D7 now separates the calculation into four logically independent
layers:

```text
D7-L  local heat-kernel coefficients and counterterms
D7-N  nonlocal winding/holonomy determinant
D7-R  RG transmutation and independent UV anchor
D7-C  LL/bimetric/bulk-boundary charge compatibility
```

An absolute prediction requires all four.

## D7-L — Universal local heat coefficients

For a closed Laplace-type operator in the convention

```text
P = -(g^{mu nu} nabla_mu nabla_nu + E),
```

the reduced integrated coefficients `a0`, `a2`, and `a4` have been encoded from
the standard universal formulas, with the common factor `(4*pi)^(-d/2)`
omitted.

For the declared complex rank-two Dirac/monopole trace convention on

```text
Sigma = S2_L x S1_(L*T),
```

they reduce to

```text
a0 = 8*pi*L^3*T,
a2 = -(4*pi/3)*L*T,
a4 = 2*pi*(5*n^2-1)*T/(15*L).
```

For primitive monopole magnitude `n^2=1`,

```text
a4 = 8*pi*T/(15*L) > 0.
```

The universal reduction exactly matches the independently written Program-D
candidate.  A numerical sum over the separated primitive-monopole product
spectrum also recovers `a0`, `a2`, and `a4` from the small-time heat trace.

Lean heads:

```text
P0EFTJanusUniversalClosedHeatCoefficients.lean
P0EFTJanusProductThroatDiracHeatCoefficients.lean
P0EFTJanusFiniteProductHeatTrace.lean
```

Executable audit:

```text
scripts/audit_janus_d7_seeley_dewitt.py
```

### Local no-go

Every displayed integrated local invariant is linear in the dimensionless
circle modulus `T`.  Consequently every finite local truncation is affine in
`T` and has no isolated interior minimum.

Moreover, under the common transformation

```text
L -> s*L,
Lambda -> Lambda/s,
a0 -> s^3*a0,
a2 -> s*a2,
a4 -> a4/s,
```

the three-dimensional local spectral action through `a4` is invariant.
Therefore local Seeley-DeWitt data cannot select an absolute metric scale when
the UV unit co-scales.

## D7-N — Nonlocal winding sector

Poisson resummation separates the circle heat trace into:

```text
w=0       local and holonomy independent,
w != 0    nonlocal and holonomy dependent.
```

For exact quarter holonomy, the `w=1` cosine weight vanishes and the first
nonzero winding is `w=2`.  This is a genuine Pin-Z4 signature invisible to all
local UV coefficients.

However, the pure exact-quarter determinant is monotone.  PT pairing cancels
the eta-odd phase but doubles the parity-even determinant magnitude and any
runaway slope.  A pure paired Z4 sector therefore cannot stabilize `T`.

Finite-modulus candidates require at least one additional ingredient:

- another holonomy or spin sector;
- interactions;
- a boundary term;
- or a finite local coefficient fixed by a microscopic law.

A finite local coefficient can place a stationary point at any chosen target.
Thus a minimum obtained by choosing that coefficient is a fit, not a
prediction.  Scheme independence requires the finite coefficient to be derived
rather than adjusted.

## D7-R — Dimensionful scale generation

Let

```text
B*X = 8*pi^2,
m_dyn*exp(X) = mu_UV,
m_dyn*T*A = x_*.
```

Here:

- `x_*` is the stationary dimensionless product selected by the complete
  renormalized nonlocal action;
- `m_dyn` is a generated physical mass;
- `mu_UV` is an independently derived UV mass;
- `T` is the selected dimensionless circle modulus.

Then D7 proves

```text
mu_UV*T*A = x_* * exp(X),
A = x_* * exp(X)/(mu_UV*T).
```

This is the terminal absolute-length formula.  It is not yet a numerical
prediction because `B`, the UV coupling, `mu_UV`, `x_*`, and `T` must all be
derived independently of the target radius.

## D7-C — Charge and radius synthesis

With the positive primitive charge-radius lock

```text
4*q_LL*A^2 = 1
```

and the geometric identification

```text
A = L,
```

D7 also derives

```text
4*q_LL*L^2 = 1,
16*q_LL^2*A^4 = 1,
4*q_LL*x_*^2*exp(X)^2 = (mu_UV*T)^2.
```

The last equation eliminates the radius and relates the microscopic RG data
directly to the normalized LL charge.

Lean:

```text
P0EFTJanusD7AbsoluteAlphaSynthesis.lean
```

## Evidence matrix

| Statement | Level | Status |
| --- | --- | --- |
| universal closed `a0,a2,a4` algebra | **T** | formalized |
| product-throat curvature and monopole integrals | **T** | formalized |
| rank-two Dirac trace reduction | **C/T** | algebra formalized; global operator convention open |
| small-time spectral recovery of coefficients | executable audit | passes numerically |
| local action affine in `T` | **T** | proved |
| common local metric/cutoff scale orbit | **T** | proved |
| local coefficients see no flat holonomy | **C/T** | winding algebra formalized; analytic Poisson theorem open |
| pure quarter determinant cannot stabilize `T` | **T/C** | finite/algebraic no-go proved |
| PT cancels eta but doubles even action | **T** | proved algebraically |
| finite counterterm can fit any target | **T** | proved |
| complete scheme-independent nonlocal action | **P** | open |
| generated mass and UV anchor | **P** | open |
| terminal RG/charge/alpha formula | **C** | formalized |
| numerical no-fit `A` | **P** | not derived |

## Terminal theorem queue

1. Construct the actual global monopole-twisted Pin/SpinC Dirac operator on the
   mapping-torus throat.
2. Prove the separated infinite spectrum, multiplicities and completeness.
3. Derive the full heat trace, Poisson resummation and Mellin/zeta continuation.
4. Compute the eta invariant and zero-mode prescription in the same regulator.
5. Derive the complete field/ghost content and all determinant signs from the
   geometry.
6. Classify allowed finite counterterms under gauge, PT and world-volume
   symmetries.
7. Fix their finite parts by a target-independent microscopic matching law.
8. Derive one stable, unique, scheme-independent stationary product `x_*` and
   modulus `T`.
9. Compute the beta function and UV boundary law that generate `m_dyn` and fix
   `mu_UV`.
10. Prove equality of the spectral, LL, bulk and bimetric charge units.

## Final verdict

```text
D7 LOCAL SPECTRAL FOUNDATION:
  mathematically coherent and pushed to an explicit a0/a2/a4 frontier.

D7 PURE PIN-Z4 NONLOCAL SECTOR:
  distinctive but insufficient; it has a runaway modulus.

D7 COMPLETE EFFECTIVE ACTION:
  viable only with derived competing sectors/interactions and microscopic
  finite counterterms.

D7 ABSOLUTE ALPHA:
  conditionally reduced to
    A = x_* exp(X)/(mu_UV T),
  but not numerically predicted until the remaining microscopic inputs are
  derived without using the observed radius.
```

Program D7 is therefore retained as the correct spectral architecture.  Its
local mathematics is no longer the main uncertainty.  The decisive frontier is
the global interacting quantum theory and its target-independent
renormalization/UV law.
