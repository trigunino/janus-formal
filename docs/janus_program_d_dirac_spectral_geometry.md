# Program D2 — Twisted Dirac Spectral Geometry

## Status

Active stacked research branch:

```text
research/fundamental-geometry-dirac-spectral
```

Focused Lean target:

```text
lake build JanusFormal.Branches.FundamentalGeometryDiracSpectral
```

This branch asks whether the effective world-volume dynamics can be derived
from the spectrum of a geometrically defined twisted Dirac operator on the
canonical throat

```text
Sigma = S2_L x S1_(L*T).
```

It is stacked on Program D but deliberately avoids importing the aggregate
Program-D branch head, so its operator algebra and CI can be tested
independently.

## 1. Spectral input on the monopole two-sphere

For the round two-sphere of radius `L`, twisted by a monopole line bundle of
absolute Chern number `m`, the standard spectral labeling is

```text
lambda_k^2 * L^2 = k * (k + m),
k = 0,1,2,...,
degeneracy_k = m + 2*k.
```

Consequences:

```text
k=0:
  lambda_0 = 0,
  zero-mode multiplicity = m;

k=1:
  lambda_1^2 * L^2 = m + 1.
```

The signed index equals the signed Chern number and the zero-mode multiplicity
is its absolute value.  In the primitive sector `|n|=1`:

```text
one chiral zero mode,
lambda_1^2 * L^2 = 2.
```

Lean module:

```text
P0EFTJanusMonopoleDiracSpectrum.lean
```

Primary spectral/index anchors:

- Brian P. Dolan, *The Spectrum of the Dirac Operator on Coset Spaces with
  Homogeneous Gauge Fields*, arXiv:hep-th/0304037;
- Rogelio Jante and Bernd Schroers, *Dirac operators on the Taub-NUT space,
  monopoles and SU(2) representations*, arXiv:1312.4879;
- A. A. Abrikosov Jr., *Dirac operator on the Riemann sphere*,
  arXiv:hep-th/0212134.

The Lean branch proves the finite arithmetic consequences of the spectral
formula.  Construction of the SpinC bundle, self-adjoint operator, compact
resolvent and spectrum remains an explicit operator-theorem target.

## 2. Product with the compact circle

For a product Dirac operator, every nonzero sphere eigenvalue produces paired
three-dimensional branches

```text
+sqrt(lambda^2 + p^2),
-sqrt(lambda^2 + p^2).
```

Their contribution to spectral asymmetry cancels exactly.  Therefore the eta
invariant is carried by the monopole zero modes and their one-dimensional
circle tower.

Lean module:

```text
P0EFTJanusProductDiracPairing.lean
```

The exact operator product formula, domains and multiplicities remain to be
formalized analytically.

## 3. Circle holonomy, eta and determinant

Let `a` be the fractional circle holonomy in the domain `0<a<1`.  For a Dirac
index `n`, the zero-mode tower gives the Hurwitz-zeta eta formula

```text
eta_zero(a) = n * (1 - 2*a).
```

PT acts as

```text
a -> 1-a,
```

and hence

```text
eta_zero(1-a) = -eta_zero(a).
```

At half holonomy:

```text
a = 1/2,
eta_zero = 0,
PT(a) = a.
```

The zeta-regularized magnitude of the one-dimensional zero-mode determinant is

```text
D0(a) = 2*sin(pi*a).
```

Its maximum amplitude is reached at `a=1/2`, where `D0=2`.  This makes half
holonomy a concrete PT-symmetric, eta-neutral vacuum candidate.

Lean module:

```text
P0EFTJanusCircleHolonomyEta.lean
```

The complete physical statement still requires the nonzero-mode determinant,
local counterterms and a proof that the full effective action—not only the
zero-mode factor—is globally minimized at half holonomy.

Eta/determinant and anomaly anchors:

- X. Dai and D. Freed, *Eta-Invariants and Determinant Lines*,
  arXiv:hep-th/9405012;
- E. Witten, *The Parity Anomaly On An Unorientable Manifold*,
  arXiv:1605.02391;
- M. F. Lapa, *A note on the parity anomaly from the Hamiltonian point of
  view*, arXiv:1903.06719.

## 4. Primitive spectral geometry lock

Use the product metric convention

```text
Sigma = S2_L x S1_(L*T),
circle radius R1 = L*T/(2*pi).
```

For a primitive monopole:

```text
sphere first nonzero Dirac gap:
  lambda_S2^2 * L^2 = 2.
```

At half holonomy, the smallest circle momentum has

```text
lambda_S1^2 * L^2 * T^2 = pi^2.
```

A Dirac spectral-isotropy condition

```text
lambda_S2^2 = lambda_S1^2
```

then gives

```text
2*T^2 = pi^2.
```

Therefore

```text
8*R1^2 = L^2,
R1/L = 1/(2*sqrt(2)).
```

This ratio belongs to the compact circle radius, not to the exact-solution
length `A`.

## 5. LL normalization and the corrected alpha identification

The LL auxiliary metric analysis supplies the normalization

```text
q_LL = lambda_S2^2 / 8.
```

For the primitive sphere gap:

```text
q_LL * L^2 = 1/4.
```

The positive primitive flux law is

```text
16*q_LL^2*A^4 = 1,
```

or equivalently

```text
4*q_LL*A^2 = 1.
```

Combining the two relations gives

```text
A = L.
```

Thus the consistent radius assignment is

```text
A = sphere throat radius L,
R1/L = 1/(2*sqrt(2)).
```

The earlier scalar-mode interpretation

```text
A/L = 1/(2*sqrt(2))
```

cannot refer to the same sphere radius, because it contradicts `A=L` at
positive radius.  The factor is reinterpreted as the compact-circle/sphere
ratio.

Lean modules:

```text
P0EFTJanusDiracSpectralGeometryLock.lean
P0EFTJanusSpectralRatioCorrection.lean
```

## 6. Bimetric matching selects the primitive monopole

For general monopole magnitude `m`, the sphere gap is

```text
lambda_1^2 * L^2 = m + 1.
```

With the same one-eighth charge normalization and primitive LL flux, the radius
relation is

```text
A/L = sqrt(2/(m+1)).
```

Therefore

```text
A=L  iff  m=1
```

inside the positive spectral/LL branch.

This is a major structural result:

- topology says the least nonzero monopole sector is primitive;
- the Dirac index says it has one chiral zero mode;
- the bimetric radius match independently selects the same primitive magnitude.

Lean module:

```text
P0EFTJanusDiracBimetricPrimitiveSelection.lean
```

## 7. Parity anomaly from the primitive index

In the doubled Chern-Simons-level convention, the induced shift is the Dirac
index.  The primitive PT pair carries

```text
positive fold: +1,
negative fold: -1,
total: 0.
```

Each fold corresponds to a half-integral level before doubling, while the total
paired theory is anomaly neutral.

Lean module:

```text
P0EFTJanusIndexParityAnomaly.lean
```

A complete proof must derive the regulator, Pin eta phase and global gauge
invariance of the paired determinant.

## 8. Absolute-scale no-go remains

The equations are invariant under

```text
L -> s*L,
A -> s*A,
q_LL -> q_LL/s^2,
lambda^2 -> lambda^2/s^2,
T and a unchanged.
```

Therefore the Dirac spectrum fixes:

- discrete sectors;
- holonomy;
- eta phase;
- dimensionless modulus;
- radius ratios;
- the equality `A=L`.

It still does not fix the common absolute length.  A quantum transmutation
scale, a normalized bulk/boundary charge or a gravitational Hamiltonian law
must break the rescaling orbit.

Lean module:

```text
P0EFTJanusDiracScaleOrbitNoGo.lean
```

## 9. Current theorem matrix

| Claim | Status |
| --- | --- |
| monopole spectral arithmetic | proved from explicit formula |
| primitive sector has one zero mode | proved algebraically |
| first primitive gap is `2/L^2` | proved algebraically |
| nonzero product branches pair | proved algebraically |
| zero-mode eta is PT odd | proved |
| half holonomy is eta neutral | proved |
| zero-mode determinant amplitude maximal at half | proved |
| `2*T^2=pi^2` under Dirac isotropy | proved conditionally |
| `8*R1^2=L^2` | proved conditionally |
| `A=L` under one-eighth LL lock | proved conditionally |
| bimetric `A=L` selects `m=1` | proved conditionally |
| PT-paired half-level anomaly cancellation | proved arithmetically |
| absolute metric scale | open |
| full determinant vacuum uniqueness | open |
| actual SpinC/Dirac operator construction in Lean | open |

## 10. Next deepest targets

1. Construct the monopole line bundle and twisted SpinC Dirac operator using
   concrete differential-geometric objects.
2. Prove the explicit spectrum and index in the formal environment.
3. Construct the product operator on `S2 x S1` and prove that eta reduces to the
   zero-mode tower.
4. Compute the complete zeta determinant, including nonzero modes and local
   counterterms.
5. Derive the one-eighth LL normalization from the operator/auxiliary metric,
   rather than importing it as an interface law.
6. Couple the determinant line to the Pin-lifted mapping-torus monodromy.
7. Identify a dimensionful renormalization or boundary-charge law that breaks
   the remaining common scale orbit.

## Honest conclusion

The Dirac program does more than add another spectral ansatz.  It corrects the
geometric interpretation of the previous ratio, explains why the primitive
monopole is singled out simultaneously by topology and bimetric matching, and
reduces the parity anomaly to the single chiral zero mode per fold.

The remaining hard problem is now sharply isolated: construct and regularize
the actual twisted Dirac determinant on the Janus throat, then determine whether
its renormalized scale can be fixed by the global geometry without importing an
observed cosmological length.
