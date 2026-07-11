# Program D Track Conclusion — Primitive Monopole, Z4 Holonomy and Dirac Spectrum

## Question

Can the canonical Janus throat

```text
Sigma = S2_L x S1_(L*T)
```

produce the LL charge normalization and the exact-solution/geometric radius
relation from a primitive monopole and a fermionic order-four monodromy?

## Inputs kept explicit

1. primitive monopole sector `|n|=1` on `S2`;
2. a global Pin lift whose circle holonomy is one quarter;
3. unweighted spectral modulus `T^2=2*pi^2`;
4. separated product Dirac spectrum;
5. PT-related folds carry opposite eta-odd data but equal even squared gaps;
6. the parity-even LL charge is the sum of the two squared gaps;
7. primitive LL flux obeys `16*q_LL^2*A^4=1`.

Items 1 and the finite algebra are theorem-level. Items 2–6 are named geometric
or analytic obligations.

## Exact algebraic spectrum

For sphere Landau level `k >= 0` and circle label `m in Z`, the normalized
squared-eigenvalue numerator is

```text
N(k,m) = 8*k*(k+1) + (4*m+1)^2.
```

The Lean branch proves

```text
N(k,m) >= 1,
N(k,m) = 1  iff  k=0 and m=0.
```

Therefore the model has one unique positive normalized gap.

## Quarter-holonomy gap

The first shifted circle momentum is

```text
p0 = pi/(2*L*T).
```

With `T^2=2*pi^2`,

```text
gap^2 * L^2 = 1/8.
```

## Eta pairing

The reduced circle eta model at quarter holonomy is

```text
eta_+(0)=+1/2,
eta_-(0)=-1/2.
```

Hence PT pairing gives

```text
eta_+ + eta_- = 0.
```

The parity-odd determinant phase cancels. The parity-even squared gaps do not
cancel; they add.

## Charge normalization

Assuming the physical even charge is

```text
q_LL = gap_+^2 + gap_-^2 = 2*gap^2,
```

one obtains

```text
q_LL * L^2 = 1/4.
```

The first nonconstant sphere squared gap satisfies

```text
lambda_S2 * L^2 = 2.
```

Therefore

```text
q_LL = lambda_S2 / 8.
```

The previously observed coefficient `1/8` is thus reproduced by the paired
Dirac-gap mechanism rather than inserted solely as a compatibility constant.

## Alpha/geometric-radius lock

Primitive LL flux gives

```text
16*q_LL^2*A^4=1.
```

Since `4*q_LL*L^2=1`, the same equation holds with `A` replaced by `L`.
Positivity then yields

```text
A=L.
```

## What this track establishes

| Statement | Status |
| --- | --- |
| primitive monopole integer sector | theorem/algebra |
| unique normalized Z4 spectral gap | theorem/algebra |
| eta cancellation under PT pairing | algebraic model; analytic eta proof open |
| charge coefficient `1/8` | conditional theorem |
| radius relation `A=L` | conditional theorem |
| absolute value of `L` | not derived |

## What would falsify the track

The track must be rejected or modified if any of the following occurs:

1. the global Pin lift does not produce quarter holonomy;
2. the actual SpinC Dirac spectrum differs from the separated model;
3. zeta/APS regularization does not give the paired eta cancellation;
4. the LL charge is not the parity-even sum of the two fold gaps;
5. the unweighted modulus is not selected by the effective action;
6. the required throat gauge bundle cannot be globally constructed.

## Final verdict

```text
RETAIN as the strongest Program-D compatibility mechanism.
DO NOT promote as an absolute-scale prediction.
```

The track successfully unifies four previously separate observations:

```text
fermionic Z4
+ primitive throat monopole
+ eta cancellation
+ LL coefficient 1/8
  -> A=L.
```

Its next stage is no longer additional algebra. It is the analytic construction
of the global SpinC/Pin Dirac operator, its complete spectrum, zeta determinant
and eta invariant. Even if that stage succeeds, a separate quantum or
gravitational law is still required to fix `L` in physical units.
