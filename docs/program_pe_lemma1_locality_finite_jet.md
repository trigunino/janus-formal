# Program P.E — Lemma 1: locality and regularity imply locally finite-jet dependence

> Parent proof architecture: [`program_pe_jet_universality_proof.md`](program_pe_jet_universality_proof.md)  
> Next step: [`program_pe_lemma2_naturality_equivariance.md`](program_pe_lemma2_naturality_equivariance.md)

## Status

This document records the analytic proof used by Program P.E-J. It is the
Peetre--Slovak reduction from a regular local operator to a smooth finite-jet
evaluator.

The result is **local in the infinite-jet space**. It does not, by itself, give
one finite order valid on every configuration. It also does not assert
polynomial dependence, naturality, ellipticity or variationality.

The proof below is a written mathematical proof, following the Whitney-extension
argument in Navarro--Sancho. It is not presently a Lean-kernel formalization of
Whitney's theorem or of the full Peetre--Slovak theorem.

## Setting

Let

```text
E -> M,
F -> M
```

be smooth finite-dimensional fibre bundles. Write `Gamma(U,E)` and
`Gamma(U,F)` for their smooth sections over an open set `U subset M`.
Suppose that for every open `U` there is a map

```text
D_U : Gamma(U,E) -> Gamma(U,F).
```

We impose two hypotheses.

### Locality

For every inclusion `V subset U`,

```text
D_U(s)|_V = D_V(s|_V).
```

Equivalently, `D` is a morphism of sheaves of smooth sections. In particular,
`D(s)(x)` depends on the germ of `s` at `x`.

### Parametric regularity

Let `T` be any finite-dimensional smooth parameter manifold. If

```text
(t,x) |-> s_t(x)
```

is a smooth family of local sections of `E`, then

```text
(t,x) |-> D(s_t)(x)
```

is a smooth family of local sections of `F`.

This is the regularity hypothesis used in the nonlinear Peetre--Slovak theorem.

## Precise statement

For a local section `s`, define formally

```text
P_D(j_x^infinity s) := D(s)(x).
```

The first part of the proof shows that this is well-defined.

> **Lemma 1 — local finite-jet reduction.** For every
>
> ```text
> theta_0 = j^infinity_{x_0} s_0 in J^infinity E,
> ```
>
> there exist an integer `r >= 0`, a neighbourhood `V` of `theta_0` in
> `J^infinity E`, a neighbourhood `W` of `j^r_{x_0}s_0` in `J^r E`, and a
> smooth bundle map
>
> ```text
> d_r : W -> F
> ```
>
> such that, after shrinking `V` inside `pi_r^{-1}(W)`,
>
> ```text
> P_D(theta) = d_r(pi_r(theta))
> ```
>
> for every `theta in V`.

Equivalently, locally around `theta_0`,

```text
D(s)(x) = d_r(j_x^r s),
```

and therefore

```text
j_x^r s = j_x^r t
  =>
D(s)(x) = D(t)(x)
```

whenever the two infinite jets lie in the chosen neighbourhood.

## Proof

### 1. Locality makes the infinite-jet evaluator well-defined

Assume

```text
j_x^infinity s = j_x^infinity t.
```

The claim is local, so choose bundle charts in which `x=0`, the base is an open
subset of `R^n`, and the source and target bundles are trivial. The difference
`s-t` is flat at the origin.

Choose two closed truncated cones `K_+` and `K_-` meeting only at the origin and
having the origin in the closure of their interiors. Prescribe a formal Whitney
field which equals the full Taylor field of `s` on `K_+` and that of `t` on
`K_-`. The equality of the infinite jets at the origin is exactly the
compatibility condition needed across the two cones. Whitney's extension
theorem therefore gives a smooth section `u` such that

```text
u = s on K_+,
u = t on K_-.
```

On the interiors of the cones, locality gives

```text
D(u) = D(s) on int(K_+),
D(u) = D(t) on int(K_-).
```

All three outputs are smooth, hence continuous. Letting points tend to the
origin through the two cone interiors yields

```text
D(s)(0) = D(u)(0) = D(t)(0).
```

Thus

```text
j_x^infinity s = j_x^infinity t
  =>
D(s)(x) = D(t)(x),
```

so

```text
P_D : J^infinity E -> F,
P_D(j_x^infinity s) = D(s)(x)
```

is a well-defined map of sets over `M`.

### 2. Diagonal stabilization lemma

We need the following consequence of locality and smoothness.

> **Diagonal lemma.** Let `x_k -> x` and let `s,t` be two fixed smooth
> sections. If
>
> ```text
> j_{x_k}^k s = j_{x_k}^k t
> ```
>
> for every `k`, then
>
> ```text
> D(s)(x_k) = D(t)(x_k)
> ```
>
> for all sufficiently large `k`.

#### Proof of the diagonal lemma

Suppose, after passing to a subsequence, that the two values are different for
every `k`. Work in a target chart and choose points `y_k`, arbitrarily close to
`x_k`, such that all `x_k` and `y_k` are pairwise distinct and

```text
||D(s)(x_k) - D(t)(y_k)||
  > k ||x_k-y_k||.
```

This is possible because `D(t)` is continuous and the difference at `x_k` is
nonzero.

For every fixed derivative order `m`, the equality of the `k`-jets implies
agreement of all derivatives through order `m` once `k >= m`. By continuity,
`s` and `t` also have the same infinite jet at the limit point `x`. After
choosing each `y_k` sufficiently close to `x_k`, the prescribed fields

```text
j_{x_k}^infinity s,
j_{y_k}^infinity t,
j_x^infinity s = j_x^infinity t
```

satisfy the Whitney compatibility conditions on the compact set

```text
{x} union {x_k : k>=1} union {y_k : k>=1}.
```

Whitney extension gives one smooth section `w` with those prescribed infinite
jets. Step 1 then gives

```text
D(w)(x_k) = D(s)(x_k),
D(w)(y_k) = D(t)(y_k).
```

Consequently,

```text
||D(w)(x_k)-D(w)(y_k)|| / ||x_k-y_k|| > k.
```

But `D(w)` is smooth. Its derivative is bounded on a sufficiently small compact
neighbourhood of `x`, so the displayed difference quotients must remain bounded.
This contradiction proves the diagonal lemma.

### 3. Assume that no finite order works near one infinite jet

Fix

```text
theta_0 = j^infinity_{x_0}s_0.
```

The problem is local. After choosing coordinates, translating the base point,
and subtracting the reference section in a local trivialization, it is enough to
work with

```text
M = R^n,
x_0 = 0,
s_0 = 0.
```

For each positive integer `k`, let `U_k` be the cylindrical neighbourhood of the
zero infinite jet defined by

```text
U_k = {
  j_x^infinity f :
  ||x|| <= 2^{-k},
  |partial^alpha f^a(x)| <= (2^{-k})^k
  for |alpha| <= k
}.
```

Suppose that `P_D` does not factor through any finite jet space on any
neighbourhood of `theta_0`. Then for every `k` there are two infinite jets in
`U_k`, based at the same point `x_k`, represented by sections `f^k,h^k`, such
that

```text
j_{x_k}^k f^k = j_{x_k}^k h^k,
```

but

```text
D(f^k)(x_k) != D(h^k)(x_k).
```

The shrinking bounds imply `x_k -> 0`, and every fixed derivative of the chosen
jets tends to zero faster than any prescribed power of `2^{-k}`.

### 4. Separate the counterexamples by one extra parameter

The points `x_k` may be badly placed for a simultaneous Whitney extension.
Introduce a real parameter and set

```text
z_k = (2^{-k},x_k) in R x R^n.
```

Then `z_k -> (0,0)` and the first coordinate gives the separation estimate

```text
||z_k||, ||z_l|| < 4 ||z_k-z_l||
```

for `k != l`, after an inessential adjustment of constants.

Regard each `f^k` and `h^k` as a family constant in the new parameter. At `z_k`
prescribe the full jet of that constant family, and prescribe the zero jet at
`(0,0)`. Thus all derivatives involving the parameter vanish, while the spatial
derivatives are those of `f^k` or `h^k` at `x_k`.

For every fixed multi-index `alpha` and every integer `m`, sufficiently large
`k` gives

```text
|partial^alpha f^k(x_k)| <= (2^{-k})^k
                         <= (2^{-k})^{k-m} ||z_k||^m,
```

and the same estimate for `h^k`. Since `(2^{-k})^{k-m} -> 0`, these prescribed
jets are flat to arbitrary order at the limit point. Together with the
separation estimate, this is the Whitney compatibility condition. Finite
initial portions of the sequence do not affect it.

Whitney extension therefore produces two smooth families

```text
F,H : R x R^n -> R^q
```

such that for every `k`,

```text
j_{z_k}^infinity F
  = j_{z_k}^infinity(constant family f^k),

j_{z_k}^infinity H
  = j_{z_k}^infinity(constant family h^k).
```

In particular,

```text
j_{z_k}^k F = j_{z_k}^k H.
```

### 5. Regularity gives the contradiction

For a smooth family `A(t,x)`, write `A_t(x)=A(t,x)` and define

```text
D_R(A)(t,x) := D(A_t)(x).
```

Parametric regularity says that `D_R(A)` is smooth. Locality of `D` says that
`D_R` commutes with restrictions. Hence `D_R` is itself a morphism of sheaves on
`R x M`, to which Steps 1 and 2 apply.

Because the infinite jets of `F` and the constant family `f^k` agree at `z_k`,
Step 1 gives

```text
D_R(F)(z_k) = D(f^k)(x_k).
```

Similarly,

```text
D_R(H)(z_k) = D(h^k)(x_k).
```

The values on the right are different for every `k`, whereas

```text
j_{z_k}^k F = j_{z_k}^k H.
```

The diagonal lemma applied to `D_R` says that the two outputs must agree for all
sufficiently large `k`. This contradiction proves that some finite order `r`
does work on a neighbourhood of `theta_0`.

Thus, after shrinking the neighbourhood if necessary,

```text
P_D = d_r o pi_r
```

for a set map `d_r` on the corresponding finite-jet neighbourhood.

### 6. The finite-jet evaluator is smooth

It remains to prove smoothness of `d_r`.

In local coordinates, write a finite jet as

```text
q = (x,u_alpha)_{|alpha|<=r}.
```

Represent `q` by its Taylor polynomial centred at `x`,

```text
xi_q(y) = sum_{|alpha|<=r}
            u_alpha/alpha! (y-x)^alpha,
```

using a fixed cutoff if a compactly supported local representative is needed.
The map

```text
(q,y) |-> xi_q(y)
```

is a smooth finite-dimensional family of sections. Parametric regularity gives
smoothness of

```text
(q,y) |-> D(xi_q)(y).
```

On the finite-jet neighbourhood where factorization has been established,

```text
d_r(q) = D(xi_q)(x).
```

Evaluation along the smooth diagonal `(q |-> (q,x))` therefore proves that
`d_r` is smooth.

This completes the proof:

```text
locality + parametric regularity
  =>
locally finite-jet dependence with a smooth evaluator.
```

## Exact scope of the conclusion

### The order is locally finite, not automatically globally uniform

The integer

```text
r = r(theta_0)
```

may vary with the infinite jet. A single global order requires an additional
compactness or boundedness argument. For example, on a compact subset of the
relevant infinite-jet image, choose finitely many factorization neighbourhoods,
lift all lower-order evaluators to the maximum order by jet truncation, and take
that maximum.

An unbounded configuration space need not admit such a finite subcover.

### Naturality is not used here

Lemma 1 needs locality and regularity only. Naturality enters in Lemma 2, where
the finite-jet evaluator is shown to be equivariant under a sufficiently high
adapted jet symmetry group.

### Smooth does not mean polynomial

The theorem produces a smooth evaluator. Polynomiality, rationality or a
classification by a finite list of polynomial curvature expressions requires
extra hypotheses.

### Ellipticity and variationality remain independent

Finite differential order does not imply ellipticity, formal self-adjointness,
Helmholtz integrability, anomaly cancellation or physical selection of the
operator.

## Janus specialization

For unconstrained smooth metric and matter fields, the source can be taken as an
open subbundle of a finite-dimensional tensor bundle. In particular, Lorentzian
metrics form an open subbundle of the bundle of symmetric two-tensors, so the
local bundle argument applies to operators defined on all such smooth fields.

If an operator is defined only on a constrained solution space, for example
only on Einstein solutions or only on a reduced FLRW ansatz, the required local
Whitney extension property is not automatic. One must prove an extensibility
result for that domain before invoking this lemma.

For the full decorated Janus category, the remaining specialization tasks are:

1. define the actual source and target sheaves;
2. prove restriction locality;
3. prove parametric regularity;
4. prove any domain-extensibility condition imposed by the constraints;
5. identify a bounded jet region if one uniform order is claimed.

## Lean correspondence

The current Lean files deliberately begin **after** the analytic reduction. They
record the Peetre--Slovak hypotheses and the resulting finite-jet presentation
as explicit fields, then prove the algebraic naturality/equivariance and
uniqueness statements.

Relevant files:

```text
JanusFormal/Branches/FundamentalGeometryPEJetUniversality.lean
JanusFormal/Branches/FundamentalGeometryPEJetUniversality/Gates/
  P0EFTJanusCorrectedJetUniversality.lean
  P0EFTJanusFiniteJetEquivariance.lean
  P0EFTJanusFiniteOrderUniformization.lean
```

Formalizing this document inside Lean would additionally require a suitable
smooth jet-bundle library, Whitney extension, smooth families of sections, and
the sheaf-theoretic Peetre--Slovak argument.

## Evidence classification

| Statement | Status |
| --- | --- |
| infinite jets determine the value of a local sheaf morphism | analytic theorem proved here via Whitney gluing |
| diagonal stabilization | analytic theorem proved here via Whitney extension |
| regular local operator has locally finite order | analytic theorem proved here via the parameter-separation argument |
| finite-jet evaluator is smooth | analytic theorem proved here via the universal polynomial family |
| one global uniform order | conditional on compactness/bounded finite-cover control |
| Lean-kernel proof of Whitney/Peetre--Slovak | open |
| Janus-specific locality and regularity verification | open |
| naturality/equivariance and evaluator uniqueness after factorization | proved in the existing Lean action model |

## References

- J. Navarro and J. B. Sancho, *Peetre--Slovak's theorem revisited*, arXiv:1411.7499. In particular: Proposition 2.2, Proposition 2.3, Definition 2.2, Lemma 2.6 and Theorem 4.1.
- I. Kolar, P. W. Michor and J. Slovak, *Natural Operations in Differential Geometry*.
