# Program P.D-G — Global natural pairings are modules over invariants

> Pointwise representation audit: [`program_pe_invariant_pairings.md`](program_pe_invariant_pairings.md)  
> Categorical jet correction: [`program_pe_categorical_jet_equivalence.md`](program_pe_categorical_jet_equivalence.md)

## Question

Suppose that at every fixed background jet the invariant bilinear pairing space

```text
Hom_(H_b)(E_i,b tensor E_j,b, R)
```

has dimension zero or one. Does this make the corresponding natural coupling
forbidden or unique up to one constant normalization?

## Verdict

The pointwise conclusion is correct, but the global conclusion is too strong.

> **Pointwise theorem.** At a fixed structured jet `b`, the isotropy group `H_b`
> controls the invariant bilinear forms on the field fibers. Dimension zero
> forbids a pairing at that jet; dimension one fixes its fiberwise shape up to a
> scalar.

> **Global correction.** Natural pairing families are equivariant sections over
> the structured-jet base. They form a module over the algebra of invariant
> scalar functions. Consequently, a one-dimensional pointwise pairing space does
> not imply one-dimensional global coupling space over the constant scalars.

This is a no-go result for the inference

```text
pointwise multiplicity one
  -> one constant global coefficient.
```

It does not invalidate the existing low-rank invariant-pairing calculations.
Those calculations remain the correct frozen-background input.

## 1. Structured-jet setting

Fix an order `R`. Let

```text
Gamma_R ==> B_R
```

be the structured jet groupoid of the decorated immersion geometry. Here `B_R`
contains admissible background jets and `Gamma_R` contains coordinate, frame and
gauge changes.

Let `E_i -> B_R` and `E_j -> B_R` be equivariant field bundles. For
`b in B_R`, write `H_b` for the isotropy group.

The pointwise invariant space is

```text
B_ij(b) = Hom_(H_b)(E_i,b tensor E_j,b, R).
```

A global natural pairing is not a choice in one fiber. It is a smooth
equivariant section

```text
beta in Gamma_Gamma_R(B_R, (E_i tensor E_j)^*).
```

Define

```text
I_R = C-infinity(B_R)^Gamma_R,
```

the algebra of invariant scalar functions, and

```text
B_ij,R = Gamma_Gamma_R(B_R, (E_i tensor E_j)^*),
```

the space of natural pairing families.

## 2. Module theorem

### Theorem D-G1 — demonstrated formally

`B_ij,R` is a module over `I_R`.

If `f` is an invariant scalar function and `beta` is an invariant pairing, then

```text
(f beta)_b(u,v) = f(b) beta_b(u,v)
```

is again an invariant pairing.

### Proof

For any groupoid arrow `gamma : b -> b'`, invariance gives

```text
f(b') = f(b)
```

and

```text
beta_b'(gamma u, gamma v) = beta_b(u,v).
```

Therefore

```text
(f beta)_b'(gamma u, gamma v)
  = f(b') beta_b'(gamma u, gamma v)
  = f(b) beta_b(u,v)
  = (f beta)_b(u,v).
```

The Lean gate

```text
P0EFTJanusInvariantCoefficientModule
  .scale_pairing_preserves_invariance
```

proves this algebraic statement in an abstract action model.

## 3. Explicit counterexample to constant global uniqueness

Take the background space

```text
B = Bool
```

with trivial symmetry, and the one-dimensional real field fiber. Let

```text
beta_b(x,y) = x y
```

for both background points. Every pointwise pairing space has the same
one-dimensional shape.

Now define the invariant scalar coefficient

```text
f(false) = 0,
f(true)  = 1
```

and the pairing family

```text
gamma_b = f(b) beta_b.
```

Both `beta` and `gamma` are invariant. There is no constant `c in R` such that

```text
gamma_b = c beta_b
```

for both values of `b`: evaluation at `false` forces `c=0`, while evaluation at
`true` forces `c=1`.

This is formalized by

```text
P0EFTJanusInvariantCoefficientModule
  .varying_pairing_is_not_one_constant_multiple
  .pointwise_shape_does_not_force_global_constant_scale
```

The example is finite and contains no analytic subtlety. It isolates the exact
logical gap.

## 4. Geometric form of the same freedom

If `beta_0` is a natural pairing and `I` is any natural scalar invariant, then

```text
F(I) beta_0
```

is another natural pairing for every admissible scalar function `F`.

Typical candidate invariants on an immersed background include

```text
|B|^2,
scalar curvature,
|F_twist|^2,
contractions of ambient curvature,
covariant derivatives of these tensors.
```

The existence and independence of any specific invariant must be proved in the
actual Janus category. The logical conclusion does not depend on a particular
choice: any nonconstant invariant scalar already enlarges the global coupling
module.

## 5. Isotropy stratification

The dimension of `B_ij(b)` need not be constant in `b`.

### Counterexample D-G2 — demonstrated

Let `Z2` act on the base line by

```text
x |-> -x.
```

Let the source fiber carry the sign representation and the target scalar be
trivial.

- At `x != 0`, the isotropy is trivial, so the pointwise equivariant Hom-space
  has dimension one.
- At `x = 0`, the isotropy is all of `Z2`, which acts by sign on the source, so
  the invariant Hom-space has dimension zero.

Thus invariant-space dimensions can jump across isotropy strata. A global
classification must prove smooth compatibility and extension between the
principal and singular strata; generic multiplicity computations alone do not
suffice.

## 6. What pointwise multiplicity one does prove

On a fixed orbit or at a fixed structured jet, if

```text
dim Hom_(H_b)(E_i,b tensor E_j,b, R) = 1,
```

then every invariant bilinear form at that jet is a scalar multiple of one
chosen generator.

This remains valuable for:

- principal symbols at a fixed background;
- Hessians linearized about one selected solution;
- homogeneous backgrounds with no nonconstant invariant scalar functions;
- calculations after freezing all background jets;
- polynomial or weighted subclasses whose coefficient ring has been fixed.

The statement must not be silently globalized.

## 7. Conditions that can recover a finite coefficient space

A finite-dimensional coupling space can follow after imposing additional data,
for example:

1. restrict to a single homogeneous orbit;
2. fix the background jet rather than varying it;
3. require polynomial dependence of bounded degree;
4. impose a prescribed differential order and engineering weight;
5. impose scale or conformal invariance;
6. quotient by field redefinitions and total divergences;
7. derive coefficients from a parent action or microscopic matching law;
8. fix a normalization at a critical background.

Each restriction is an extra theorem or modeling choice. None follows merely
from `dim Hom = 1`.

## 8. Corrected Program P.D statement

The defensible classification chain is

```text
structured jet b
  -> isotropy H_b
  -> pointwise invariant Hom-spaces
  -> isotropy-stratified equivariant bundle of pairings
  -> module over invariant scalar algebra
  -> degree/order/weight or parent-law restrictions
  -> finite residual coefficient space
  -> physical normalization.
```

Therefore Program P.D should report three distinct objects:

```text
fiber rank on each isotropy stratum,
invariant scalar coefficient algebra,
global equivariant pairing module.
```

Only the combination controls natural couplings.

## 9. Relation to Hessians and symbols

A principal symbol of order `k` at `b` belongs to

```text
Hom_(H_b)(Sym^k T_b^* tensor E_b, F_b).
```

Multiplicity one can make that leading symbol unique up to scale at a fixed
background. It does not fix lower-order terms, which can depend on curvature,
second fundamental form, gauge curvature and their derivatives.

Similarly, a pointwise one-dimensional Hessian pairing does not determine one
global Hessian family: invariant scalar coefficients and lower-order natural
terms remain unless further conditions eliminate them.

## 10. Evidence table

| Claim | Status |
| --- | --- |
| pointwise low-rank pairing dimensions | Lean/Python finite models already in repository |
| invariant pairings closed under invariant scalar multiplication | proved in new Lean action model |
| pointwise multiplicity one does not imply constant global scale | explicit Lean counterexample |
| actual invariant scalar algebra of Janus jets | open |
| isotropy stratification of structured Janus jets | open |
| smooth global equivariant pairing module | open |
| finite polynomial/weighted generator theorem | conditional on a jet-normal-form and invariant-theory theorem |
| physical normalization | open; requires parent/microscopic input |

## 11. Lean correspondence

```text
JanusFormal/Branches/FundamentalGeometryPEInvariantPairings/Gates/
  P0EFTJanusInvariantCoefficientModule.lean
```

The formal layer proves module closure and the finite counterexample. It does not
claim to construct `B_R`, `Gamma_R`, their smooth invariant algebra or the actual
Janus field bundles.

## 12. Next theorem queue

1. Construct the structured jet groupoid and its isotropy stratification.
2. Compute the scalar invariant algebra at the required jet order.
3. Compute equivariant pairing generators as a module over that algebra.
4. Prove extension across singular isotropy strata.
5. Impose order, weight, parity, ghost number and variational constraints.
6. Insert the resulting finite basis into the Helmholtz system.
7. Derive remaining normalizations from a parent action, anomaly-compatible
   regulator and microscopic matching law.
