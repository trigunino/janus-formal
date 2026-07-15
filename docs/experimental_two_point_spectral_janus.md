# Experimental two-point spectral Janus seed

## Isolation

This experiment is not imported by `JanusFormal.lean`, P-E, Program P, or the
nonlinear bimetric program.  It must not be reported as a Janus closure result.

Lean entry:

```text
JanusFormal/Experimental/TwoPointSpectralJanus.lean
```

Isolated A/B bridge:

```text
JanusFormal/Experimental/TwoPointSpectralBimetricBridge.lean
```

Isolated nonlinear audit:

```text
JanusFormal/Experimental/TwoPointSpectralNonlinearBimetricAudit.lean
```

Higher-invariant audit:

```text
JanusFormal/Experimental/TwoPointSpectralHigherInvariantAudit.lean
```

Affine fluctuating-link audit:

```text
JanusFormal/Experimental/TwoPointSpectralFluctuatingLinkAudit.lean
```

Quadratic-link finite-jet bridge:

```text
JanusFormal/Experimental/TwoPointSpectralQuadraticLinkJet.lean
```

## Minimal seed

The internal algebra is the two-point algebra

```text
A_F = R plus R.
```

Its elements act diagonally, while one odd finite Dirac operator links the two
components:

```text
pi(a_plus,a_minus) = diag(a_plus,a_minus),
D_F(m)              = [[0,m],[m,0]],
Gamma                = diag(1,-1).
```

The formalization proves

```text
Gamma D_F + D_F Gamma = 0
```

and computes the spectral commutator exactly:

```text
1/2 ||[D_F,pi(a_plus,a_minus)]||_F^2
  = m^2 (a_plus-a_minus)^2.
```

Thus one off-diagonal geometric operator genuinely produces an
exchange-symmetric reciprocal coupling between the sheets.

## Derived reduced equations

The scalar Euler coefficients are

```text
E_plus  =  2 m^2 (a_plus-a_minus),
E_minus = -2 m^2 (a_plus-a_minus).
```

They satisfy the diagonal Noether identity

```text
E_plus + E_minus = 0.
```

For `m != 0`, simultaneous stationarity selects

```text
a_plus = a_minus.
```

## Result and limitation

The experiment succeeds at generating the shape of a cross interaction from a
single two-point link operator.  It also proves that the geometry does not fix
the link magnitude: different values of `m^2` give distinct actions with the
same exchange symmetry.

This is only a finite scalar internal model.  It does not yet contain:

- Lorentzian metrics on `M`;
- spinor bundles or a spacetime Dirac operator;
- the spectral action and heat-kernel expansion;
- determinant-weighted M15 matter sources;
- a Boulware--Deser constraint analysis;
- a derivation of the link scale.

The next admissible experiment is to tensor this finite seed with a fixed
spacetime Dirac geometry and derive the block curvature/action before making
any Janus identification.

## Isolated compatibility bridge

The companion bridge proves, without adding an assumption, that

```text
spectralLinkAction m h_plus h_minus
  = relativeModePotential (m^2) h_plus h_minus.
```

It also propagates the physical massive eigenvalue through unequal kinetic
weights.  Two further identifications are deliberately assumptions rather than
closure claims:

```text
m^2 = fpMassCombination(beta) = 2 (beta1+beta2),
m   = c_m v.
```

Under both assumptions the bridge gives the target

```text
c_m^2 v^2 = 2 (beta1+beta2).
```

Thus the exact result is compatibility of the quadratic shapes.  Deriving the
normalization `c_m`, the link scale, or the full nonlinear bimetric potential
remains outside this experiment.

## Nonlinear completion audit

Around the symmetric point `c=1+x`, the full PT-flat proportional interaction
has the exact expansion

```text
12 (beta1+beta2) x^2
+ 12 (beta1+beta2) x^3
+ (4 beta1+3 beta2) x^4.
```

Choosing `m^2=12(beta1+beta2)` therefore matches the quadratic Hessian, but the
minimal spectral link leaves the displayed cubic and quartic residual.  The
Lean audit proves a stronger no-go: if one constant two-point link is required
to equal the complete PT-flat interaction for every proportional ratio `c`,
then necessarily

```text
m^2 = beta1 = beta2 = 0.
```

Consequently the minimal commutator seed cannot by itself generate the full
nonlinear bimetric potential.  A successful completion needs extra finite
spectral data, a field-dependent link, or higher spectral invariants; none of
these extensions is assumed here.

## Higher even invariants

The first natural extension was tested explicitly:

```text
S_even(x) = q x^2 + r x^4.
```

It cannot reproduce the safe PT-flat interaction.  Its odd part under
`x -> -x` vanishes, whereas the bimetric target has odd part

```text
24 (beta1+beta2) x^3.
```

Lean proves that global equality forces `beta1+beta2=0`, i.e. a vanishing
Fierz--Pauli combination.  This contradicts the selected safe cone
`beta1>0`, `beta2>=0`.  Merely adding ordinary even spectral invariants is
therefore insufficient: a viable nonlinear completion must explain the cubic
term through richer finite geometry, background/measure dependence, or a
nonconstant fluctuated link.

## Affine fluctuating link

The smallest field-dependent candidate,

```text
m(x) = m0 (1+a x),
S(x) = m(x)^2 x^2,
```

does generate a cubic term.  Matching the quadratic and cubic coefficients of
B fixes `a=1/2`.  The resulting quartic coefficient then matches B only when
`beta1=0`.  Lean therefore proves that no affine fluctuating link reproduces
the complete target on the safe cone `beta1>0`, `beta2>=0`.

This narrows the next admissible construction: the link must fluctuate
nonlinearly, or its action must include an independently derived measure or
curvature factor.  Merely allowing the single link to vary affinely is not
enough.

## Quadratic fluctuating link and fourth-order jet

For

```text
m(x) = m0 (1 + a x + b x^2),
```

coefficient matching through fourth order has the unique solution

```text
m0^2 = 12 (beta1+beta2),
a     = 1/2,
b     = beta1 / (24 (beta1+beta2)).
```

Lean proves the exact identity

```text
S_link(x) = V_B(x)
          + (beta1/2) x^5
          + beta1^2/[48(beta1+beta2)] x^6.
```

Thus the fourth-order jet of the nonlinear bimetric potential is reproduced
exactly.  On the safe cone the fifth-order obstruction is strictly positive,
so this is a local finite-jet bridge rather than a global completion.  The
coefficient `b` is currently inferred by matching; it still needs an
independent geometric derivation before it can be interpreted physically.
