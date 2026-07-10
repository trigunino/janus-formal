# RP4 Orientation-Twisted Four-Form Alpha Attempt

## Status

Experimental research branch.  It closes one missing mathematical component:
the primitive signed flux sector.  It does **not** yet close a no-fit value of
the Janus scale.

## 1. Normalize the target before solving it

The published exact expansion solution uses

```text
a(u) = alpha_squared * cosh(u)^2
alpha_squared = -(8 pi G / (3 c^2)) E_global
E_global = a_plus^3 rho_plus + a_minus^3 rho_minus = constant < 0
```

Here `alpha_squared` is the positive length appearing as the minimum of the
published scale factor.  This branch therefore targets

```text
alpha_squared / L_projective
```

and does not silently identify source `alpha^2` with a differently normalized
repo variable called `alpha`.

Source: D'Agostini--Petit 2018, Appendix A, Eqs. 9--11,
DOI `10.1007/s10509-018-3365-3`.

## 2. Topological correction: the flux must be twisted

`RP4` is non-orientable.  Consequently, an ordinary real top-degree form is not
the right global flux object.  The correct object is a degree-four differential
cocycle valued in the orientation local system:

```text
F4_twisted in H^4(RP4; Z_orientation)
```

Twisted Poincare duality gives the integer lattice

```text
H^4(RP4; Z_orientation) ~= Z.
```

On the orientation double cover `S4 -> RP4`, the field becomes an ordinary
four-form satisfying antipodal anti-invariance:

```text
tau^* F4_cover = -F4_cover.
```

Its signed sector is an integer `n`, and PT sends

```text
n -> -n.
```

This differs from an ordinary top-degree de Rham flux, which would miss the
non-orientable global class.

General differential-twist reference: Bunke--Nikolaus,
*Twisted differential cohomology*, arXiv:1406.3231.

## 3. Pin sign correction

For real projective space,

```text
w(T RP^n) = (1 + a)^(n+1).
```

For `n = 4` this gives

```text
w1 = a,
w2 = choose(5,2) a^2 = 0 mod 2,
w1^2 = a^2 != 0.
```

Hence the global `RP4` topology admits `Pin+` and does not admit `Pin-`:

```text
Pin+ obstruction: w2 = 0                -- satisfied
Pin- obstruction: w2 + w1^2 = 0         -- not satisfied
```

`Pin-` remains relevant to the two-dimensional `RP2`/Boy-surface shadow, but it
must not be transported unchanged to global `RP4`.  Witten's treatment of
unorientable four-dimensional fermion systems likewise uses `Pin+` for the
`T^2 = (-1)^F` case: arXiv:1508.04715.

## 4. Primitive sector theorem now proved in Lean

Suppose the boundary/anomaly law selects the non-trivial mod-two class and the
fixed-flux action selects the least magnitude in that class.  Algebraically:

```text
|n| mod 2 = 1
|n| <= m for every odd natural m
```

Then necessarily

```text
|n| = 1.
```

The file

```text
JanusFormal/Branches/RP4TwistedFourFormAlpha/Gates/
  P0EFTJanusRP4TwistedFluxPrimitiveSelector.lean
```

proves this theorem, together with

```text
PT(PT(n)) = n
|PT(n)| = |n|
PT(n)^2 = n^2.
```

This removes the old logical gap between “integer flux exists” and “the
primitive nonzero sector is selected,” provided a Janus law really enforces the
non-trivial mod-two class and least-action condition.

## 5. Conditional radius law

Let the round quotient volume be

```text
Vol(RP4_L) = v L^4,
v = 4 pi^2 / 3.
```

For fixed twisted flux

```text
integral^twisted F4 = n q,
f = n q / (v L^4),
```

an Einstein/fixed-flux balance of the convention

```text
3/L^2 = (kappa/2) f^2
```

reduces algebraically to

```text
L^6 = kappa (n q)^2 / (6 v^2).
```

With `kappa = 8 pi G` and the round `RP4` volume coefficient, this becomes

```text
L^6 = 3 G (n q)^2 / (4 pi^3).
```

The Lean branch proves the generic algebraic sixth-power law once the balance
and its sign are supplied.  It does not yet claim that this is the correct
Janus Euclidean action or ensemble.

## 6. New obstruction: a standard four-form is vacuum-like, not Janus dust

The published Janus constant is

```text
E_global = a^3 rho_total = constant.
```

A standard four-form kinetic sector has a constant vacuum-like density.  For a
constant density `rho_F`, its comoving energy obeys

```text
E_F(s a) = s^3 E_F(a).
```

Therefore a standard Brown--Teitelboim vacuum four-form cannot be identified
directly with the published dust-like `E_global` on a non-static branch.  The
Lean file

```text
P0EFTJanusRP4FourFormScaleAudit.lean
```

proves this scaling obstruction.

This is the most important outcome of the attempt: the old four-form candidate
was underspecified.  It can quantize a cosmological/vacuum term, but it does not
by itself fix the integration constant in Eq. 9 of the published dust solution.

## 7. Remaining viable bridge

The four-form must be used as a **global canonical/boundary charge**, not simply
inserted as a vacuum density.  A complete route would have to derive

```text
orientation-twisted differential cocycle
  -> integer charge n
  -> PT/anomaly rule selecting odd sector
  -> fixed-charge action selecting |n| = 1
  -> Janus-derived charge unit q_J
  -> boundary Hamiltonian or moment map E_global(Q)
  -> alpha_squared = -(8 pi G / (3 c^2)) E_global
  -> Lorentzian continuation and projective-radius matching.
```

The new branch closes the integer and primitive-selection algebra.  The hard
atoms are now reduced to:

1. derive the `Pin+` anomaly/boundary condition that forces the non-trivial
   mod-two sector;
2. derive the dimensionful Janus charge unit `q_J`;
3. derive a fixed-charge boundary Hamiltonian mapping the twisted charge to the
   dust-like `E_global` rather than to a vacuum density;
4. derive the Euclidean-to-Lorentzian matching that compares `alpha_squared`
   with `L_projective`.

## 8. Honest verdict

```text
orientation-twisted integer lattice: closed mathematically
PT pair n <-> -n: closed mathematically
odd + least magnitude => |n| = 1: closed in Lean
conditional L^6 law: closed algebraically
Janus charge unit: open
map to published dust E_global: open, with a proved standard-four-form mismatch
alpha_squared/L no-fit value: not yet closed
```

This is progress rather than a final value: it fixes the global topological
object, corrects the Pin sign, closes the primitive integer sector, and exposes
the precise dynamical law that must still be constructed.
