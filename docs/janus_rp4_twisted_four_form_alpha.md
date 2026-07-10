# RP4 Twisted Flux, Finite PT Bridge and LL-Brane Alpha Scale

## Status

This branch has been pushed to the final **conditional** scale frontier.

It now closes:

```text
source-normalization audit
primitive twisted flux magnitude |n| = 1
whole-slice curvature no-go
finite-sphere bridge matching algebra
minimal LL-brane auxiliary invariant F^2 = 1/2
primitive LL flux radius law
charge/tension relation
conditional alpha_squared spectrum
```

It does **not** manufacture an absolute cosmological length.  The remaining
scale datum is one dimensionful world-volume charge normalization, together
with the derivation of the signed bimetric junction used by the finite-sphere
matching.

## 1. Keep the source variable unambiguous

D'Agostini--Petit 2018 writes

```text
a(u) = A cosh(u)^2
A = alpha^2 = -(8 pi G / (3 c^2)) E_global
E_global = a_plus^3 rho_plus + a_minus^3 rho_minus < 0.
```

Here `A = alphaSquaredLength` is a **positive length**.  It must not be silently
identified with another repo variable called `alpha` carrying a different
normalization.

Source: D'Agostini--Petit 2018, Appendix A, Eqs. 9--14,
DOI `10.1007/s10509-018-3365-3`.

## 2. Source-level factor-two audit

Direct differentiation of the printed parametric solution gives

```text
da/dt = c tanh(u)
d2a/dt2 = c^2 / (2 A cosh(u)^4)
a^2 d2a/dt2 = A c^2 / 2.
```

Using the printed Eq. 11 then gives

```text
a^2 d2a/dt2 = -(4 pi G / 3) E_global.
```

Thus the printed triplet Eq. 9--11 cannot all hold for a nonzero source if Eq. 9
contains `8 pi G/3`.  Eq. 10, Eq. 11 and the printed deceleration formula Eq. 13
are mutually consistent with `4 pi G/3`.

The branch does not silently repair the source.  It records the discrepancy in

```text
P0EFTJanusExactCoshNormalizationAudit.lean
scripts/audit_janus_exact_solution_normalization.py
```

and uses the explicit source scale law

```text
3 c^2 A = -8 pi G E_global
```

only where stated.

## 3. Global topology and Pin sign

Because `RP4` is non-orientable, the correct top-degree flux is orientation-
twisted:

```text
[F4] in H^4(RP4; Z_orientation) ~= Z.
```

On the orientation cover `S4 -> RP4`, it is represented by an ordinary
anti-invariant four-form:

```text
tau^* F4_cover = -F4_cover.
```

For `RP4`,

```text
w1 = a,
w2 = 0,
w1^2 != 0.
```

Therefore the global projective four-manifold is compatible with `Pin+`, not
`Pin-`.  The `Pin-` statement for the `RP2`/Boy-surface shadow must not be lifted
unchanged to `RP4`.

## 4. Primitive twisted sector

The Lean theorem proves:

```text
|n| mod 2 = 1
and
|n| is minimal among positive odd magnitudes
imply
|n| = 1.
```

This closes the purely arithmetic primitive-sector step.  A physical anomaly or
boundary law must still establish that the non-trivial mod-two sector and the
least-action representative are the sectors realized by Janus.

## 5. Whole-slice matching is impossible

The published exact branch imposes `k = -1`.  Its normalized spatial scalar
curvature is

```text
R3_open = -6 / A^2.
```

A round positive-curvature projective slice has

```text
R3_round = +6 / L^2.
```

For positive `A` and `L`, these have opposite signs.  Therefore the complete
three-dimensional bounce slice cannot be identified isometrically with a round
`S3/RP3` tunnel slice merely by setting `A=L`.

This no-go is proved in

```text
P0EFTJanusSpatialCurvatureMatchingNoGo.lean.
```

The viable object is a **finite spherical boundary or null world-volume** with
proper junction conditions.

## 6. Conditional finite-sphere bridge matching

Let `r` be the dimensionless radial coordinate of a finite sphere in the open
FLRW slice, so at the bounce

```text
R_boundary = A r.
```

Introduce the following explicit matching laws:

```text
3 c^2 A = -8 pi G E_global
3 M_bridge = -4 pi E_global r^3
c^2 R_s = 2 G M_bridge
R_boundary = R_s.
```

The second law is the genuinely new bimetric input: it maps the negative signed
Janus sector to a positive bridge mass.  It is **not** ordinary one-metric GR
and is therefore kept as an explicit hypothesis.

The equations imply

```text
R_s = A r^3.
```

Together with `A r = R_s`, positivity gives

```text
r = 1
A = R_s
A / R_s = 1
4 pi E_global + 3 M_bridge = 0.
```

These results are proved in

```text
P0EFTJanusFiniteSphereBridgeMatching.lean.
```

This is stronger than assuming equal radii by hand, but it remains conditional
on deriving the signed quasi-local mass and null junction from the active
bimetric action.

## 7. The LL-brane action fixes `F^2`

For the `p=2` LL-brane action of Guendelman--Kaganovich--Nissimov--Pacheva and
the wrong-sign Maxwell choice

```text
L(F^2) = F^2 / 4,
```

the world-volume equations give

```text
M_measure = F^2 / 4
a0 = F^2 / 4.
```

The Einstein-Rosen junction conditions give

```text
a0 = 1/8
m = 1/(16 pi |chi|)
R_s = 2m = 1/(8 pi |chi|).
```

Therefore

```text
F^2 = 1/2
M_measure = 1/8.
```

This closes `F2_0_dynamical_value_derived` for this specific LL action and
normalization.  It does not fix the tension magnitude `|chi|`.

## 8. Correct auxiliary-flux normalization

The LL constraint is

```text
g_ij = 2 a0 gamma_ij.
```

For an induced spherical metric of radius `R_s`, write

```text
F_theta_phi = f sin(theta)
integral_S2 F = 4 pi f = 2 pi n / q_LL.
```

Contracting the antisymmetric two-form with the **auxiliary** metric gives

```text
F^2 = 8 a0^2 f^2 / R_s^4.
```

With `a0=1/8`, this yields the cleared relation

```text
32 F^2 q_LL^2 R_s^4 = n^2.
```

Using `F^2=1/2` and `|n|=1`:

```text
16 q_LL^2 R_s^4 = 1.
```

This normalization is recorded in

```text
P0EFTJanusLLBraneAuxiliaryFluxClosure.lean.
```

In this convention `q_LL` supplies an inverse-area scale.  Calling it
“dimensionless” merely hides a rescaling length unless that rescaling is
explicitly derived.

## 9. Complete conditional alpha spectrum

Combining

```text
A = R_s
16 q_LL^2 R_s^4 = 1
8 pi |chi| R_s = 1
```

gives

```text
16 q_LL^2 A^4 = 1
8 pi |chi| A = 1
q_LL^2 = 256 pi^4 |chi|^4.
```

For positive variables this is equivalent to

```text
A = 1 / (2 sqrt(q_LL))
|chi| = sqrt(q_LL) / (4 pi).
```

The global source and bridge mass are then related by

```text
E_global = -3 M_bridge / (4 pi).
```

The assembled Lean interface is

```text
P0EFTJanusConditionalAlphaSpectrumClosure.lean.
```

This is the furthest non-circular result currently available: a discrete
primitive sector and a one-parameter dimensionful spectrum.

## 10. Bulk four-form and LL auxiliary flux are distinct

The bulk twisted four-form is the field strength of a three-form potential.  A
codimension-one LL-brane couples electrically to that bulk potential through a
Kalb--Ramond-type charge.

The LL auxiliary field entering `F^2`, however, is a separate two-form intrinsic
to the world-volume.  Therefore

```text
bulk twisted integer = LL auxiliary flux integer
```

is not automatic.  It requires an explicit transgression, anomaly-inflow or
boundary field equation.

The branch blocks silent identification in

```text
P0EFTJanusBulkWorldvolumeFluxSeparation.lean.
```

## 11. Numerical scale diagnostic only

For a diagnostic radius `R_s = 10^26 m`, the conditional formulas require
approximately

```text
q_LL = 2.5e-53 m^-2
|chi| = 3.98e-28 m^-1
M_bridge = 6.73e52 kg
E_global = -1.61e52 kg.
```

These values are outputs after supplying the radius and are **not** a no-fit
prediction.

Conversely, taking a Planck-normalized inverse-area charge

```text
q_LL = 1 / l_P^2
```

gives

```text
R_s = l_P / 2,
```

which is Planckian.  A cosmological bridge therefore requires either an
extremely small fundamental `q_LL`, an enormous integer/degeneracy, or a new
dynamical hierarchy mechanism.

The executable audit is

```text
scripts/audit_janus_finite_bridge_ll_closure.py
```

with its focused test under `tests/`.

## 12. Terminal frontier

The branch now proves or isolates the following:

```text
source factor-two discrepancy: audited
orientation-twisted integer lattice: identified
primitive magnitude |n|=1: proved in Lean
whole-slice round matching: disproved
finite-sphere r=1 and A=R_s: proved conditionally
LL auxiliary invariant F^2=1/2: proved algebraically
conditional alpha spectrum: proved algebraically
bulk/world-volume flux distinction: enforced
absolute q_LL magnitude: not derived
signed bimetric junction: not derived
absolute no-fit A: not closed
```

The absolute-scale problem has therefore been reduced to exactly two physical
atoms:

1. derive the signed finite-boundary/junction law from the nonlinear Janus
   bimetric action;
2. derive the dimensionful LL charge unit `q_LL` (or equivalently `|chi|`) from
   microscopic world-volume/bulk dynamics, without importing `H0`, an observed
   radius, or another freely chosen scale.

Topology, parity and primitive-sector selection cannot supply this last unit by
themselves.  The branch's scale-covariance theorem proves the corresponding
abstract no-go: a nonempty solution family invariant under positive rescaling
cannot select a unique positive length.
