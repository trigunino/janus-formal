# Janus Quantum World-Volume Alpha Program

## Purpose

Generate the absolute LL-brane charge scale without importing `H0`, an observed
radius, a fitted `alpha`, or an arbitrary world-volume mass parameter.

The classical bridge program has already reduced the exact-solution length
`A = alpha^2` to

```text
16 q_LL^2 A^4 = 1,
8 pi |chi| A = 1.
```

Therefore a microscopic derivation of `q_LL` or `|chi|` fixes `A`.

## Concrete candidate theory

On the `2+1` dimensional LL world-volume, introduce:

- a real scalar `phi`;
- a compact `U(1)` connection `A_aux`;
- its intrinsic field strength `F_aux`;
- an integer Chern--Simons level `k`;
- the existing non-Riemannian LL measure sector.

A classically scale-invariant candidate density is

```text
L_WV = 1/2 (D phi)^2
       - lambda6 phi^6 / 6
       - F_aux^2 / (4 phi^2)
       + Chern--Simons_k[A_aux]
       + L_LL-measure.
```

In three spacetime dimensions:

```text
[phi] = 1/2,
[A_aux] = 1,
[(D phi)^2] = 3,
[phi^6] = 3,
[A dA] = 3,
[F_aux^2 / phi^2] = 3.
```

Thus no classical dimensionful coefficient is required.  By contrast, an
ordinary undressed Maxwell term needs a coefficient of mass dimension `-1` and
would simply hide the missing scale.

Lean file:

```text
JanusFormal/Branches/WorldvolumeQuantumAlpha/Gates/
  P0EFTJanusScaleInvariantWorldvolumeAction.lean
```

## Condensate-to-alpha map

Let the renormalized vacuum select

```text
v = <phi> > 0
```

and let the normalized LL charge be

```text
q_LL = c_q v^2,
```

where `c_q` is dimensionless and must be computed from the compact gauge-field
normalization.

Primitive flux then gives

```text
4 c_q v^2 A^2 = 1.
```

For `c_q = 1`:

```text
2 v A = 1,
A = 1/(2v).
```

Lean file:

```text
P0EFTJanusCondensateToAlphaMap.lean
```

## Dimensional transmutation

A Planck-anchored asymptotically free or nonperturbative sector may generate

```text
ell_dyn = ell_UV exp(X),
B X = 8 pi^2,
q_LL ell_dyn^2 = 1.
```

The primitive LL law then gives

```text
2 A = ell_dyn = ell_UV exp(X).
```

For `ell_UV = ell_P` and a diagnostic `A = 10^26 m`:

```text
X ~= 140,
B = beta0 g_UV^2 ~= 0.56.
```

Representative couplings are moderate:

```text
beta0 = 7  -> g_UV ~= 0.28,
beta0 = 11 -> g_UV ~= 0.23.
```

However the hierarchy is exponentially sensitive:

```text
d log A / d log g = -2 X ~= -280.
```

Therefore a fit of `g_UV` would be useless.  The microscopic theory must derive
`beta0`, fix `g_UV` through an integer level or bulk boundary law, and prove that
the vacuum is stable and unique.

Lean file:

```text
P0EFTJanusWorldvolumeRGTransmutation.lean
```

Executable audit:

```text
scripts/audit_janus_worldvolume_quantum_completion.py
```

## Parity anomaly

For unit-charge fermions in `2+1` dimensions, use the doubled-level convention

```text
2 k_eff = 2 k_bare + N_f.
```

An exactly vanishing integral effective level requires even `N_f`.  An odd
multiplicity obstructs a single-fold parity-symmetric zero-level theory.  A
Janus pair can instead carry opposite levels, so the total paired theory is PT
symmetric while each fold is anomalous.

Lean file:

```text
P0EFTJanusWorldvolumeParityAnomaly.lean
```

This discrete anomaly condition can select sectors and matter content.  It does
not by itself generate a length.

## Flat-direction no-go

An exactly flat positive vacuum family cannot select a unique scale.  The Lean
branch proves that if every positive condensate is a vacuum, `ExistsUnique`
fails.  Consequently a Bardeen--Moshe--Bander-like flat direction is not a
prediction until quantum corrections, a boundary condition or a stable gap
equation lifts the modulus.

Lean file:

```text
P0EFTJanusWorldvolumeVacuumSelection.lean
```

## Literature anchors and caveat

Relevant mechanisms exist in three-dimensional field theory:

- Maxwell--Chern--Simons scalar QED dimensional transmutation:
  `arXiv:hep-th/9509109`;
- large-N Chern--Simons scalar spontaneous scale breaking:
  `arXiv:1402.4196`;
- related fermionic large-N phase:
  `arXiv:1404.7477`.

But stability is a major caveat.  The proposed light dilaton phase was found
unstable in `arXiv:1605.00750`, and a recent next-to-leading large-N revisit of
the three-dimensional `phi^6` model reports the disappearance of the naive BMB
fixed line (`arXiv:2502.07880`).  Those papers motivate a mechanism; they do not
establish the Janus world-volume theory.

## Acceptance criteria

The quantum route closes only after all of the following are derived:

1. compact `U(1)` bundle and global flux operator;
2. anomaly-free paired matter content;
3. renormalized effective action;
4. bounded-below Hamiltonian or reflection-positive Euclidean theory;
5. unique stable nonzero condensate;
6. computed `beta0` or exact gap equation;
7. microscopic law fixing the UV coupling;
8. bulk-gravity UV anchor;
9. convention-independent charge normalization `c_q`;
10. controlled Lorentzian continuation;
11. no target cosmological scale inserted anywhere.

## Verdict

This is the only currently explicit mechanism in the branch capable of
producing a cosmological hierarchy without an integer of order `10^122`.
It is also highly sensitive and requires a genuinely new quantum theory.
The mathematical map from its derived RG data to `A` is closed; the quantum
dynamics selecting those data is the remaining research theorem.
