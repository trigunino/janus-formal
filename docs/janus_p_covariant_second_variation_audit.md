# P covariant second-variation audit

Status: isolated bridge; no `1001` input.

## Closed tensor sector

The P interaction Hessian is exactly the relative bilinear mass form.  Combined
with the positive two-sheet Einstein--Hilbert TT Fourier operator already
audited in program B, it gives two constraint-reduced tensor channels:

`omega_diag^2(k) = k^2`,

`omega_rel^2(k) = k^2 + m_rel^2 (1/M_plus^2 + 1/M_minus^2)`.

The first is the common massless graviton.  The second is the weighted relative
massive graviton.  Positive Planck weights and positive relative mass make the
massive frequency strictly positive.  TT modes require no scalar lapse/shift
elimination, so this bridge is the clean part of the requested reduction.

The newer P linearized-Einstein symbol now removes one conditional input from
this bridge.  On the explicit TT polarization `h_12=h_21=A` and Fourier
covector `(omega,0,0,k)`, its actual component is

`G_12 = (1/2) (omega^2-k^2) A`.

For nonzero amplitude the vacuum equation therefore derives
`omega^2=k^2` directly inside P, with the Bianchi identity and pure-gauge
kernel already proved by the source gate.  The common TT spatial operator is
no longer merely imported from B.

## Vector/scalar boundary

Program B contains exact algebraic Schur-complement and stability theorems, and
its executable square-root expansion checks projected interaction Hessians.
However, the scalar-reduction script explicitly leaves open:

- the full Einstein--Hilbert scalar quadratic action;
- exact normalized projection into the interaction Hessian variables;
- reinsertion of lapse/shift/bending solutions into that full action;
- the independent secondary Hamiltonian constraint.

Therefore the current vector/scalar dispersions are conditional coefficient
models, not yet the second variation of the complete P action.  Promoting them
would overstate the derivation.

## Consequence for mode counting

The tensor result fixes two polarizations in each of one massless and one
massive TT channel, over whatever spatial spectrum the background and boundary
conditions provide.  It selects no finite global count and does not revive
`1001`.

## Exact TT kernel classification

The two-sheet Fourier equations are now diagonalized without an additional
physical assumption. Their symbol determinant factors exactly as

`(1/4) (omega^2-k^2) (omega^2-k^2-4 coupling)`.

Consequently, for nonzero coupling:

- away from both dispersion shells, the TT kernel is trivial;
- on the massless shell, every solution is common (`h_plus=h_minus`);
- on the massive shell, every solution is relative (`h_plus=-h_minus`).

Positive coupling gives a strict relative mass gap. Negative coupling instead
produces a low-momentum interval with no real frequency. These are exact
statements for the isolated flat TT reduction only; they do not close the ADM
scalar/vector sector.

Off both shells, the inverse `2 x 2` tensor symbol is also explicit and proved
to be the unique response to an arbitrary pair of sheet sources. Its
denominator is precisely the factored determinant above, so the reduced
propagator introduces no additional tensor pole.
