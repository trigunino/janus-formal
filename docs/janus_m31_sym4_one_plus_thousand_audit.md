# M31 / Sym4: audit of the `1 + 1000` coincidence

Status: isolated experiment; no promotion into the Janus research heads.

For an eleven-dimensional vector space equipped with a nondegenerate invariant
quadratic form `q`, the orthogonal harmonic decomposition gives

`Sym^4(V) = H^4(V) + q H^2(V) + <q^2>`.

Its dimensions are `935 + 65 + 1 = 1001`.  Thus a canonical invariant line
`<q^2>` and a `1000`-dimensional complement really do arise in the orthogonal
case.  The Lean audit constructs the radial quartic and proves its invariance
under every map preserving `q`; it also checks the dimension arithmetic.

This does not currently apply to the full M31 action.  M31 is an affine
extension: its coadjoint action contains the translation-dependent term
`D P^T L^T - L P D^T` in the moment component.  Such terms act as shears, not
as orthogonal transformations on the eleven torsor coordinates.  The source
provides the Lorentz Casimir `E^2-p^2`, but not a nondegenerate invariant
quadratic form on the complete eleven-dimensional representation whose fourth
symmetric power was used in the `1001` candidate.

Verdict: `1 + 1000` is a mathematically natural conditional mechanism, but it
is not yet a Janus/M31 derivation.  Advancing it requires either an M31-invariant
nondegenerate pairing on the selected eleven-dimensional module, or a justified
restriction/quotient on which such a pairing exists.
