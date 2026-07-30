# P covariant second-variation audit

Status: sectoral bridges; no `1001` input.

## Global closure obstruction

`HESSIAN-GLOBAL-01` is not closed by the existing sectoral operators.
The field-content choice is now explicit rather than hidden:

- `GlobalPhysicalFieldTangent` excludes D10; the legacy extended tangent and
  common analytic aggregate retain it only for regulator/determinant work.
- `P0EFTJanusProgramPGlobalGaugeFixedSpectralHessianFredholm4D` is the corrected
  D10-free spectral target. Its mode family contains only the historical D9
  gauge--ghost packet and the two primitive signed SpinC sectors.
- the Candidate-A matter field and action were migrated directly to
  `Sector → D9PrimitiveSpinCSmoothSection ...`; the primitive smooth action,
  its graph action, exact second Fréchet derivative and Fredholm realization
  now use the same `2D + m²` operator. Their equality is proved on every
  finite two-sector signed coefficient family and exposed directly by the
  global Candidate-A matter summand.
- the abelian and diffeomorphism D9 gauge fermions now have distinct
  ghost/antighost/Nakanishi--Lautrup types. Their combined BRST differential is
  nilpotent, `sΨ` has an exact symmetric Hessian, and its reduced ghost pairing
  is the existing D9 Faddeev--Popov principal symbol.
- the nine corresponding global smooth field species are distinct as well:
  two sector-indexed `U(1)^2`-valued Abelian triples and one tangent-vector
  diffeomorphism triple. Their universal nonminimal differential
  `s c = 0`, `s cbar = B`, `s B = 0` is globally square-zero and extends the
  physical configuration without changing it. The wrappers, their three
  nonminimal triples and their product now inherit the exact real-module
  structures of the existing smooth section spaces; linear physical and
  nonminimal projections are explicit. The corrected gauge-fixed tangent is
  the kernel of the legacy coefficient ghost/auxiliary projection, so those
  spectator directions are held fixed and the typed fields occur only once.
  The physical Abelian rule
  `sA = -dc` is now global and square-zero on the paired state. Its genuine
  `sΨ`, built with the supplied metrics and `δ_g d`, is integrable for every
  finite measure and is attached to the actual Candidate-A metrics,
  Maxwell potentials and nonminimal fields. The state is a real module; the
  mixed action is bilinear, and differentiating
  `t ↦ sΨ(state + t direction)` twice gives its symmetric polarization.
  The physical metric rule `sg`
  still awaits complete de Donder and the gauge-fixed chart.

This removes the old D10 and matter-bundle mismatches without adding an axiom.
It does not close the total Hessian. The D10-free spectral target still covers
only D9 gauge `3` plus the historical five ghost coordinates and SpinC matter;
it omits the two metric tensors, normal displacement, the newly typed
antighost/Nakanishi--Lautrup fields, LL auxiliary
metric/measure and boundary blocks. The LL Fredholm enlargement covers only
the `llField` slice. The `llAuxMetric × llMeasure` directions now have an
exact symmetric Hessian derived from the global LL action, an injective dense
embedding into a Hilbert graph completion and a bounded Riesz representative
which agrees with that same Hessian on the smooth core. This construction also
exposes the honest obstruction: every pure `llMeasure` direction lies in the
Riesz kernel. The closed pure-measure radical and its Hilbert quotient are now
constructed; the descended operator is injective exactly when that radical
equals the full weighted-feature kernel. This equality can fail when the
actual LL energy weights vanish, and closed range still needs a coercive
estimate, so no Fredholm claim follows.

The normal displacement is not a missing field type: the D10-free physical
tangent already contains the genuine sign-clutched smooth normal-line
section, now exposed directly by
`GlobalPhysicalFieldTangent.normalDisplacement`. What is missing is the
faithful chart curve that sends this tangent into the metric/boundary action;
without it, assigning an independent normal Hessian would again be a chosen
operator rather than a second variation.

The canonical non-null GHY block is no longer missing: the existing exact
Candidate-A theorem makes this action summand identically zero for every
global datum. Its pullback to every regular chart is smooth with zero first
and second Fréchet derivatives, hence its same-action Hessian is genuinely
the zero symmetric form. For the finite null-face/counterterm/joint block,
scaling each supplied generator normalization now gives a genuine exact
reparametrization curve; the existing face--joint transgression makes the
global action constant, so both real derivatives vanish. General null-face
geometry and normal-displacement variations remain open.

The existing full-action line bridge must also be retained rather than
reimplemented. On every genuine
`CandidateAEinsteinMaxwellFullMetricFiniteBVVariation`, the same nine-block
Candidate-A/EH/Maxwell/matter/Robin/LL/BV action is `C²` for a Dirac measure,
and for an arbitrary finite measure under the already isolated joint
regularity criteria. The EH and Maxwell pointwise second derivatives are
canonical derivatives of their actual first variations. This is an honest
one-dimensional same-action result, but its configuration space is `Real`;
it is not the missing normed raw-field chart or a Fredholm operator on all
independent directions.

`P0EFTJanusProgramPGlobalActionSpectatorSectors4D` and the unbounded
zero-quotient-Hessian no-go still forbid reusing the historical D10-extended
operator as the action Hessian. The unbounded promotion gate itself now uses
the corrected D10-free LL target, but honestly leaves its dense global
same-action core as residual data. Closing the ticket requires construction,
not a new postulate: a faithful `C²` global gauge-fixed chart with the typed
nonminimal fields; the de Donder operator and pairings; promotion of the
existing linewise general metric/mixed-Maxwell derivatives to one bilinear
chart Hessian; the normal, full LL and general null-boundary blocks; then a
dense synthesis with the correct, nonduplicated multiplicities and a
same-action Fredholm direct sum.

The Abelian smooth differential operator is now constructed. The local raised
potential and its Levi-Civita divergence obey the true transition law, hence
descend for every supplied `SmoothGeneralLorentzMetric` to a global linear
Lorenz codifferential
`δ_g : SmoothAbelianGaugePotential → SmoothScalarField`. Its actual
Faddeev--Popov composite is `δ_g d` and agrees chartwise with the covariant
scalar wave. The earlier canonical operator is exactly the intrinsic-metric
specialization and satisfies `δ(d c)=+□c`. What remains for this block is its integrated Green identity
and `L²` adjoint: the available Green cores still carry an
`integral_eq_divergence` hypothesis, so claiming the adjoint before a genuine
Stokes/volume theorem would add a new assumption. For the metric block there
is now a chart-independent smooth trace `tr_g h`, its differential and the
`-1/2 d(tr_g h)` part of de Donder on
`SmoothSymmetricCovariantTwoTensor`. The induced Levi-Civita derivative is now
constructed in every general-metric presentation, is smooth and symmetric,
satisfies `∇g = 0`, and obeys the full rank-three overlap law. The remaining
step is to descend that law into an actual smooth `T*⊗Sym²T*` section, contract
with `g⁻¹` to obtain `div_g h`, and prove the integrated adjoint. Existing
complete de Donder occurrences are D9 principal symbols only. Replacing the
remaining operator by that symbol or by a nonlocal `H¹` adjoint would be the
unsupported plaster excluded by this audit.

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

## Closed conformal and exact-gauge Maxwell slices

`P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D` globalizes the
Maxwell pairing of two arbitrary smooth abelian potentials, hence its diagonal
Lagrangian density and action, for every `SmoothGeneralLorentzMetric`. The
overlap proof combines `F₁=JᵀF₂J` with `g₁=Jᵀg₂J`; the resulting frame-free
fields are smooth and integrable.

In four dimensions a positive conformal rescaling multiplies the pairing and
Lagrangian density by `scale⁻²` and the relative volume by `scale²`.
Consequently the integrated action is exactly its reference value. Along
`scale(t)=baseScale*exp(t*u)` for a smooth spatial `u`, it is `C∞` and
constant, with zero symmetric conformal Hessian.

`P0EFTJanusMappingTorusFrameFreeMaxwellGaugeOrbitHessian4D` proves global
exact-gauge invariance in either pairing slot against an arbitrary second
potential and for the action. Exact gauge orbits are constant and their
pulled-back symmetric Hessian is zero. Differentiating first in an exact-gauge
direction and then in an arbitrary potential direction certifies the zero
kernel; differentiating first in a logarithmic-conformal metric direction and
then in an arbitrary potential direction gives a zero mixed block.

`P0EFTJanusMappingTorusFrameFreeMaxwellPotentialHessian4D` closes the
fixed-metric physical potential block. It polarizes the global pairing into
an integrable symmetric bilinear form on two arbitrary smooth potential
directions. The exact affine-line expansion identifies its diagonal with the
second derivative, the two-parameter surface identifies its mixed values, and
exact gauge directions lie in both kernels.

This does not construct arbitrary-metric--potential mixing, a field-space
Fréchet Hessian, the Candidate-A interaction or nine-block
chart/core/Jacobi/Fredholm identification. It also does not extend
Einstein--Hilbert to a spatially varying conformal factor.

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

## Global scalar-wave prerequisite

`P0EFTJanusMappingTorusGlobalSmoothScalarWave4D` now proves that the canonical
intrinsic scalar wave is a global smooth scalar field, a real-linear operator,
and integrable for every finite measure.
`P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D` supplies the global smooth
pointwise product and its local gradient Leibniz law. This is a prerequisite
only. Its symmetric algebraic covariant product jet obeys the exact wave
contraction rule with twice the inverse-metric gradient pairing. Compatibility
with the actual second derivative of the global product is now proved. The
resulting global smooth gradient pairing agrees locally with the
inverse-metric contraction and yields the global pointwise wave-product rule.
The spatial-conformal Einstein--Hilbert Hessian and raw curvature
bridge through scalar curvature are closed. The available
metric--potential line/C2 interfaces still require supplied curves and do not
construct an arbitrary metric-section chart.

`P0EFTJanusMappingTorusSpatialConformalMetricJet4D` now identifies the local
coefficient matrix and first derivative of the already constructed positive
smooth conformal Lorentz metric. Its inverse and Christoffel laws are closed,
and the companion curvature jet reaches Riemann, Ricci and scalar curvature.
## Spatial conformal Einstein--Hilbert sector

Closed for the genuine spatial conformal metric line. The exact Christoffel
correction, its derivative, raw Riemann/Ricci/scalar contractions, the
Palatini linear trace and the quadratic trace now prove the standard
four-dimensional conformal scalar-curvature formula. Its exponential
specialization is global:
`R(g_t) = exp(-2tu) (R(g₀) - 6t □u - 6t² ⟨du,du⟩)`.

The conformal volume ratio is `exp(4tu)`. Consequently the frame-free
metric-volume Einstein--Hilbert action is exactly the previously
differentiated conformal action curve. Differentiation under the compact
canonical measure, the symmetric polarized Hessian, and its exact diagonal
second variation at zero therefore apply to the genuine action, not only to a
reduced density model.
