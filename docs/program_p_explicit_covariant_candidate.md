# Program P - Explicit Covariant Candidate A

## Decision

M30 Eq. 80 leaves two interaction densities symbolic.  Candidate A replaces
those two independent-looking slots by the reciprocal half-density
representations of one elementary-symmetric bimetric interaction.  This is a
new completion choice, not a formula attributed to M30.

The pure spin-2 choice follows the Hassan--Rosen bimetric family because it has
a nonlinear massless-plus-massive spin-2 interpretation and a published
Hamiltonian/secondary-constraint route excluding the Boulware--Deser mode:

- [Bimetric Gravity from Ghost-free Massive Gravity](https://arxiv.org/abs/1109.3515)
- [Confirmation of the Secondary Constraint](https://arxiv.org/abs/1111.2070)
- [Resolving the Ghost Problem in non-Linear Massive Gravity](https://arxiv.org/abs/1106.3344)

The repository does not treat those papers as Lean proofs.  Their constraint
analysis remains an external theorem that must be translated and audited for
the exact Janus field and matter content.

## Fields and domain

First covariant stage:

- one oriented four-manifold region `Omega` whose initial boundary is smooth
  and non-null for both metrics;
- two independent Lorentz metrics `g_plus` and `g_minus` on the same base;
- two separate matter multiplets `psi_plus` and `psi_minus`;
- a selected real square-root branch
  `X^2 = g_plus^{-1} g_minus`;
- positive Einstein--Hilbert coefficients `M_plus^2` and `M_minus^2`;
- interaction scale `m^4` and coefficients `beta_0,...,beta_4`.

The metrics are independent variables.  No induced metric is varied again as
an independent field.  The interaction breaks the product of the two metric
diffeomorphism groups to their diagonal subgroup.

The admissible Lorentz domain cannot be all metric pairs. The square-root and
causal-compatibility analysis of
[Hassan--Kocic](https://arxiv.org/abs/1706.07806) and the geometric-mean
parametrization of [Kocic](https://arxiv.org/abs/1803.09752) provide the target
local domain: compatible null-cone/time orientations with a covariantly
selected real root and compatible `3+1` split. Those analytic and causal
conditions are not yet encoded by the current finite matrix contracts.

The corresponding pointwise matrix statement is now exact: a common
invertible frame acts by simultaneous metric congruence and root similarity,
leaving the interaction scalar invariant. The coordinate density is invariant
for unit absolute determinant, while an explicit independent-frame example
fails. The full matrix covector is now constructed by differentiating the
Leibniz determinant and the Newton formulas for `e_2` and `e_3`.
Differentiating a supplied genuine similarity curve gives a commutator
tangent, and this explicit covector annihilates it without a supplied-gradient
hypothesis. This remains a finite-frame Noether identity, not yet the
spacetime diagonal diffeomorphism or Bianchi identity.

## Candidate action

For a non-null Dirichlet boundary problem,

```text
S_A = (M_plus^2/2)  integral_Omega sqrt(|g_plus|)  R[g_plus]
    + (M_minus^2/2) integral_Omega sqrt(|g_minus|) R[g_minus]
    - m^4 integral_Omega sqrt(|g_plus|)
        sum_(n=0)^4 beta_n e_n(X)
    + S_matter_plus[g_plus, psi_plus]
    + S_matter_minus[g_minus, psi_minus]
    + M_plus^2  integral_boundary sqrt(|h_plus|)  epsilon_plus K_plus
    + M_minus^2 integral_boundary sqrt(|h_minus|) epsilon_minus K_minus.
```

Both spin-2 kinetic coefficients are positive.  Candidate A therefore does
not implement the M30 Newtonian choice `kappa = -1` as a negative graviton
kinetic term.  Reproducing the Janus force-sign matrix is a separate matter and
weak-field acceptance test.

Piecewise-null segments, joints/corners and the LL worldvolume are not hidden
in this purely non-null formula. They require a separate stratified extension
before applying Candidate A to the throat geometry; a face may have different
causal type for the two metrics unless the admissible domain excludes it.

`P0EFTJanusExplicitBoundaryDensityLedger.lean` now declares separate pointwise
slots for non-null GHY, null inaffinity, the null expansion counterterm,
joints and a generic worldvolume placeholder with a supplied measure. This
follows the gravitational boundary decomposition
discussed in [Boundary terms of the Einstein-Hilbert action](https://arxiv.org/abs/1607.05986)
and [Gravitational action with null boundaries](https://arxiv.org/abs/1609.00207).
The strata remain typed separately and are summed only after integration; the
two gravitational sectors share one common worldvolume contribution rather
than double counting it. The null counterterm uses the continuous zero branch
at vanishing expansion. This is a convention-explicit EH ledger, not the LL
auxiliary-field action, the integrated throat functional, or a proof that its
variation cancels the Candidate-A bulk flux. The missing lightlike-brane slot
must use its actual
auxiliary metric/measure fields, as in the published
[LL-brane action](https://arxiv.org/abs/hep-th/0703114), rather than a
determinant measure of the degenerate induced metric.

`P0EFTJanusExplicitBoundaryDensityLocalVariations.lean` computes exact affine
one-parameter derivatives of the GHY extrinsic-curvature slot, null
inaffinity, joint angle, and local worldvolume Lagrangian/tension. Measures,
metrics, inverses and the other geometric inputs are fixed in these curves.
This is not the full metric variation, an integrated EH-flux cancellation, or
an LL auxiliary-field equation.

The non-null GHY gate now also proves the linearized inverse identities,
varies the inverse-metric/extrinsic-curvature trace, and derives the variation
of `sqrt(|det h|)` from the actual affine metric curve. Their product gives the
exact pointwise first jet of the GHY density with no supplied measure tangent.
The inverse used away from the base point is deliberately labelled an affine
first-jet representative, not the exact inverse of `h + t delta h`; the
extrinsic-curvature tangent is still supplied. Thus this is not yet a curve in
the full geometric boundary-data space, the physical EH-flux cancellation, or
an integrated boundary theorem.

For the null expansion counterterm, the actual derivative of
`theta log(lengthScale * |theta|)` is now proved for positive length scale and
nonzero expansion and lifted to the fixed-measure ledger density. Along the
explicit path `theta = exp(-t)/lengthScale`, its derivative coefficient is
`1-t` and is unbounded below while `theta -> 0`. Thus the continuous zero value
does not silently provide a regular first variation; a zero-expansion
prescription remains part of the admissible boundary problem.

A separate two-sector local model now matches each supplied bulk boundary
flux with the explicit fixed-geometry GHY derivative. The matched first
variation reduces exactly to the interior Euler term, stationarity is
equivalent to both interior equations, and a mismatched coefficient leaves a
proved nonzero residual. This instantiates the cancellation architecture but
does not derive the physical Einstein--Hilbert flux or perform any stratum
integration.

## The two M30 density slots

Let

```text
V_beta(X) = sum_(n=0)^4 beta_n e_n(X).
```

Candidate A defines

```text
S_cross       = -(m^4/2) V_beta(X),
Sbar_cross    = -(m^4/2) V_reversed(X^{-1}),
beta_reversed_n = beta_(4-n).
```

They have no matter-field dependence.  Matter occurs only in the two declared
sector actions.  On a positive square-root branch,

```text
sqrt(|g_minus|) = sqrt(|g_plus|) det(X),
det(X) V_reversed(X^{-1}) = V_beta(X).
```

Consequently the two weighted half-densities are equal and their sum is
exactly the single interaction term in `S_A`.  This removes both independent
cross-density freedom and accidental double counting.

The Lean spectral theorem treats the plus-volume and `det(X)` ratio as
explicit weights. The matrix gate separately derives
`sqrt(|g_minus|) = sqrt(|g_plus|) det(X)` from nondegenerate square-root data
and proves the end-to-end identification for a supplied real diagonalization.
It still does not construct that diagonalization or the smooth branch.

The pointwise derivative chain is now explicit. The map
`(g_plus_inverse, g_minus) -> g_plus_inverse * g_minus` has its actual Frechet
derivative, the squaring map has its actual first and second Frechet
derivatives, and a supplied differentiable square-root selection has the
Sylvester inverse formula for its derivative. A further gate removes the
independent-inverse shortcut: for an invertible `g_plus` it proves
`D(g_plus^{-1})[delta g] = -g_plus^{-1} delta g g_plus^{-1}` and composes this
with `g_minus` before applying Sylvester. On the open positive diagonal
spectrum chart, the Sylvester operator now has an explicit entrywise
continuous-linear two-sided inverse, and the conditional square-root
derivative specializes to it. The differentiable Lorentzian root selection
and a Sylvester inverse on the full causal-compatible matrix domain remain to
be constructed.

The full four-eigenvalue identity, its proportional specialization, explicit
matter independence and the weighted no-double-counting equality are proved in
`P0EFTJanusExplicitReciprocalCrossDensities.lean`.

`P0EFTJanusMatrixSquareRootInteractionDensity.lean` defines the same potential
from the Newton trace/determinant invariants of an actual `4 x 4` matrix,
proves its diagonal-spectrum specialization and invariance under invertible
similarity, and records nondegenerate symmetric metric data, an invertible
positive-determinant root, `X^2 = g_plus^{-1} g_minus`, and a branch-uniqueness
contract.  The branch contract is supplied data: it does not construct a
smooth real principal square-root field.  An exact diagonal bridge proves that
the matrix coordinate density contains one, and only one, plus-volume factor
multiplying the measure-free common potential.

`P0EFTJanusExplicitReciprocalCrossDensityFrechet.lean` proves the actual
Frechet gradient, Hessian symmetry and nonlinear Helmholtz condition of the
four-eigenvalue interaction, and checks its proportional derivative against
the existing PT-flat force.  These are spectral-chart results, not metric
functional derivatives.

That full spectral chart also corrects the reduced stability reading: whenever
the displayed `01` mixed Hessian coefficient is nonzero, two explicit
eigenvalue directions have opposite interaction-Hessian signs. In particular,
the positive PT-flat reduced cone remains interaction-Hessian indefinite in
this larger chart. This is not a ghost theorem or a stability verdict because
kinetic, gauge and constraint sectors are absent.

On the product of this spectral chart with two independent scalar matter
coordinates, the displayed Candidate-A interaction plus two quadratic matter
slots now has its actual Frechet Euler one-form and actual Hessian. Stationarity
is equivalent to the spectral equation and the two matter equations; both
interaction--matter Hessian blocks vanish, and the full pointwise Euler
Jacobian is symmetric. These are exact finite-dimensional Euler/Helmholtz
results, not the Einstein or matter PDEs.

## PT/exchange branch

Metric exchange is imposed by

```text
M_plus^2 = M_minus^2,
beta_n = beta_(4-n),
(g_plus, psi_plus) <-> (g_minus, psi_minus).
```

This additionally requires an explicit identification of the two matter
field spaces, equality of their actions under exchange, and compatible
boundary data. Those matter/boundary exchange contracts are not yet proved.

Flatness of the proportional point `g_minus = g_plus` further gives the
already formalized family

```text
beta_0 = beta_4 = -4 beta_1 - 3 beta_2,
beta_3 = beta_1.
```

The cone `beta_1 > 0`, `beta_2 >= 0` has a positive reduced relative-mode
curvature. It is not sufficient for nonlinear stability and does not make the
full spectral interaction Hessian positive.

On the FLRW diagonal spectrum `(N_minus/N_plus, r, r, r)`, the reciprocal
interaction is exactly affine in both lapses. Its two lapse variations are
primary-constraint precursors and all lapse Hessian entries vanish. For the
vacuum reduced Hamiltonians taken as explicit model inputs, the canonical
bracket is now factorized into a kinematic and a potential factor, primary
preservation forces the resulting reduced secondary constraint, and an exact
local witness has three independent constraint covectors and fixes
`N_minus = 2 N_plus`. The primary and secondary covectors are also verified as
actual derivatives along arbitrary affine phase-space lines on their regular
domains. This witness uses unrestricted
coefficients outside the committed PT/exchange-flat family. The covariant
Legendre bridge, ADM shift/functional bracket, generic rank and BD closure
remain open.

The source algebra is also explicit: a single-sheet matter source generically
excites the relative mode, equal sources remove it, and opposite PT sources
are purely relative. This is a PPN rejection precursor, not a propagator, PPN
parameter, or observational bound.

The scheme audit now instantiates the existing parity-odd anomaly proxy with
Candidate-A parameters. PT pairing cancels that proxy, but two explicit
witness pairs remain flat-compatible and anomaly-proxy-free while differing
in the overall normalization or a reduced flat-vanishing parity-even
finite-counterterm proxy `(c-1)^4`. Its covariant admissibility is not proved.
Therefore this proxy cannot close the scheme. No determinant
line, regulator, or physical Janus anomaly is computed by that no-go.

## Acceptance ledger

Implemented in the current finite, spectral or pointwise models:

- explicit formulas for both interaction densities;
- exact spectral weight reciprocity for all four nonzero eigenvalues;
- exact metric-volume ratio for supplied nondegenerate square-root data and
  its identification with the spectral ratio on a supplied diagonalization;
- one common interaction without double counting;
- cross-density matter independence;
- PT coefficient reversal and flat proportional coefficient family;
- positive reduced relative-mode curvature in the selected cone;
- actual spectral Frechet gradient, Hessian and Helmholtz symmetry;
- explicit opposite-sign directions for a nonzero `01` spectral mixed Hessian;
- pointwise matrix potential and invertible-frame similarity invariance;
- simultaneous-frame interaction invariance, an independent-frame
  counterexample, an explicit matrix Frechet covector and its unconditional
  commutator pairing along supplied similarity curves;
- actual derivatives of metric inversion and `g_plus_inverse * g_minus`, plus
  an explicit two-sided Sylvester inverse on the open positive diagonal chart
  and a conditional derivative of a supplied differentiable square root;
- explicit pointwise EH-stratum ledger plus a generic supplied-measure
  worldvolume placeholder;
- exact fixed-geometry affine variations of selected boundary/worldvolume
  slots;
- exact non-null GHY pointwise first jet, including the determinant-derived
  measure tangent and the linearized inverse-metric contribution;
- actual nonzero-expansion null-counterterm derivative and its explicit
  singular approach to zero expansion;
- exact local two-sector bulk/GHY cancellation and a nonzero mismatch
  residual;
- finite Gram-tensor map, its actual first and second derivatives, positivity
  on the injective immersion domain, and the associated concrete finite
  compatibility map and Jacobian;
- first-jet naturality of `K` and its actual `J` under source-frame changes and
  ambient isometries, with ambient infinitesimal isometries in `ker J`;
- exact classification of additive reduced scale translation; relating it to
  the covariant diagonal diffeomorphism remains a separate bridge;
- exact FLRW lapse affinity and primary-constraint precursors, plus reduced
  bracket factorization and an unrestricted-parameter local Dirac-chain
  witness for the secondary constraint and lapse ratio;
- exact diagonal/relative source decomposition as a PPN rejection precursor;
- actual pointwise Euler equations and symmetric full Hessian for the spectral
  interaction plus two independent quadratic matter blocks;
- explicit Candidate-A witnesses proving that the paired anomaly proxy fixes
  neither overall normalization nor the reduced finite even-counterterm proxy.

Still required before Candidate A is a completed Janus action:

1. extend the diagonal-chart Sylvester inverse to a smooth real principal
   square-root branch on the admissible Lorentz field domain, prove the density
   transformation law and control branch changes;
2. lift the pointwise spectral/matter Euler equations to both covariant metric
   and spacetime matter Euler--Lagrange PDEs from `S_A`;
3. replace the GHY first-jet representative by a genuine curve of geometric
   boundary data, instantiate and integrate all gravitational strata,
   construct the actual LL auxiliary-field action, specify the zero-expansion
   variational domain, and prove cancellation of the physical bulk flux;
4. instantiate the diagonal diffeomorphism generator and covariant Noether--
   Bianchi identity;
5. reproduce the Janus Newtonian sign matrix without a negative spin-2 kinetic
   mode;
6. derive the reduced Hamiltonians from the covariant Candidate-A Legendre
   transform, move the local FLRW witness onto the selected PT branch, and
   extend it to the ADM shift, functional Poisson bracket and generic
   independent secondary-constraint closure; then derive constrained stability
   and PPN parameters for the exact matter couplings;
7. compute the actual local/global anomalies in one regulator and supply a
   microscopic normalization/finite-part law in that same scheme.

Candidate A is rejected if any of items 1--7 fails.  No observed-radius input
is used in its definition.

## Six-lock checkpoint

| Lock | Implemented now | Remaining rejection test |
| --- | --- | --- |
| 1. Cross densities | explicit reciprocal pair, one common interaction, spectral Frechet data, actual metric-inverse/relative-product derivatives, and two-sided Sylvester inverse on the open positive diagonal chart | smooth Lorentz root/Sylvester inverse on the causal-compatible domain, density covariance and full metric functional variation |
| 2. Fields/induced/gauge | independent field choice, simultaneous-frame invariance/counterexample, constructed matrix covector and unconditional finite-frame commutator pairing | global field space and actual diagonal diffeomorphism action |
| 3. Bulk/boundary/worldvolume | typed ledger, determinant-measure GHY first jet, null-counterterm singularity audit and exact local matched bulk/GHY cancellation | genuine geometric boundary curve, physical EH metric flux, zero-expansion prescription, throat data, LL action/EOM and stratum integration |
| 4. Concrete `K/J` | actual first-jet Gram `K/J`, source/ambient naturality and explicit gauge-kernel directions | Lorentzian/global Janus compatibility PDE/jet complex and symbol exactness |
| 5. Euler/Helmholtz/Noether | actual spectral-plus-matter Euler/Hessian/Helmholtz, explicit finite-frame Noether, FLRW primary precursor, reduced bracket factorization and local secondary/lapse witness | covariant metric/matter PDEs, diagonal Bianchi, Candidate-A Legendre bridge, PT-branch genericity and ADM shift/Poisson closure |
| 6. Stability/scheme | explicit spectral interaction indefiniteness, source-mode rejection precursor and reduced Candidate-A anomaly-proxy scheme-freedom no-go | constrained kinetic stability, PPN derivation, covariantly admissible counterterms, actual regulated anomalies and a microscopic normalization/finite-part law |
