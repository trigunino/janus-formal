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
Sylvester inverse formula for its derivative. The inverse plus metric remains
an independent input, and both the differentiable Lorentz branch and the
continuous-linear inverse of the Sylvester operator are hypotheses rather
than constructed objects.

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
primary-constraint precursors and all lapse Hessian entries vanish. A concrete
ledger counterexample proves that lapse affinity alone does not supply the
secondary constraint; shift redefinition and Poisson closure remain open.

The source algebra is also explicit: a single-sheet matter source generically
excites the relative mode, equal sources remove it, and opposite PT sources
are purely relative. This is a PPN rejection precursor, not a propagator, PPN
parameter, or observational bound.

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
- actual derivative of `g_plus_inverse * g_minus` and a conditional
  Sylvester-inverse derivative of a supplied differentiable square root;
- explicit pointwise EH-stratum ledger plus a generic supplied-measure
  worldvolume placeholder;
- exact fixed-geometry affine variations of selected boundary/worldvolume
  slots;
- finite Gram-tensor map, its actual first and second derivatives, positivity
  on the injective immersion domain, and the associated concrete finite
  compatibility map and Jacobian;
- exact classification of additive reduced scale translation; relating it to
  the covariant diagonal diffeomorphism remains a separate bridge;
- exact FLRW lapse affinity and primary-constraint precursors, with a proved
  non-implication of the secondary constraint;
- exact diagonal/relative source decomposition as a PPN rejection precursor.

Still required before Candidate A is a completed Janus action:

1. construct the smooth real principal matrix square root and Sylvester inverse
   on the admissible Lorentz field domain, derive `D(g_plus_inverse)` from
   `g_plus`, prove the density transformation law and control branch changes;
2. derive both metric and matter Euler--Lagrange equations from `S_A`;
3. instantiate and integrate the declared gravitational strata, construct the
   actual LL auxiliary-field action, and prove cancellation of the bulk flux;
4. instantiate the diagonal diffeomorphism generator and covariant Noether--
   Bianchi identity;
5. reproduce the Janus Newtonian sign matrix without a negative spin-2 kinetic
   mode;
6. extend the FLRW primary precursor to the ADM shift, Poisson and independent
   secondary constraint, then derive the kinetic/constrained stability and PPN
   parameters for the exact matter couplings;
7. compute anomalies, normalization and finite counterterms in the same
   scheme.

Candidate A is rejected if any of items 1--7 fails.  No observed-radius input
is used in its definition.

## Six-lock checkpoint

| Lock | Implemented now | Remaining rejection test |
| --- | --- | --- |
| 1. Cross densities | explicit reciprocal pair, one common interaction, spectral Frechet data, actual relative-product derivative and conditional Sylvester formula | derivative of metric inversion plus smooth Lorentz branch/Sylvester inverse and metric variation |
| 2. Fields/induced/gauge | independent field choice and finite Gram tensor with an injective immersion domain | global field space and actual diagonal diffeomorphism action |
| 3. Bulk/boundary/worldvolume | typed density ledger, generic worldvolume placeholder and fixed-geometry affine slot derivatives | full metric variation, geometric throat data, actual LL action/EOM, integration and flux cancellation |
| 4. Concrete `K/J` | actual finite Gram compatibility map and Jacobian | full Janus compatibility PDE/jet complex |
| 5. Euler/Helmholtz/Noether | spectral Hessian/Helmholtz, reduced proxy no-go and exact FLRW primary-constraint precursor | covariant Euler equations, diagonal Bianchi, ADM shift/Poisson and secondary constraint |
| 6. Stability/scheme | explicit spectral interaction indefiniteness and exact source-mode rejection precursor | constrained kinetic stability, PPN derivation, anomalies, normalization and counterterms |
