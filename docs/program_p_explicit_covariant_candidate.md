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

The parametrized global-field gate is now based on the actual effective D8
mapping-torus and fixed-throat quotients.  The two continuous PT maps are
involutive, their common quotient throat inclusion is equivariant, and the
independent-field exchange preserves that same inclusion.  This is a
same-object topological base bridge. The same two quotient objects now carry
covering-induced analytic `ChartedSpace` and `IsManifold` structures; both
cover projections are analytic local diffeomorphisms and the injective throat
inclusion is `C∞`. A differential immersion/embedding theorem and curved
tensor fields are still not constructed.

On exactly those bases, a nonempty algebraic field branch now takes both
metric matrices to Minkowski, both scalar matter fields to zero and the
relative root to the identity.  Its inverse/volume slots are exact and the
whole independent configuration is fixed by the effective PT exchange.
Concrete continuity predicates cover every independent, induced and LL
coordinate; the same branch therefore inhabits a continuous PT-matched
effective configuration with exact throat inclusion and root-square equation.
This is only a topological field-space realization: it supplies no Sobolev or
smooth spaces, boundary traces/conditions, field equation, stationarity,
stability or global root map.

The analytic D8 cover now provides the next layer: coefficient fields into any
normed real fiber can be required to be genuinely smooth upstairs and exactly
invariant under every deck iterate. They descend continuously and injectively
to the same effective quotient. In particular, two metric-coefficient fields,
two scalar fields and an identity-root coefficient field have a nonempty
constant smooth witness. This is not yet a Lorentz-constrained configuration
or a Sobolev/traced field space directly on the `C∞` quotient.

The admissible Lorentz domain cannot be all metric pairs. The square-root and
causal-compatibility analysis of
[Hassan--Kocic](https://arxiv.org/abs/1706.07806) and the geometric-mean
parametrization of [Kocic](https://arxiv.org/abs/1803.09752) provide the target
local domain: compatible null-cone/time orientations with a covariantly
selected real root and compatible `3+1` split. Those analytic and causal
conditions are not yet encoded by the current finite matrix contracts.

A concrete nonempty subchart is now encoded: both Lorentz metrics are
co-diagonal with one negative and three positive entries built from positive
scales. Their inverses, the positive ratio root, `X^2 = g_plus^{-1} g_minus`,
`det X > 0`, and uniqueness among positive diagonal roots are proved, and the
positive-diagonal Sylvester witness is instantiated. On the open positive
scale-pair domain, the metric, inverse, relative target and root now have
actual Frechet derivatives; differentiating the square identity proves the
Sylvester equation internally. This proves a first Frechet derivative on the
local co-diagonal chart, not higher regularity, an open Hassan--Kocic domain or
a root selection for arbitrary Lorentz pairs.

On that same positive chart, the complete Candidate-A interaction density is
now differentiated as an actual composite map: plus metric to determinant,
absolute value and square root, together with root matrix to the full
five-coefficient spectral potential. The resulting Frechet covector is
rewritten through the explicit positive Sylvester inverse and the density is
proved equal to the committed pointwise Candidate-A expression. This remains
a finite scale-pair derivative, not a metric-functional derivative on a
manifold.

The corresponding pointwise matrix statement is now exact: a common
invertible frame acts by simultaneous metric congruence and root similarity,
leaving the interaction scalar invariant. The coordinate density is invariant
for unit absolute determinant, and for a general invertible frame it carries
the exact weight `|det Q|`; multiplication by the supplied inverse-frame
Jacobian restores the original representative. An explicit independent-frame
example fails. The full matrix covector is now constructed by differentiating
the Leibniz determinant and the Newton formulas for `e_2` and `e_3`.
Differentiating a supplied genuine similarity curve gives a commutator
tangent, and this explicit covector annihilates it without a supplied-gradient
hypothesis. This remains a finite-frame Noether identity, not yet the
spacetime diagonal diffeomorphism or Bianchi identity.

The same exact covariance is also lifted from one point to an arbitrary
finite field of sites. Each site may carry its own simultaneous diagonal
frame, and its inverse determinant compensates the local density weight; the
weighted finite sum is exactly invariant. Independent sheet frames still fail
at one site. This is a finite algebraic local-frame symmetry, not a manifold
diffeomorphism or spacetime integral.

An actual one-dimensional diagonal pullback is now also present. For
`phi_epsilon(t) = t + epsilon xi(t)`, the displayed Jacobian
`J_epsilon = 1 + epsilon xi'(t)` is proved to be `partial_t phi_epsilon`.
Differentiating the genuine pulled-back Candidate-A density
`J_epsilon rho(phi_epsilon)` at `epsilon = 0` gives
`xi rho' + xi' rho = (xi rho)'`, followed by an exact oriented endpoint
ledger. This is a one-dimensional reparametrization model, not the spacetime
diagonal diffeomorphism or covariant Bianchi identity.

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
variation cancels the Candidate-A bulk flux. The full lightlike-brane slot
must ultimately use its actual
auxiliary metric/measure fields, as in the published
[LL-brane action](https://arxiv.org/abs/hep-th/0703114), rather than a
determinant measure of the degenerate induced metric.

A finite pointwise LL model now instantiates that slot with an independent
symmetric auxiliary inverse metric, a non-Riemannian measure density and a
magnetic worldvolume flux. Actual metric, measure and flux derivatives give
the symmetric auxiliary stress equation and the measure constraint. On the
conditional auxiliary branch the induced metric has an explicit nonzero null
vector. A companion affine `2+1` first-jet model realizes the measure as the
signed determinant of the Jacobian of three auxiliary scalars. It proves the
actual determinant variation along every affine line, its signed coordinate
weight and compensation, and a nondegenerate identity-jet witness. The full
determinant map also now has a genuine Frobenius-space Frechet derivative at
every first jet, including singular jets, and its continuous covector agrees
exactly with the earlier line coefficient. This verifies local algebra only:
it does not construct global auxiliary fields or an orientation-changing
absolute density, prove branch non-emptiness, derive the worldvolume PDEs or
integrate a throat solution.

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

A stronger gate now replaces that inverse first-jet representative by the
actual matrix inverse `(h + t delta h)^{-1}`. It proves local invertibility,
the two-sided inverse identities, the forced inverse derivative, and the same
determinant-measure GHY derivative along the resulting exact local algebraic
curve. The curve is only inverse-compatible in the proved neighbourhood;
that gate still supplied `delta K` independently.

The next gate removes that scalar slot pointwise. It uses the exact local
inverse of `h(t) = h + t delta h`, the affine covariant form
`B(t) = B + t delta B`, and defines `K(t) = tr(h(t)^{-1} B(t))`. Product and
inverse differentiation derive `K'`, the determinant measure and the complete
GHY density derivative with no supplied scalar `delta K` or measure tangent.
An affine normal metric jet realizes `partial_n h = 2 B`. Constructing an
embedding, its unit normal and Levi-Civita second fundamental form, then
lifting the flux to arbitrary coordinates and integration, remain open.

For the null expansion counterterm, the actual derivative of
`theta log(lengthScale * |theta|)` is now proved for positive length scale and
nonzero expansion and lifted to the fixed-measure ledger density. Along the
explicit path `theta = exp(-t)/lengthScale`, its derivative coefficient is
`1-t` and is unbounded below while `theta -> 0`. Thus the continuous zero value
does not silently provide a regular first variation. More sharply, the zero
extension is continuous, but the explicit sequence
`theta_n = exp(-n)/lengthScale` has difference quotient `-n`; hence no finite
derivative, and therefore no differentiability, exists at zero. A
zero-expansion prescription remains part of the admissible boundary problem.

For a one-dimensional null-generator model, actual derivatives satisfying
`A' = A Theta` and the reparametrization shift `kappa -> kappa + sigma'`
now give the exact local transgression
`A sigma' + A Theta sigma = (A sigma)'`. A typed oriented endpoint ledger
cancels its final-minus-initial face shift against opposite joint shifts.
This fixes the algebraic sign architecture only: the transformation law and
corner orientations are model conventions here, with no integration theorem,
global null geometry or `Theta = 0` counterterm prescription.

A separate two-sector local model now matches each supplied bulk boundary
flux with the explicit fixed-geometry GHY derivative. The matched first
variation reduces exactly to the interior Euler term, stationarity is
equivalent to both interior equations, and a mismatched coefficient leaves a
proved nonzero residual. This instantiates the cancellation architecture but
does not derive the physical Einstein--Hilbert flux or perform any stratum
integration.

That supplied-flux caveat is now removed in one controlled gauge. In a finite
Gaussian-normal `4 x 4` point model with unit lapse, zero shift and fixed
normal, the inverse metric, normal metric-variation jet, linearized
Christoffel tensor and both Palatini traces are constructed explicitly. The
Stokes orientation and normal-covector factors give the tested signs for
`epsilon = +/-1`; for Dirichlet `delta h = 0`, the derived EH boundary density
cancels the actual exact-inverse GHY derivative. Arbitrary-coordinate
covariance and boundary integration remain open.

For arbitrary variable fluxes on a finite three-dimensional rectangular
lattice, a separate gate now proves exact telescoping from the bulk divergence
to all six oriented faces and cancellation by the matching boundary
counterterm, including two sectors.  The bulk, boundary and matched ledgers
are also realized as actual derivatives along arbitrary affine flux curves,
with the matched derivative equal to zero.  This is a discrete box Stokes
theorem, not a continuum manifold result or a construction of GHY, null,
joint or corner terms.

The compatibility gate now also has a genuinely Lorentzian finite model.
With explicit `eta = diag(-1,1,1,1)`, it proves nondegeneracy,
`K(F) = F^T eta F`, the actual Frechet derivative `J_F`, source and ambient
`eta`-isometry naturality, the exact infinitesimal `eta`-antisymmetric kernel
when `F` is an equivalence, and the nonzero-frequency symbol kernel as the
`eta`-orthogonal complement of `range F`. This remains pointwise and
finite-dimensional, not the global Janus PDE/jet complex.

The Gram--Saint-Venant symbol sequence is now exact for every nonzero
`xi : Fin 4 -> Real`, not only for the canonical time frequency.  An explicit
nonzero pivot reconstructs the vector variation from every symmetric tensor in
the Saint-Venant kernel; Lorentz lowering gives the same exact range.  This is
still pointwise symbol algebra, not a global differential complex, boundary
solvability theorem or compatibility PDE result.

Coefficientwise exactness is also proved for every mode in an arbitrary finite
family of nonzero Fourier frequencies, with finite support and an explicit
modewise reconstruction.  The zero mode, infinite-series convergence,
continuum PDE solvability and boundary conditions remain outside this gate.

A separate finite-mode gate now classifies the previously omitted zero modes.
Every symmetric compatible coefficient family has a unique decomposition into
a Lorentz--Gram image whose potential vanishes on the zero frequencies and a
symmetric coefficient family supported only on those frequencies.  The
residual projection is idempotent and gives the corresponding finite
cohomology representative.  This is a finite coefficientwise decomposition,
not an infinite-series convergence, boundary or global PDE theorem.

On the full `Z^4` lattice, these coefficients now also live in completed
weighted `ell^2` Hilbert spaces. The reconstruction is bounded, the compatible
zero-free symbol range is closed, and the zero mode is a bounded projection.
Because the Lorentz--Gram symbol has order one, a further gate equips the
source with its exact one-order graph-Sobolev weight. The normalized symbol is
then a bounded contraction into the target weighted metric space, and an exact
encoding theorem identifies it with the unnormalized physical symbol. On the
same completed spaces, the target identity pairing is a continuous positive
self-adjoint Hessian and its genuine adjoint pullback `J†J` is symmetric,
nonnegative and positive definite after the finite zero-mode kernel is removed.
The zero mode is now the range of a bounded idempotent projection; its closed
complement represents an actual normed quotient by `ker J`, via a continuous
linear equivalence, and the pullback Hessian is nondegenerate there.
This is a periodic coefficient-scale theorem, not yet the Hessian of the
nonlinear global action or a Sobolev-section theorem on the mapping-torus
bundles and their boundary conditions.

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
derivative specializes to it. This has now been globalized on the complete
fixed-frame diagonal Lorentz domain
`diag(-a₀,a₁,a₂,a₃), diag(-b₀,b₁,b₂,b₃)` with all magnitudes positive: the
domain is open, convex, connected and nonempty; the positive principal root
exists uniquely in the diagonal branch, is `C∞`, its Sylvester map has an
explicit inverse everywhere, and its full derivative contains both metric
variations including the inverse-plus term. This remains restricted to the
simultaneously diagonal fixed-frame sector, not the full causal-compatible
matrix domain. More generally in dimension four, a supplied
continuous square-root lift that remains pointwise Sylvester-regular agrees
locally with the corresponding IFT branches and is therefore differentiable
with the inverse-Sylvester derivative.  The continuous lift and regularity are
still hypotheses: this neither constructs the lift nor proves that an
admissible evolution avoids the Sylvester boundary.  A separate
unconditional construction around the independent Minkowski pair now gives
an explicit open inverse-function-chart domain for the actual relative metric
map.  Its selected root is continuous, squares exactly to the relative metric
at every point of that domain and is unique among roots that remain in the IFT
source.  This remains a local chart, not the global causal-compatible
principal-root domain.  A separate
two-dimensional boost orbit gives
coordinate off-diagonal entries, actual derivatives of `X(s)` and `X(s)^2`,
and their differentiated Sylvester identity.  The orbit remains Lorentz-
conjugate to the diagonal seed and the metric pair is reconstructed from the
chosen root; it is therefore not a genuinely non-co-diagonalizable branch or a
solution for independently supplied metrics.  A differentiable Lorentzian
root selection and Sylvester inverse on the full causal-compatible matrix
domain remain to be constructed.

At the independent Minkowski pair, the full Candidate-A density is now also
differentiated as one actual composite of the plus determinant measure, the
unconditional local relative-root branch and the complete matrix spectral
potential. The resulting Frechet covector and its value on two independent
symmetric metric variations are explicit, and the affine variation curve
remains on the exact root-square branch eventually. This closes the local
Minkowski chain, not the global two-sector functional variation.

The local result is no longer restricted to the base point. On every pair in
the explicit IFT target domain, the quantitative inverse-chart estimate keeps
the Sylvester map within a strict Neumann neighborhood of twice the identity.
This proves Sylvester invertibility and differentiability of the selected root
throughout the domain, then differentiates the determinant measure, complete
spectral potential and Candidate-A density there. Intersecting with the
exchanged domain gives a nonempty open PT-paired chart on which both sector
densities are differentiable and their sum is exactly invariant under metric
exchange. The chart remains local to the identity root; it is not the global
causal-compatible Lorentz domain.

That PT-paired density now defines an actual integral functional for fields
valued in the same open chart. A uniform admissible-curve contract keeps every
fiber inside the root domain, and an explicit measurable/integrable domination
contract justifies differentiation under the integral. Fiber exchange and a
measure-preserving PT involution preserve the functional, curve and first
variation. This specializes to the effective D8 spacetime for any supplied
PT-invariant Borel measure; neither such a measure nor domination is derived.

A separate two-dimensional null-coordinate family now supplies independently
defined symmetric nondegenerate Lorentz metrics whose relative matrix is a
nontrivial Jordan block.  For nonzero parameter that target is not real
diagonalizable, while an explicit root squares to it; actual target/root
derivatives and their Sylvester identity are proved.  This is one explicit
Jordan family, not a smooth principal-root selection on the full admissible
Lorentz domain.

A broader three-parameter null-coordinate chart now starts from independently
supplied two-dimensional Lorentz metrics and uses the Cayley--Hamilton formula
for a real square root.  On its explicit open inequalities the root squares to
the relative matrix, has positive determinant and trace, and varies
continuously at every chart point.  The chart includes diagonalizable and
Jordan points, but proves neither uniqueness nor a global or four-dimensional
principal branch.

On that same two-dimensional chart, the equal-diagonal root form now gives an
explicit two-sided inverse for the Sylvester operator.  The operator is
bijective, every target variation has a unique preimage, and differentiation
of `X^2 = A` identifies the derivative of any supplied differentiable root
curve, including a differentiable explicit-chart parameter curve, with that
inverse.  This is a chartwise two-dimensional
existence-and-uniqueness result, not a global four-dimensional Sylvester or
principal-root theorem.

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

A separate scalar first-jet density now couples a supplied gradient to an
inverse metric and explicit measure.  Its simultaneous measure, inverse-
metric, scalar and gradient affine variation is an actual derivative, with
coordinate-only corollaries for each slot and zero mixed response between two
independent matter blocks.  The scalar value/gradient and measure/inverse
metric are independent jet coordinates here: neither `delta p = d(delta phi)`
nor `delta sqrt(|g|)` is imposed, and no spacetime integral, covariant matter
PDE or stress tensor is derived.

The four-dimensional pointwise scalar gate now removes the metric shortcut:
on the open component `orientation * det(g) > 0`, one symmetric nondegenerate
metric supplies both the exact inverse of `g + t delta-g` and
`sqrt(|det(g + t delta-g)|)`.  Their actual derivatives give the constrained
scalar-density variation and the explicit symmetric stress tensor, with
`delta rho = -sqrt(|det g|)/2 <T,delta g>`.  The scalar value and covector
gradient are fixed pointwise; this is not yet `p = d phi`, a spacetime action,
a functional Euler variation, a covariant PDE or stress conservation.

A separate continuous flat-chart gate now removes the independent-gradient
shortcut for scalar-field variations. On `R^4`, the coordinate covector is the
actual Frechet derivative of the same differentiable field; an affine line in
the function space therefore varies `phi` and `d phi` together. The exact
pointwise density derivative lifts to an integral over an arbitrary measure
under explicit measurability, integrable-majorant and local-Lipschitz
hypotheses. The metric is fixed along this scalar variation, so this gate alone
does not provide simultaneous metric/holonomic variation, a curved-manifold
construction, integration by parts, a covariant PDE, a boundary theorem or
conservation.

A companion flat-chart gate closes the simultaneous variation. One parameter
varies the exact metric-induced determinant measure and inverse together with
the genuine scalar field and its `p = d phi` jet. Its derivative splits
exactly into the fixed-field metric-stress contribution and the fixed-metric
holonomic-field contribution, and its integral has that derivative under an
explicit dominated local-Lipschitz contract. At fixed metric, the holonomic
variation also decomposes pointwise into the flat scalar Euler operator plus
the divergence of an explicit boundary flux. The integrated flux is still a
named boundary condition. Under explicit integrability and that zero-flux
condition, the integrated first variation equals the weak Euler pairing, and
any already-justified action derivative acquires the same coefficient. The
flux is not automatically zero; curved covariance, a strong PDE and
conservation are not proved.

A finite periodic scalar model now closes the first of those two shortcuts in
a genuine holonomic setting: the gradient is induced from the field, its
variation is the gradient of the field variation, the action has an actual
line derivative, and discrete summation by parts gives the strong nearest-
neighbour Euler equation and its stationarity equivalence.  Two sectors retain
zero mixed response.  This remains a finite periodic network, not a continuum
covariant matter PDE, stress tensor or determinant-measure variation.

The periodic model is now also coupled to one positive metric coefficient:
the measure is `sqrt(g)`, the kinetic coefficient is `sqrt(g) / g`, and both
metric and holonomic scalar variations are derived from the same variables.
This removes the independent measure/inverse shortcut only in a finite
one-dimensional model; no four-dimensional covariant PDE or stress tensor is
obtained.

Under an arbitrary bijection of finite site sets, conjugating the periodic
shift and transporting the field now leaves this metric-holonomic action
unchanged.  Its simultaneous first variation and strong Euler field are
equivariant, and fixed-metric stationarity is preserved in both directions.
This is finite reindexing covariance, not a spacetime diffeomorphism or a
covariant density law.

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
EH/GHY reduction, ADM shift/functional bracket, generic rank and BD closure
remain open.

For any finite site set, the mixed smeared-primary bracket is also lifted to
an actual finite functional sum.  It equals the weighted sum of the reduced
secondaries, and supported test differentials localize the displayed primary
preservation equations site by site.  A `Fin 2` witness carries independent
local constraint covectors and separately fixed lapse ratios.  Jacobi is
proved only for affine constant-differential functionals; this ultralocal
model has no spatial derivatives, continuum ADM shift, hypersurface-
deformation algebra or nonlinear constraint-algebra closure theorem.

A separate canonical second-jet gate now proves the exact Poisson Jacobi
identity with arbitrary symmetric, potentially nonzero Hessians.  Quadratic
functionals realize those jets with actual line derivatives, including the
derivative of their Poisson bracket, so the result is genuinely nonlinear at
finite-jet level.  It is not yet instantiated by the Candidate-A constraints
and proves no continuum ADM or hypersurface-deformation closure.

The input-Hamiltonian caveat has now been narrowed. Starting from an explicit
spatially flat reduced Candidate-A Lagrangian, the velocity derivatives give
the canonical momenta, the regular momentum--velocity maps are inverse, the
common square-root interaction has the required lapse/volume normalization,
and the Legendre transform is exactly `N_plus C_plus + N_minus C_minus`.
The reduced kinetic Lagrangian itself is still supplied rather than derived
from the covariant EH/GHY action.

There is also a sharp rejection result on the selected vacuum PT-flat cone.
For positive scale factors, Planck coefficients and interaction scale with
`beta1 > 0`, `beta2 >= 0`, both primary constraints force
`a_plus = a_minus` and `p_plus = p_minus = 0`; at that point their covectors
are dependent. Therefore the unrestricted local rank witness cannot simply be
moved onto this vacuum flat branch. Matter, spatial curvature or a different
coefficient branch is required before attempting a generic constraint chain.

The reduced model now supplies one explicit matter-supported answer. Adding
fixed comoving dust energies and the standard scale-linear curvature terms
preserves the factorized primary bracket. At the flat witness
`a_plus = a_minus = p_plus = p_minus = 1` with positive dust
`rho_plus = rho_minus = 1/12`, both primaries and the dynamical secondary
vanish, the primary covectors are independent, and a three-constraint minor is
exactly `145/144`. Secondary preservation is
`(145/12) (N_plus - N_minus) = 0`, hence `N_minus = N_plus`. The witness uses
dust, not curvature; its source Hamiltonians remain reduced inputs and imply
no covariant matter, ADM or BD conclusion.

The constrained tangent audit is now exact at this witness. The common kernel
of the two primary covectors and the secondary covector is one-dimensional,
generated by `(2,1,2,1)`. The equal-lapse ambient Hamiltonian Hessian is
`-1/3` on that generator, but its affine line leaves the primary surface at
second order. The nonlinear curve
`a_plus = a_minus = (1+t)^2`, `p_plus = p_minus = 1+t` has the same tangent,
stays on all three constraints and gives zero constrained second variation.
Thus the negative ambient number is not a reduced stability or ghost verdict.

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

A separate finite-mode gate now introduces an actual heat-kernel regulator.
For nonnegative squared eigenvalues and nonnegative regulator time it computes
the finite Fujikawa-type chiral trace. An explicitly isospectral PT partner
with opposite chirality cancels that regulated trace at every time, while the
parity-even heat trace doubles; a one-zero-mode witness makes both statements
non-vacuous. The spectrum and PT partner are still supplied finite data: no
continuum Janus operator, heat-kernel asymptotic coefficient, local anomaly
density, global determinant-line holonomy or normalization law is derived.

The circle model now also has a genuine unbounded diagonal Dirac operator on
`l2(Z, C)` with its maximal weighted domain.  Finite Fourier modes prove the
domain dense; the graph characterization proves closedness, unit domain
vectors prove unboundedness, and the adjoint-domain calculation proves
self-adjointness.  Squaring this actual operator on each Fourier basis vector
now recovers the spectral eigenvalue square, and the resulting finite and
summable diagonal traces agree with the previous heat sums and PT
cancellations.  This is a basiswise spectral bridge, not a global construction
of `exp(-t D^2)` by functional calculus or a trace-class theorem.

A genuine bounded continuous diagonal heat operator on `l2(Z, C)` is now also
constructed for every nonnegative time.  It is contractive, equals the identity
at time zero, satisfies the semigroup law, and has the expected Fourier
multipliers and diagonal trace sums.  Strong continuity is now proved globally
for every state and at every nonnegative time, and differentiation of each
Fourier-basis orbit gives the expected `-lambda_n^2` generator action on that
dense basis. The strong right derivative on the full Hilbert space now exists
exactly on the squared-eigenvalue weighted domain, that domain equals the
actual iterated domain of `D ∘ D`, and the unique generator is `-D²`. Neither
the abstract functional-calculus exponential nor a general Mathlib
trace-class interface is available. However, at every positive time the same
operator is now the operator-norm sum of explicit rank-one Fourier maps with
summable norms, and its nuclear trace equals the spectral trace. The full
Janus Dirac operator, anomalies,
determinants and normalization remain open.

The same circle family now has its canonical bounded transform. It is an
operator-norm 1-Lipschitz self-adjoint Fredholm family of index zero. The exact
endpoint crossings are related by the large-gauge mode shift, PT reverses
their orientation, and the two physical quarter holonomies are bijective.
Its genuine pointwise determinant fibers have rank one and nonzero Fourier
frames, with a bijective large-gauge transition between endpoint fibers. No
topology is yet installed on their dependent union, so this does not construct
a Janus family index or Quillen line bundle.

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
- exact finite-matrix density weight `|det Q|` and inverse-Jacobian
  compensation under arbitrary invertible simultaneous frames;
- exact finite-site lift with independent simultaneous local frames,
  inverse-Jacobian coordinate weights and invariant weighted action sum;
- actual affine one-dimensional density pullback and Jacobian, whose variation
  is the total derivative `(xi rho)'`, with exact endpoint-ledger cancellation;
- actual local four-dimensional affine flow, Frechet Jacobian, determinant
  derivative `d det(I + epsilon A)/d epsilon|_0 = tr A`, density pullback and
  equality of its variation with the four-coordinate flux divergence;
- explicit flat Minkowski principal symbol of the linearized Einstein tensor,
  with finite-sum proofs of `k^mu G_mu_nu = 0` and annihilation of every
  linearized diffeomorphism direction;
- actual derivatives of metric inversion and `g_plus_inverse * g_minus`, plus
  an explicit two-sided Sylvester inverse on the open positive diagonal chart
  and a conditional derivative of a supplied differentiable square root;
- actual pointwise 4D scalar-density variation with determinant measure and
  exact inverse supplied by the same symmetric metric, together with its
  explicit symmetric stress tensor and stress-pairing identity, lifted to an
  arbitrary measured base and two sectors under explicit measurability,
  integrable-majorant and local-Lipschitz hypotheses, or an explicit uniform
  bound on the rebased derivative at every admissible parameter; the integrated
  action and stress variation are sector-exchange invariant. In that stress
  gate the gradient remains a fixed coordinate covector;
- on the continuous flat chart `R^4`, an actual differentiable scalar field
  supplies both its value and `p = d phi`; its affine function-space variation
  has exact pointwise and integrated derivatives under an explicit dominated
  local-Lipschitz contract. A simultaneous metric/field curve also
  uses the same metric for measure/inverse and the same field for `p = d phi`,
  with an exact stress-plus-field split and an integrated derivative under the
  same kind of explicit contract. Its fixed-metric holonomic contribution is
  pointwise Euler plus flux divergence and becomes the weak Euler pairing after
  explicit integrability and zero-integrated-flux hypotheses. Curved-manifold
  covariance, derivation of flux cancellation from boundary data, a strong
  PDE, conservation and automatic domination are not claimed;
- an unconditional local four-dimensional relative-root branch around the
  independent diagonal Minkowski metric pair, obtained by composing the
  identity-root IFT branch with the actual map
  `(g_plus,g_minus) -> g_plus^-1 g_minus`; its full pair derivative includes
  metric inversion and the half-Sylvester inverse, and its square is the
  relative metric throughout a neighbourhood. No global, principal or
  Lorentz-causal selection follows from this local result;
- conditional gluing of the local four-dimensional IFT roots along a supplied
  continuous square-root lift with pointwise Sylvester equivalences, which
  removes a separate differentiability assumption but not the lift or
  regularity hypotheses;
- explicit co-diagonal Lorentz metric pairs with shared signature, positive
  root, determinant, diagonal-root uniqueness and Sylvester witness, together
  with actual metric/inverse/target/root Frechet derivatives on the open
  positive scale chart and an internally proved differentiated square identity;
- a coordinate off-diagonal two-dimensional Lorentz-boost orbit with symmetric
  nondegenerate reconstructed metrics, actual root/target derivatives and the
  Sylvester identity; the orbit remains conjugate to its diagonal seed;
- an independent two-dimensional Lorentz-metric Jordan family with a
  non-diagonalizable relative matrix for nonzero parameter, an explicit square
  root, actual derivatives and the differentiated Sylvester identity;
- a continuous three-parameter two-dimensional Lorentz chart for independently
  supplied metrics, with an explicit Cayley--Hamilton root covering
  diagonalizable and Jordan points, together with an explicit bijective
  Sylvester operator, its two-sided inverse, unique solution for every target
  variation and the chart-root derivative identity; no global or
  four-dimensional root theorem is claimed;
- genuine Frechet derivative of the full co-diagonal Candidate-A interaction
  density, including determinant/absolute-value/square-root measure and the
  five-coefficient spectral potential, rewritten through the Sylvester inverse;
- explicit pointwise EH-stratum ledger plus a generic supplied-measure
  worldvolume placeholder;
- exact fixed-geometry affine variations of selected boundary/worldvolume
  slots;
- exact non-null GHY pointwise first jet, including the determinant-derived
  measure tangent and the linearized inverse-metric contribution;
- actual local inverse-compatible non-null GHY curve, followed by
  `K(t) = tr(h(t)^{-1} B(t))` and a complete density derivative with no
  supplied scalar `delta K` or measure tangent;
- derived Gaussian-normal Palatini/EH boundary flux and its exact pointwise
  cancellation with GHY for Dirichlet variations, with both orientation signs;
- explicit embedded `n = 0` hypersurface in an affine Gaussian-normal chart,
  with two-sided surface inverse, actual coordinate metric derivatives,
  Levi-Civita Christoffels, signed unit normal, orthogonality, and derived
  `B_ab = sigma partial_n h_ab / 2` and `K = h^{ab} B_ab`;
- genuine threefold interval integration of the constant affine EH
  boundary-flux and exact GHY first-variation densities on a compact
  tangential box, including integrability,
  orientation cases and two-sector cancellation;
- exact finite-box Stokes telescoping for arbitrary variable three-dimensional
  fluxes, all six oriented faces and the cancelling boundary counterterm,
  promoted to actual bulk, boundary and matched action derivatives;
- actual nonzero-expansion null-counterterm derivative and its explicit
  singular approach to zero expansion, plus continuity but proved
  non-differentiability of its zero extension;
- actual null-generator product derivative and exact face/joint endpoint
  transgression cancellation in the typed one-dimensional ledger;
- actual pointwise LL auxiliary-metric, measure and flux variations, the
  symmetric auxiliary stress/measure equations and a conditional nonzero
  induced-metric null kernel;
- affine auxiliary scalars whose `3 x 3` Jacobian gives the signed composite
  LL measure, with actual line derivatives, coordinate-density compensation
  and a nondegenerate first-jet witness, plus its genuine Frobenius-space
  Frechet derivative at arbitrary, including singular, jets;
- exact local two-sector bulk/GHY cancellation and a nonzero mismatch
  residual;
- finite Gram-tensor map, its actual first and second derivatives, positivity
  on the injective immersion domain, and the associated concrete finite
  compatibility map and Jacobian;
- first-jet naturality of `K` and its actual `J` under source-frame changes and
  ambient isometries, with ambient infinitesimal isometries in `ker J`;
- explicit finite principal symbol: for nonzero covector its kernel is exactly
  the ambient normal space to `range F`, and it is injective in codimension
  zero when `F` is surjective;
- explicit Minkowski `eta`, Lorentzian Gram `K/J`, source/isometry naturality,
  exact infinitesimal kernel for equivalent `F`, and Lorentz-orthogonal symbol
  kernel with injectivity under surjectivity;
- arbitrary nonzero-frequency strain/Gram--Saint-Venant symbol sequence, with
  zero composition, injective Lorentzian Gram symbol, explicit pivot
  reconstruction and exact symmetric-kernel range;
- coefficientwise Gram--Saint-Venant exactness and reconstruction on arbitrary
  finite families of nonzero Fourier modes, followed by a unique normalized
  Gram-image plus symmetric zero-mode-residual decomposition and its finite
  cohomology characterization; no infinite-series convergence, PDE or boundary
  result is claimed;
- exact classification of additive reduced scale translation; relating it to
  the covariant diagonal diffeomorphism remains a separate bridge;
- exact FLRW lapse affinity and primary-constraint precursors, plus reduced
  bracket factorization and an unrestricted-parameter local Dirac-chain
  witness for the secondary constraint and lapse ratio;
- finite-site ultralocal functional sums with actual line derivatives, mixed
  primary bracket equal to the sum of local secondaries, localized primary
  preservation and a two-site witness; no nonlinear closure is claimed;
- exact canonical Poisson Jacobi at nonlinear second-jet level for arbitrary
  symmetric Hessians, with actual quadratic-functional and bracket
  derivatives; no Candidate-A constraint or continuum ADM closure is claimed;
- actual reduced velocity derivatives, regular Legendre inversion and exact
  derivation of those Hamiltonian constraints from the displayed FLRW
  Lagrangian;
- PT-flat vacuum no-go: simultaneous primary constraints collapse to the
  symmetric static point where their covectors are dependent;
- explicit positive-dust PT-flat witness with both primary constraints and the
  secondary zero, independent primary covectors, nonzero three-constraint
  minor and secondary preservation fixing `N_minus = N_plus`;
- exact one-dimensional constrained tangent at that dust witness; its negative
  ambient Hessian is separated from the zero second variation along an exact
  nonlinear constraint curve, preventing a false stability/ghost verdict;
- exact diagonal/relative source decomposition as a PPN rejection precursor;
- reduced PT-signed source bridge: positive Candidate-A matter Hessian,
  opposite pure-relative sources, a positive mediator cross term and the full
  Janus sign table alongside two positive spin-2 kinetic coefficients; the
  charge law remains imported reduced input rather than a covariant result;
- actual pointwise Euler equations and symmetric full Hessian for the spectral
  interaction plus two independent quadratic matter blocks;
- actual pointwise first-jet scalar density variation in independent measure,
  inverse-metric, scalar and gradient coordinate slots, with two matter blocks
  of zero mixed response;
- an actual continuous flat-chart scalar-field variation on `R^4`, where the
  same differentiable field supplies its value and coordinate covector
  `p = d phi`, with exact pointwise and integrated derivatives under an
  explicit dominated local-Lipschitz contract;
- an actual simultaneous flat-chart metric/holonomic-field
  variation, tying measure/inverse and value/`p = d phi` to the same objects
  and splitting exactly into stress and field contributions, with an
  integrated derivative under an explicit dominated contract and a pointwise
  flat Euler-plus-boundary-divergence decomposition; under explicit
  integrability and zero-flux assumptions its integrated variation is the weak
  Euler pairing;
- an actual finite periodic holonomic scalar variation, discrete summation by
  parts, strong nearest-neighbour Euler equation, stationarity equivalence and
  zero mixed response between two sectors;
- a positive one-dimensional metric version of that finite periodic model,
  with induced `sqrt(g)` measure, inverse weight and simultaneous metric/scalar
  variation, whose action, first variation, strong Euler field and stationarity
  are invariant or equivariant under arbitrary finite-site bijections;
- explicit Candidate-A witnesses proving that the paired anomaly proxy fixes
  neither overall normalization nor the reduced finite even-counterterm proxy;
- actual finite-mode heat-kernel chiral trace with typed nonnegative spectrum
  and time, exact PT cancellation, parity-even doubling and a nonzero witness;
- countable supplied spectrum with exact cancellation at every finite cutoff,
  convergence of the paired cutoff sequence to zero, and, under explicit
  summability, convergence to a well-defined cancelling infinite trace;
- explicit circle Fourier spectrum `lambda_n = n + a`, diagonal algebraic
  Dirac action, derived PT-isospectral squares, proved Gaussian summability on
  both integer tails, symmetric-cutoff convergence and finite/infinite chiral
  cancellation;
- a densely defined closed, unbounded and self-adjoint circle Fourier Dirac
  operator on its maximal weighted `l2` domain;
- a basiswise bridge from its actual square `D^2` to the finite and summable
  diagonal heat traces; no global functional-calculus construction is claimed;
- a genuine bounded contractive diagonal circle heat operator, with identity,
  semigroup law, global strong continuity, the expected diagonal trace sums and
  the expected generator derivative on the dense Fourier basis, plus exact
  equality of its maximal strong generator domain with the iterated `D²`
  domain on the full Hilbert space, plus an operator-norm-convergent nuclear
  rank-one expansion at every positive time whose trace is the spectral heat
  trace; equality with the abstract functional-calculus exponential and a
  general trace-class API are open;
- an exact bridge from the quarter-twisted Program-P circle operator to the two
  PT-related D7 root towers, compactness of every fixed sphere-level heat block,
  and an explicit common-counterterm renormalized determinant certificate for
  both physical `Z4` roots;
- an infinite monopole heat trace, an order-four Euler--Maclaurin formula with
  uniform integral remainder control, and an unconditional small-time proof of
  the exact spectral/universal product coefficients `a0/a2/a4`.

Still required before Candidate A is a completed Janus action:

1. extend the co-diagonal root, its coordinate off-diagonal boost orbit, the
   independent non-diagonalizable Jordan witness and the continuous
   three-parameter two-dimensional Cayley--Hamilton chart with its explicit
   bijective Sylvester inverse and derivative identity,
   together with the full interaction-density Frechet derivative, to a smooth
   unique real principal square-root branch on the full admissible
   four-dimensional Lorentz field domain, lift the finite density weight to the
   manifold transformation law and control branch changes;
2. lift the finite positive-metric periodic model, where `sqrt(g)` and `g^-1`
   are already tied to one metric and finite-site reindexing covariance is
   proved, to four-dimensional holonomic matter fields;
   then derive the covariant metric and spacetime matter Euler--Lagrange PDEs
   and stress tensor from `S_A`;
3. lift the Gaussian-normal Palatini calculation to arbitrary coordinates,
   lift the explicit local embedded Gaussian chart and its `h/B/K` data to a
   geometric boundary curve on the manifold, extend the constant-box
   boundary-flux/first-variation integral to variable geometric data, beyond
   the finite variable-flux six-face Stokes theorem, and
   integrate all gravitational strata, select an admissible zero-expansion
   variational domain, lift the affine composite LL measure and pointwise
   auxiliary action to global fields and worldvolume PDEs, establish a
   nonempty throat branch, and prove cancellation of the physical bulk flux;
4. extend the finite zero-mode cohomology decomposition through infinite-series
   convergence and boundary analysis to the global Lorentzian compatibility
   differential/PDE complex, and lift the local affine density identity and
   flat linearized Einstein-symbol Bianchi theorem to arbitrary diagonal
   diffeomorphisms and the nonlinear curved Candidate-A metric/matter
   Noether--Bianchi identity;
5. derive the reduced PT-signed charge law and resulting Janus Newtonian sign
   matrix from the covariant Candidate-A weak-field equations while retaining
   positive spin-2 kinetic terms;
6. derive the displayed reduced kinetic Lagrangian and dust source from the
   covariant Candidate-A EH/GHY/matter action, extend the explicit
   dust-supported branch, finite ultralocal bracket and nonlinear canonical
   second-jet Jacobi gate to the actual Candidate-A constraints and continuum
   ADM shift/spatial-derivative bracket with generic independent secondary-
   constraint closure; then derive constrained
   stability on the physical reduced tangent/quotient and PPN parameters for
   the exact matter couplings;
7. extend the self-adjoint unbounded circle Fourier operator to the full Janus Dirac
   operator, identify the constructed contractive diagonal heat-semigroup
   generator on its maximal domain and the semigroup with the abstract
   functional calculus of `D^2`, prove the required trace-class statements,
   construct the smooth Fredholm/Quillen family, compute local/global anomalies
   and supply a microscopic normalization/finite-part law in the same scheme.

Candidate A is rejected if any of items 1--7 fails.  No observed-radius input
is used in its definition.

## Six-lock checkpoint

| Lock | Implemented now | Remaining rejection test |
| --- | --- | --- |
| 1. Cross densities | explicit reciprocal pair, one common interaction, spectral Frechet data, actual metric-inverse/relative-product derivatives, first Frechet derivative of the co-diagonal root, coordinate off-diagonal boost orbit still conjugate to its diagonal seed, an independent non-diagonalizable Lorentz Jordan family, a continuous three-parameter two-dimensional Cayley--Hamilton root chart with an explicit bijective Sylvester inverse, an unconditional relative-root branch on an explicit open IFT target domain with continuity, exact square, chart-source uniqueness and pointwise Sylvester invertibility/differentiability everywhere, complete Candidate-A determinant/root/potential variation throughout that domain and on its PT-paired exchanged intersection, conditional gluing along any supplied continuous Sylvester-regular four-dimensional root lift, genuine Frechet derivative of the full co-diagonal Candidate-A density through the Sylvester inverse, and exact finite-frame density weight | extension of the identity-root chart, or construction of a compatible lift with proved Sylvester regularity, to a unique global causal-compatible four-dimensional Lorentz domain, plus global functional variation there |
| 2. Fields/induced/gauge | independent field choice, parametrized global configuration package instantiated on the same effective D8 quotient bases/PT actions/equivariant throat inclusion; concrete continuity predicates for every independent, induced and LL coordinate; a nonempty continuous PT-matched Minkowski/identity-root configuration on those same objects; simultaneous-frame invariance/counterexample, constructed matrix covector, invariant finite-site action, actual affine 1D and local affine `R^4` density pullbacks, independent scalar first-jet coordinate slots, a pointwise 4D scalar metric variation with one determinant measure/exact inverse and explicit symmetric stress tensor, its integrated one/two-sector lift on an arbitrary measured base under explicit contracts with exchange invariance, a continuous flat-chart holonomic scalar variation with `p = d phi`, its simultaneous metric/holonomic extension integrated under an explicit dominated contract with exact stress-plus-field split and conditional weak Euler pairing, a finite periodic holonomic scalar Euler model, and its positive one-dimensional metric version with induced `sqrt(g)` measure, inverse weight and action/variation/Euler/stationarity covariance under finite-site bijections | smooth manifold/tensor and Sobolev or smooth function spaces with boundary conditions, global root map, stationarity/stability, discharge of the integration contract and derivation of zero flux from boundary data, covariant matter PDE/stress conservation, arbitrary spacetime diagonal diffeomorphisms and covariant density law |
| 3. Bulk/boundary/worldvolume | typed ledger, exact inverse-compatible GHY curve with `K=tr(h⁻¹B)` and no supplied `delta K`, derived Gaussian-normal EH cancellation, explicit local embedded hypersurface/unit normal/Levi-Civita `B` and `K`, actual threefold integration of constant EH/GHY densities, exact finite-box Stokes for variable fluxes and six faces with actual matched-action derivative, null zero-extension audit, null/joint transgression, pointwise LL action and affine composite measure | arbitrary-coordinate global embedding and variable-field continuum flux, physical GHY/null/joint/corner completion, admissible zero-expansion domain, global LL fields/PDEs/throat and full stratum integration |
| 4. Concrete `K/J` | Euclidean and explicit Minkowski Gram `K/J`, source/ambient naturality, exact infinitesimal gauge kernels, finite principal-symbol kernels, Gram--Saint-Venant exactness at every nonzero 4D frequency, coefficientwise exactness for finite nonzero Fourier families, and unique normalized decomposition with a finite zero-mode cohomology residual | boundary analysis, infinite-series convergence, and the global Lorentzian Janus compatibility differential/PDE complex |
| 5. Euler/Helmholtz/Noether | actual spectral-plus-matter Euler/Hessian/Helmholtz, independent metric-coupled scalar first-jet variation, pointwise 4D determinant/inverse-constrained scalar stress variation, integrated one/two-sector stress variation under an explicit dominated-differentiation contract and exchange invariance, continuous flat-chart holonomic scalar first variation and simultaneous metric/holonomic split integrated under an explicit contract, pointwise flat scalar Euler-plus-flux-divergence decomposition and integrated weak Euler identity under explicit integrability/zero-flux assumptions, finite periodic holonomic scalar Euler equation and positive-metric `sqrt(g)`/inverse variation, finite-frame density identities, flat linearized Einstein Bianchi/gauge symbol, reduced signed-charge/Newtonian bridge, reduced Legendre/Dirac chain, finite-site ultralocal primary bracket/localization, nonlinear canonical second-jet Jacobi, PT-flat vacuum no-go and dust-supported witnesses | nonlinear curved Candidate-A metric/matter PDEs, discharge of domination and derivation of zero flux from physical boundary conditions, nonlinear Bianchi/stress conservation, covariant signed charge, dust reduction, actual constraint second jets and continuum ADM closure |
| 6. Stability/scheme | spectral indefiniteness, source-mode precursor, constrained dust tangent audit, scheme-freedom no-go, finite/countable heat traces, explicit circle Fourier Gaussian summability/cutoff/PT cancellation, a dense closed unbounded self-adjoint circle Dirac operator, a basiswise `D^2`-to-trace bridge, a contractive diagonal heat semigroup whose maximal strong generator domain is exactly the iterated `D²` domain and which has a summable rank-one nuclear expansion at positive time, compact D7 level blocks, convergent physical `Z4` determinants, order-four Euler--Maclaurin remainder control and unconditional spectral/universal `a0/a2/a4` small-time matching | physical quotient stability, PPN, covariant counterterms, abstract `D^2` functional calculus/general trace-class API, full Janus Dirac/Fredholm/Quillen family, local/global anomalies and microscopic normalization/finite-part law |
