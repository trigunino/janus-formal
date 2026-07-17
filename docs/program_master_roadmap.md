# Janus Formal — Master Roadmap

## Purpose

This document is the detailed dependency map for the current fundamental-geometry and variational programs. For merge state, CI truth and a concise scientific summary, read [`current_status.md`](current_status.md) first.

The repository does **not** currently claim:

- a complete global Janus geometry;
- a unique field content or action;
- a scheme-independent stable quantum vacuum;
- an absolute no-fit prediction of the Janus scale.

## Evidence labels

| Label | Meaning |
| --- | --- |
| **T** | theorem or exact algebra checked in Lean |
| **X** | executable Python/symbolic audit |
| **C** | conditional theorem from explicit assumptions |
| **I** | analytic/geometric theorem represented by an interface |
| **N** | no-go result or correction |
| **O** | open theorem or construction |

## Complete dependency graph

```text
Program D — geometry, bundles and operators
├── D0/D8  mapping torus, one-sided throat, analytic normal line bundle and quarter lift
├── D2     focused twisted-Dirac spectral geometry
├── D7     heat kernel, winding determinants and scale no-go results
├── D9     gauge-fixed elliptic-symbol / BRST gate collection
├── D10    determinant-line, Quillen and anomaly interfaces
└── D11    natural bundles, symbols and finite-jet interfaces
          ↓
Program P — action selection and reconstruction
├── P0     moduli-geometry no-go
├── P-A    relative universal property / parent-bulk reduction
├── P-B    anomaly consistency and discrete selection
├── P-C    Helmholtz inverse variational problem
├── P-D    pointwise invariant pairings and global coefficient modules
├── P-E    finite jets, adapted frames, oriented overlaps and SpinC lifts
└── P-F    compatibility-map pullbacks, Helmholtz and Noether identities
          ↓
Programs A/B/C — quantum scale, nonlinear junction, charge compatibility
          ↓
Program E — observational falsification
```

The ordering is logical, not chronological. P-B and P-C are independent filters; P-A may supply the Euler family used by P-C; P-E supplies the local operator/jet category and its structured symmetry data; P-D classifies pointwise pairing shapes together with their invariant coefficient module; P-F explains one route by which compatibility geometry can inherit a variational pairing.

# Program D

## D0/D8 — Global geometry and normal lift

- **T/C** compact fundamental strips project continuously and surjectively onto the actual smooth spacetime and throat mapping-torus quotients, so both are compact;
- **T/C** smooth coefficient fields on the quotient and throat form real vector spaces, admit smooth PT-equivariant throat restriction, and embed into completed `L²` spaces for finite Borel measures; PT is an involutive `L²` isometry for PT-preserving measures;
- **T/C** a finite global smooth tangent-generating family feeds a complete first-jet graph `H¹`; uniform coefficient/mass bounds and holonomic coercivity are automatic, and a geometric frame-control contract implies the static energy-to-graph bridge. The differential normal has an exact total-space `Diffeomorph` and strata; exact finite-frame normal reconstruction is proved, and compact uniform coefficient/integrability control follows from the remaining tangent-lift continuity predicate. Physical coarea, intrinsic Sobolev identification and Lorentzian null/joint strata remain open.
- **T/C** arbitrary smooth inclusion-preserving diagonal diffeomorphisms act on all global coefficient sectors with exact pullback laws and natural throat trace; smooth orbits have a manifold tangent generator;
- **T/C** the compact throat carries an actual finite-measure LL worldvolume action, a nonempty zero branch and exact PT covariance of its action/variation/Euler data; the null counterterm has the explicit open admissible variation domain `Theta ≠ 0`.

Candidate:

```text
J(T,rho) = (S3 x R)/((x,u) ~ (rho(x),u+T)),
Sigma ~ S2 x S1.
```

Current results:

- **T** the effective orbit quotient of `S3 x R` by the combined integer
  monodromy/translation is constructed; the action is free and properly
  discontinuous, and the quotient projection is a covering map;
- **T** the spacetime and throat quotients carry installed analytic
  `ChartedSpace` and `IsManifold` instances, and their covering projections
  are analytic local diffeomorphisms;
- **T** the equatorial `S2` inclusion is continuous and injective on the cover,
  equivariant, and induces a continuous injective map of effective quotients;
- **T** cover-coordinate time reversal descends to a continuous involution on
  the effective mapping torus and its fixed throat, and the quotient throat
  inclusion is equivariant for those same two involutions;
- **T** the associated normal line is an explicit topological orbit quotient
  with continuous projection, zero section and sign monodromy;
- **T** the even-winding quotient of the fixed throat is an actual two-sheeted
  topological covering: its deck involution is free, every fiber has two
  elements, and the pulled-back normal line is globally homeomorphic to the
  product with `R`;
- **T** the exact local-section sign cocycle constructs a genuine analytic
  real rank-one `VectorBundle` on the effective throat; one circuit acts by
  `-id`; its fibers are assembled into a global base-preserving algebraic
  equivalence with the dependent differential normal family;
- **T** transporting through that equivalence installs on the differential
  normal total space the exact quotient-fiber topology, local trivializations,
  `FiberBundle`, `VectorBundle` and analytic `ContMDiffVectorBundle` structures;
  the total comparison is a base-preserving homeomorphism with the same sign
  transition cocycle;
- **T** the equatorial complement in the concrete unit `S3` is exactly two
  nonempty disjoint open sign sides; reflection and one deck iterate exchange
  them, while the image of either side is exactly the full effective-throat
  complement and PT preserves that quotient complement;
- **T/N** the throat inclusion is a global `IsSmoothEmbedding`; the analytic
  differential-normal bundle and its exact fiber-linear total `Diffeomorph`
  comparison are installed. Its zero section is an analytic embedding with
  closed image and open nonzero complement; Lorentzian null/non-null/joint
  strata still require quadratic data absent from the real normal line;
- **T/C** the twisted generator squares to translation by `2T`;
- **T/N** nonzero translation is incompatible with a local fixed point of the same generator;
- **N** the constructed object is a free analytic mapping-torus manifold, not
  a singular orbifold;
- **N** expected `pi_1` is `Z`, not `Z4`;
- **T/C** the normal clutching sign is `-1`, its doubled pullback is trivial, and the two complex square roots are `+i` and `-i`;
- **T/C** the associated sign representation identifies the orientation cover with the even-winding kernel and proves pulled-back `w1 = 0`;
- **T/C** the integer deck action on the normal-line cover satisfies the identity and composition laws;
- **T/C** the two `Z4` lifts obey the cyclic cocycle law, are exchanged by PT, and reproduce the one-, two- and four-loop boundary-condition hierarchy;
- **T/C** both lifts now define genuine global complex line bundles whose smooth real underliers have analytic transitions, whose squares recover the normal sign for every winding, and whose full cocycles are exchanged by involutive real-linear complex conjugation;
- **T/C** the same integer cocycle defines a genuine topological principal normal `Pin⁻(1) ≃ Z4` bundle: its right action is free and transitive, transitions are equivariant, one loop is the order-four generator and reduction modulo two recovers orientation parity;
- **T/C** applying the two quarter characters to that principal cocycle gives
  actual associated root-phase bundle cores; their characters square to the
  orientation half-turn for every winding and PT exchanges them;
- **T/C** the actual quotient charts give real ambient tangent transitions,
  invertible differentials, nonzero determinants and the exact `ZMod 2`
  orientation parity cocycle;
- **T/C** an explicit positive nondegenerate real quadratic form on the 4D
  cover model transports across every tangent transition with a genuine
  `QuadraticForm.IsometryEquiv`; global orthonormal compatibility remains a
  separate contract;
- **T/C** the Clifford `spinGroup` now acts faithfully on ambient vectors and
  gives a multiplicative quadratic-preserving projection `Spin(Q) →* GL(4)`;
  finite-dimensional reflection generation and determinant parity now prove
  unconditional `Spin(4) → SO(4)` surjectivity and provide a lifting function.
  The twisted Pin extension is isolated exactly, while coherent smooth atlas
  transition lifts and their Čech cocycle remain open;
- **C** a P-independent topology ledger separates Spin/PinC existence, lift classification, cocycle, monodromy and lifted boundary conditions;
- **N** a real codimension-one line does not itself carry a literal quarter-turn;
- **N** a square-root line or `Z4` lift is extra global structure, not a canonical functor of the underlying line;
- **O** construct atlas-specific Spin/Pin transition lifts and their Čech
  cocycle, compare them with the normal lift, then extend to SpinC.

## D2 — Focused twisted Dirac spectral geometry

Focused head:

```text
lake build JanusFormal.Branches.FundamentalGeometryDiracSpectral
```

Current results:

- **T/C/X** monopole-spectrum arithmetic and product pairing;
- **T/C** an explicit separated product-mode model gives a positive spectral gap and PT invariance of the squared spectrum;
- **T/C** finite Hilbert truncations now have a proved symmetric diagonal Dirac action, nonnegative square and explicit two-sided resolvent away from the finite spectrum;
- **T/C** the separated modes now generate an actual complete real `l2` Hilbert space; the maximal weighted diagonal operator is densely defined, linear, formally symmetric and closed, while its finite-mode span is dense and contained in every weighted domain;
- **T/C** after complexification, both `(D-i)^{-1}` and `(D+i)^{-1}` are explicit mode multipliers; dense domain, formal symmetry and surjectivity of both non-real shifts are assembled into a concrete von Neumann self-adjointness certificate;
- **T/C** properness of the diagonal eigenvalue weight is proved sufficient for every nonzero superlevel set of the `(D-i)^{-1}` multiplier to be finite, isolating the exact compact-resolvent growth obligation;
- **T/C** bounded mode boxes are finite, coercivity implies spectral properness, and every finite diagonal resolvent truncation is now an actual Mathlib `IsCompactOperator` built from compact coordinate rank-one maps;
- **T/C** the truncations converge in operator norm whenever the multiplier vanishes at infinity; closedness of compact operators therefore promotes the full diagonal `(D-i)^{-1}` to an actual `IsCompactOperator` under spectral properness;
- **T/C** the explicit product eigenvalue `sqrt(lambda_S2^2 + lambda_S1^2)` is coercive in both the sphere level and circle mode; its bounded windows are finite and its full separated D2 resolvent is proved compact without a remaining analytic hypothesis;
- **T/C** finite-cutoff log determinants, a holonomy-independent local subtraction, the positive renormalized determinant and fixed-scheme uniqueness are formalized; compact resolvent is fed directly into the closure certificate;
- **I/O** the sole remaining determinant input is existence/convergence of one common local subtraction for the full holonomy family; compact resolvent alone does not imply that stronger zeta/heat-kernel statement;
- **T/C** eta/holonomy relations and primitive-sector gap laws;
- **T/N** correction: `1/(2*sqrt(2))` is a compact-circle/sphere ratio, not `alpha/L_sphere`;
- **C** primitive compatibility can give `A=L_sphere` under the declared LL/bimetric inputs;
- **N** a common metric scale orbit survives;
- **O** construct the actual self-adjoint global operator, prove the spectrum/eta analytically and compute the full determinant.

Last focused CI: **green**.

## D7 — Heat kernel and effective action

- **T/C** an abstract P-independent Dirac/PT package proves spectral pairing `lambda <-> -lambda` from PT anticommutation;
- **C** principal symbol, formal self-adjointness and global Fredholm realization are separated into explicit hypotheses, including domain, elliptic boundary condition and compact resolvent;
- **C** a consolidated analytic certificate transports Sobolev-domain, Green-formula, self-adjointness and compact-resolvent inputs into the Fredholm ledger;
- **C** an explicit D2-to-D7 bridge maps completed separated-mode obligations into that certificate;
- **T/C** the product-throat `a0/a2/a4` coefficients now generate an explicit cubic/linear/inverse cutoff subtraction, manifestly independent of holonomy;
- **T/C** a D7 heat-remainder family maps directly to the D2 renormalized determinant, and fixed heat coefficients give a unique determinant;
- **T/C** the monopole sphere law `lambda_n^2 = n(n+|q|)/L^2`, with multiplicity `|q|+2n`, is integrated into the separated operator and determinant cutoff; the already zeta-regularized circle product is counted exactly once;
- **T/C** the cutoff remainder is an exact telescoping sum of shell increments; summable increments imply convergence, and either a uniform geometric bound or the expected `C/(N+1)^2` bound constructs the full renormalized family and closes the D2 determinant certificate;
- **T/C** in the physical `Z4` root sectors, the exact spectral subtraction leaves `(|q|+2n) log(1+exp(-2 beta lambda_n))`; it is explicitly dominated by a polynomially weighted geometric series, hence both quarter-root determinants converge and agree by PT;
- **T/C** the infinite monopole-sphere heat trace is constructed as an actual `tsum`; for every positive heat time its terms are dominated by the same polynomially weighted geometric mechanism;
- **T/C** Euler--Maclaurin boundary jets give the spectral coefficients `2`, `-1/3`, `(5*q^2-1)/30`; after the circle factor these match the universal product-throat `a0/a2/a4` formulas exactly;
- **T/X** local heat-kernel coefficients for the declared product-throat convention;
- **T/N** finite local truncations are affine in the circle modulus and cannot isolate a minimum;
- **T/X** local/nonlocal winding separation and quarter-phase cancellation structure;
- **N** pure and PT-paired quarter determinants do not stabilize the modulus;
- **N** a finite local coefficient can fit a chosen target and therefore is not predictive unless derived;
- **T/C** the order-four Euler--Maclaurin remainder is controlled uniformly by
  an integrable fifth derivative, so the spectral/universal `a0/a2/a4`
  small-time correspondence is unconditional. Field/ghost weights and the
  final vacuum remain downstream of P.

## D9 — Elliptic and BRST symbol gates

Supported head:

```text
lake build JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex
```

The consolidated P-independent foundation contains:

- tangent/normal immersion splitting;
- de Rham and Maxwell symbols;
- metric/de Donder and diffeomorphism-ghost symbols;
- normal Jacobi symbol;
- abstract Clifford/Dirac symbol;
- linear BRST and gauge-fixed block models.

These form a supported algebraic symbol/linear-BRST head. They are not yet a
global Fredholm complex on the Janus throat: the action, Hessian, global domains,
zero-mode cohomology and nonlinear BV closure remain explicit obligations.

## D10 — Determinant line and anomalies

- **N** Quillen/Bismut–Freed is canonical only relative to a specified smooth Fredholm family;
- **N** determinant-line data do not choose field content, domains, finite counterterms or the scalar effective action;
- **T/C** additive transgression preserves stacking and opposite bulk inflow cancels the boundary anomaly class;
- **T/C** the explicit D2 PT mode family has cancelling `Z4` anomaly phases and an opposite-inflow relative class;
- **T/C** a symmetric finite Fourier family is holomorphic entrywise,
  algebraically Fredholm of index zero, induces an actual rank-one
  top-exterior determinant-line section, is PT covariant and is invertible at
  both quarter holonomies;
- **T/C** the explicit P--D7--D10 bridge combines compact fixed-level heat
  blocks, the convergent physical-`Z4` spectral determinant, equality of the PT
  renormalized logarithms and modewise opposite-inflow cancellation;
- **I/O** the finite-mode line and spectral bridge are not the global unbounded
  Janus Fredholm family, eta holonomy or Quillen partition section; construct
  those objects with the common regulator, physical Hessian and complete
  field/ghost content.

## D11 — Natural operators

Supported head:

```text
lake build JanusFormal.Branches.FundamentalGeometryD11NaturalImmersionOperators
```

The consolidated head formalizes:

- an abstract category of decorated immersions;
- natural bundle/section functors;
- natural operator and jet interfaces;
- principal-symbol composition/product closure;
- lower-order nonuniqueness;
- relative bridges to Quillen;
- a concrete one-object cyclic immersion groupoid with integer morphisms and functorial `Z4` jet monodromy.

The concrete Janus category, global structured jet groupoid, regularity hypotheses, descent theorem and invariant-theory classification remain open.

# Program P

Exhaustive closure checklist:
[`program_p_exhaustive_todo.md`](program_p_exhaustive_todo.md).

## P0 — Moduli-geometry no-go

- **T/N** the same metric supports different potentials and gradients;
- **T/N** the same symplectic form supports different Hamiltonians;
- **N** a Kähler-like package does not select a moment map or action.

## P-A — Relative action selection

- **T** a quadratic Hessian fixes an action only up to an affine functional;
- **T** Hessian + critical point + reference value yield unique normalized quadratic action;
- **T/C** a finite two-sector quadratic parent bulk problem has a unique stationary mode and yields an exact Schur-complement boundary action with reciprocal, PT-even Hessian;
- **T/C** the scalar-bulk Schur coefficient theorem extends to an arbitrary
  finite boundary rank, including exact on-shell formula, reciprocal kernel and
  pairing-level self-adjointness;
- **T/C** in that finite model the displayed bulk Euler equation is the actual
  derivative of the parent action, while the reduced Schur gradient and
  constant Hessian are exact Fréchet derivatives;
- **T/C** exact square completion makes the stationary scalar bulk mode at
  fixed boundary data the unique global minimum for positive bulk coefficient
  and the unique global maximum for negative bulk coefficient;
- **T/C** on the concrete one-dimensional positive PT-flat proportional
  bimetric branch, the reduced interaction has its actual derivative, `c = 1`
  is stationary, its actual Hessian is twelve times the Fierz--Pauli mass
  combination, and for `beta1 > 0`, `beta2 >= 0` it is positive and `c = 1` is
  the unique global minimizer on `c > 0`; this is not the full Janus metric
  field theory;
- **T/N** explicit quadratic and quartically deformed two-variable extensions
  have the same proportional branch, genuine longitudinal derivatives and
  complete transverse two-jet with Hessian `2 kappa`, but a nonzero
  `lambda * y^4` distinguishes them off branch; even the local transverse
  Hessian does not select the nonlinear extension;
- **T/C** an explicit exchange-symmetric two-scale PT-flat lift has the exact
  first variation of its bulk, interaction and reduced boundary channels for
  every independent affine variation; stationarity is exactly the two Euler
  equations;
- **T/N** unspecified reduced boundary coefficients can stationarize every
  scale pair, so the physical boundary functional remains selection data;
- **T/C** a reduced quadratic two-mode candidate has genuine Frechet gradient
  and Hessian, positive full Hessian for positive kinetic signs, and a positive
  algebraic relative-sector quotient for positive PT-flat mass;
- **T/N** the reduced pure-kinetic `kappa = -1` choice has a strictly negative
  actual Hessian direction in the ordinary positive-Hilbert interpretation;
- **T/C** a normed trace/lift interface with arbitrary admissible boundary
  submodules gives exact Frechet/directional variations and an iff between
  stationarity and interior-bulk plus lifted-boundary balance in both sectors;
- **T/N** a nonzero accessible boundary flux obstructs stationarity when its
  sector bulk Euler functional already vanishes;
- **T/C/N** a supplied differentiable Helmholtz boundary flux has a normalized
  actual counterterm with derivative `-flux`; cancelling counterterms are
  unique up to a constant, while one non-Helmholtz Jacobian blocks a global
  `C^2` primitive. No physical GHY/null/corner flux is derived;
- **T/C/N** for an induced second field, the actual Euler equation is
  `E_bulk + E_induced ∘ D(induced) = 0`; the exact action `x-y` on the
  diagonal proves that treating both slots independently can add two nonzero
  equations;
- **T/C** the parametrized global-field package is instantiated on the actual
  effective D8 spacetime/throat quotients; its base PT actions are involutive
  and preserve the same equivariant throat inclusion. On those same bases an
  explicit nonempty diagonal branch uses equal Minkowski matrices, zero matter
  and the identity relative root, and is fixed by PT. Concrete continuity
  predicates cover its independent, induced and LL coordinates, producing an
  inhabited continuous PT-matched configuration with exact throat inclusion
  and root-square equation. This topological closure alone supplies neither Sobolev
  or smooth field spaces, boundary conditions, stationarity/stability, a
  global root map nor a smooth-manifold/tensor-field realization;
- **T/N** different parent problems can preserve the reduced diagonal terms while changing the same-parity mixing;
- **N** changing the parent action, boundary conditions or normalization changes the reduced action;
- **O** derive one actual Janus parent bulk/junction action.

## P-B — Anomaly filter

- **T** PT-paired anomaly proxies cancel;
- **T/N** anomaly cancellation leaves parity-even couplings and finite even counterterms free;
- **T/N** anomaly cancellation and Helmholtz integrability are logically independent; four finite candidates realize all Boolean truth patterns;
- **C** discrete multiplicity selection requires independently fixed regulator data;
- **O** compute the actual local/global anomaly in the same field content and regulator used by the action.

## P-C — Helmholtz reconstruction

- **T** quadratic Hessian realizability iff formal self-adjointness in the finite models;
- **T** three-sector PT-invariant quadratic realizability iff reciprocity holds and both even--odd couplings vanish;
- **T** equal Hessians differ by affine terms;
- **T** PT plus normalization removes the quadratic affine ambiguity;
- **T** finite polynomial Helmholtz conditions reconstruct a cubic potential;
- **T** the coefficient-level affine/quadratic Euler problem over any finite
  field index reconstructs linear/quadratic/cubic potential coefficients iff
  its linear and quadratic Helmholtz swaps hold;
- **T** the normalized reconstructed cubic potential has the Euler source as
  its actual Fréchet derivative in every finite-dimensional direction;
- **T** conversely, equality of the genuine derivative with the prescribed
  finite Euler pairing at every field value alone recovers the normalized
  affine, quadratic and cubic potential coefficients;
- **T** the finite-rank Euler map has its displayed Jacobian as its actual
  Fréchet derivative, and the Helmholtz coefficient swaps make it pairing
  self-adjoint at every field value;
- **T** for that finite polynomial family, actual Jacobian self-adjointness is
  equivalent to the coefficient Helmholtz swaps; these conditions construct an
  actual cubic polynomial gradient realization;
- **T/C** on an open convex normed configuration domain, every differentiable
  Euler one-form with symmetric actual Jacobian has a scalar action primitive;
  on a nonempty convex domain equal Euler derivatives determine actions up to
  one additive constant, removed by a base-value normalization;
- **T/C** on the whole configuration space, for an action whose actual
  derivative is the supplied Euler one-form everywhere, additive linear gauge
  invariance is equivalent to Euler horizontality; the horizontal normalized
  radial primitive is therefore invariant under every corresponding gauge
  translation;
- **T/C** for a supplied complete differentiable one-parameter flow, when the
  supplied Euler one-form is the action's actual derivative everywhere,
  full-flow invariance is equivalent to annihilation of the field-dependent
  generator; horizontal Helmholtz data yield an invariant normalized radial
  primitive;
- **T/C** the set quotient by full orbits of that supplied flow is constructed;
  for any target, functions on the quotient are equivalent to invariant
  configuration-space functions, with real-valued functions specializing to
  invariant actions, including the reconstructed radial action; no quotient
  topology or smooth structure is supplied;
- **T/C** the actual D8 mapping torus now carries a nontrivial complete
  analytic real time-translation action, with analytic diffeomorphism slices;
  its induced action and set-theoretic orbit quotient on the complete current
  Janus field package are exact; integration of arbitrary tangent ghosts
  remains open;
- **T/C** in a supplied reduced two-metric chart, the relative quadratic
  action has its genuine Frechet derivative; independent variations recover
  both Euler components, diagonal/sign-linked variations recover their
  sum/difference, and diagonal translation symmetry yields the reduced Noether
  identity;
- **T/C** in a supplied metric--metric--matter chart, a common `C^2` action
  exists with the proposed linear cross sources iff all three ordered
  cross-block pairs are reciprocal; the sufficient action has a genuine
  Frechet derivative;
- **T/N** any explicitly supplied nonreciprocal cross block rules out that
  common reduced action, while unspecified M30 cross densities do not decide
  the criterion;
- **T/C/N** on the nonlinear plus--minus--matter product, three diagonal and
  three cross-block conditions are equivalent to symmetry of the total actual
  Euler derivative; on an open convex domain they reconstruct a unique
  normalized common action, and a supplied failed block excludes a global
  `C^2` action;
- **T/C/N** a genuine common reduced action with diagonal symmetry and supplied
  boundary Euler term yields only `E_plus + E_minus + boundary_flux = 0`;
  separate sector conservation additionally requires zero exchange and zero
  boundary flux, as shown by the exact `(1,-1,0)` counterexample;
- **T/C/N** for a supplied field-dependent diagonal generator `K(q)`, genuine
  infinitesimal action invariance is equivalent to `E(q) ∘ K(q) = 0`; the
  identity is stable under parameter maps but need not split between sectors;
- **N** a Hessian at one background does not determine a global nonlinear action;
- **T/C** the concrete D8 time flow has a jointly analytic action map,
  restricts analytically to the throat and
  acts on all eight blocks of the current independent-field package, with exact
  group/inverse/PT laws and compatibility with all five induced fields; an
  explicit periodic matter mode gives a complete field configuration with a
  distinct half-period pullback, so the full-package representation is
  nontrivial. Its set-theoretic orbit quotient on the
  complete package has the exact invariant-function equivalence;
- **O** integrate
  arbitrary ghosts into the gauge group, and derive the complete Euler source,
  PDE Noether identities, nonlinear Helmholtz conditions, variational
  cohomology and boundary/null terms.

### Candidate A implementation checkpoint

New controlled subgates are now checked:

- **T/C** compatible symmetric coefficients on the countable `Z^4` Fourier
  lattice decompose into an explicit Lorentz--Gram image plus their zero-mode
  residual; a maximal integer-coordinate pivot gives a uniform inverse bound
  on completed weighted `ell^2` Hilbert spaces. The reconstruction is bounded,
  the order-one symbol is defined on its maximal domain, its compatible
  zero-free image is closed, and the zero-mode obstruction remains in the same
  weighted space. No identification with global Sobolev sections,
  differentiated-series convergence, global PDE or boundary solvability is
  proved;
- **T/C** an invertible Sylvester derivative at a supplied real `4 x 4` root
  produces a genuine local differentiable matrix-root branch, with a concrete
  identity-base instance; no global/principal Lorentz-causal or smooth-field
  root selection is claimed;
- **T** at the independent diagonal Minkowski pair, that identity-base branch
  is now composed with the genuine relative-metric map
  `(g_plus,g_minus) -> g_plus^-1 g_minus`. Its Frechet derivative includes the
  inverse-metric contribution, and its square is the relative metric on an
  actual neighbourhood. This does not select a global, principal or causal
  branch;
- **T/C** along a supplied continuous square-root lift, pointwise Sylvester
  equivalences identify each lift germ with its local IFT branch and force the
  inverse-Sylvester derivative; existence of that continuous lift and its
  Sylvester regularity remain hypotheses, so no global admissible root domain
  is claimed;
- **T/C** on the full positive-diagonalizable locus, a presentation-independent
  global selector is continuous, locally IFT-stable and has the exact
  inverse-Sylvester derivative. It glues at `{I}` to the polynomial root on the
  entire similarity-invariant unipotent locus `(A-I)⁴=0`, using the finite
  binomial root and a bijective polynomial Sylvester inverse; this exhausts
  every unipotent Jordan size in dimension four and exactly extends all lower
  strata. Rescaling covers every single positive eigenvalue `λ>0`, jointly
  continuously with exact Sylvester and agreement at `λ=1`; the positive
  two-eigenvalue `2+2` stratum is also closed blockwise with a finite-series
  Sylvester inverse, and the positive `3+1`/`2+1+1` strata now have the same
  closure. All strictly-positive real Jordan partitions of four are covered
  from supplied presentation data and unified by one exhaustive inductive
  selector with exact square/Sylvester and per-stratum continuity; raw-matrix
  presentation existence is reduced to the single missing Mathlib-level
  Jordan-basis bridge after proving split positive charpoly/minpoly facts and
  exposing Jordan--Chevalley. Nonpositive spectra and the complete physical
  admissible domain remain open;
- **T/C** on the selected global fixed-frame diagonal Lorentz domain, both
  metrics share a strict timelike direction, the nonnegative closure and
  spectral frontier are exact, and the positive root/Candidate-A chain is
  smooth. The Minkowski IFT branch agrees with it on an explicit open nonempty
  overlap; one-sided diagonal boundary paths give root limits zero/infinity,
  Sylvester degeneration on the zero face, and no positive branch switch.
  Positive curves of the same smooth D8 metric fields give the exact
  pointwise density derivative and the integrated functional derivative under
  an explicit domination contract. Smooth symmetric covariant two-tensors and
  their nondegenerate Lorentzian fiber domain are now intrinsic and preserved
  by fiber pullback. With an exact musical equivalence, the same tensor now
  supplies inverse contraction, Gram volume, `p=d phi`, and an exact pointwise
  scalar variation. Frame-change invariance and the true D8-diffeomorphism
  chain rule are exact. On the regular field space with smooth sharp/frame/
  volume data, the density is smooth and integrable for every finite measure,
  and its global action/first variation are exact. A global regular metric
  witness from the diagonal branch remains open;
- **T/N** a deck-compatible anti-periodic determinant obstructs the global
  frame requested by that old regularity class. Canonical local tangent
  frames, a smooth subordinate partition, a nonempty flat local
  regularization and local musical/sharp/tensor/volume data replace it; exact
  gluing to one global Lorentz tensor remains open;
- **T/C** independently, the product cover carries a concrete nonempty
  Lorentz cocycle: tangent `S³` orthogonals plus the line direction give a
  nondegenerate `(3,1)` musical, and the true reflection generator is an exact
  isometry. The intrinsic dependent-tensor and smooth quotient-descent bridges
  are now typed but not yet discharged;
- **T/C** the canonical quotient measure is now built unconditionally from
  spherical measure times Lebesgue measure on a fundamental time domain. Its
  finite Lorentz-density atlas glues uniquely back to that finite nonzero
  measure and gives a nonzero frame-free intrinsic scalar action;
- **T/C** on an open fixed-determinant-sign component of symmetric `4 x 4`
  metrics, the exact inverse and determinant measure of the same metric curve
  give the actual pointwise scalar-density variation and an explicit symmetric
  stress tensor; over an arbitrary measured base, an explicit local
  Lipschitz/dominated-differentiation contract lifts this identity to the
  integrated action for one or two sectors. Rebasing also gives the pointwise
  derivative at every admissible parameter and an alternative integral theorem
  from a uniform derivative bound; sector exchange is invariant.
  In that stress gate the scalar covector is still supplied independently;
- **T/C** on the continuous flat chart `R^4`, the scalar covector is now the
  actual Frechet derivative of the same differentiable scalar field. Its affine
  function-space line varies `phi` and `d phi` together, with an exact
  pointwise density derivative and an integrated derivative under an explicit
  measurability, integrable-majorant and local-Lipschitz contract. On the same
  flat chart, a simultaneous pointwise metric/field curve now ties the exact
  determinant measure and inverse to the same metric and the value and
  `p = d phi` to the same field; its derivative splits exactly into metric
  stress and holonomic-field contributions. This simultaneous variation is
  now integrated on the flat chart under an explicit measurable,
  integrable-majorant and local-Lipschitz contract. At fixed metric its
  holonomic part also decomposes pointwise into the flat scalar Euler operator
  plus the divergence of an explicit boundary flux. Under explicit
  integrability and `IntegratedScalarFluxVanishes`, integration gives the weak
  Euler pairing and rewrites any already-justified action derivative with that
  coefficient. Discharging the contract and deriving the vanishing integrated
  flux from actual boundary conditions,
  curved-manifold covariance, PDE and conservation remain open;
- **T/C** on the compact smooth D8 quotient, the fixed-frame scalar action
  uses the same scalar for value and genuine manifold differential and the
  same positive diagonal metric for inverse contraction and volume. Its
  affine scalar variation is exact pointwise and after integration at fixed
  metric/measure under an explicit integrability contract; Euler--flux form
  and tensorial covariance remain open;
- **T/C/N** for that same global scalar action, weak Euler `K` and symmetric
  Jacobi `J` are defined on all smooth fields under one explicit integrability
  contract and equal its first/second variations. The negative Lorentz time
  coefficient is proved; only the time-static positive-mass sector yields a
  positive Hilbert energy completion whose bounded Riesz extension is
  self-adjoint, bijective and Fredholm of index zero. This is not positivity
  of the full Lorentzian dynamics and no compact resolvent is asserted;
- **T/C** a genuine tangent-section diffeomorphism ghost has exact pullback
  laws and scalar Lie derivative; its linearized BRST differential is
  nilpotent and connected to the independent matter field. Its ordinary real
  self-bracket is proved zero, so a nontrivial nonlinear quadratic BRST term
  genuinely requires odd/graded coefficients; metric Lie derivatives and BV
  remain open;
- **T/C** three explicit deck-equivariant spatial rotations descend through
  the quotient with their `so(3)` bracket table, yielding a faithful nonzero
  nonabelian closed ghost triple. Its explicit exterior CE differential is odd,
  Koszul-Leibniz and square-zero, making the closed triple data unconditional;
  the corrected total `D⊗id + action` is an unconditional global square-zero
  `Z2` differential, while the legacy sign has an exact scalar-square
  obstruction. It extends with square zero to the current linear matter,
  gauge-coordinate, internal-ghost and auxiliary sectors; LL/throat is reduced
  to an infinitesimal-action completion, while metrics, antifields and BV remain;
- **T/C** the actual compact throat carries a differential LL action built
  from a finite smooth tangent-generating frame. Its auxiliary metric has a
  strictly nontrivial positive response, and its integrated first variations
  give an exact weak stationary equation. Its functional PT average has
  invariant action, first variation, weak equation and stationary space for
  every measure. Its same-action flux Hessian is symmetric, PT-covariant,
  equals the linearized weak pairing and has positive kinetic part. The weak
  Euler and Jacobi maps are now actual linear operators on the smooth test
  space, with exact affine linearization and Jacobi symmetry. A topology on
  the algebraic dual, strong divergence form, intrinsic Lorentz contraction
  and a PT-equivariant generating frame remain open;
- **T/C** in the strictly positive LL-measure sector, that same PT Hessian is
  the inner product of a completed Hilbert energy space. Its Riesz realization
  extends to a bounded self-adjoint operator with zero kernel, full closed
  range and index zero; its smooth pairing is the linearized Euler operator of
  the same action. No compact resolvent or D10 identification is claimed;
- **T/C** an explicit quadratic Robin action of the two actual throat traces
  derives the integrated weak junction balance and vanishing squared residual.
  Its symmetric bilinear Hessian has exact sign/kernel classification and is
  the derivative of the same weak-balance operator. On the true throat `L²`
  it is the self-adjoint Fredholm operator `(k_+ + k_-) Id`, with closed range
  and index zero when the coefficient is nonzero. Under a PT-invariant measure,
  traces, fluxes, action, variations, Hessian and the `L²` operator intertwine
  exactly with sector/coupling exchange; geometric normal derivatives and
  Israel/null conditions remain open;
- **T/C** the genuine bulk differential `dφ` now evaluates on a representative
  of the differential normal quotient, transforms with the one-loop normal
  sign, pairs globally with a twisted normal section, and yields an action and
  weak stationary balance. Its splitting is algebraic pointwise; a smooth
  unit normal, Israel jump and null rigging remain open;
- **T/C** the completed first-jet graph `H¹` has dense smooth fields and a
  continuous `L²` projection; under `HasH1TraceBound`, smooth throat trace
  extends continuously and uniquely. In the static scalar sector a pointwise
  uniform graph-ellipticity contract derives the energy-to-graph bound and
  continuous bridge; uniform magnitudes and holonomic coercivity are automatic,
  while the true-frame coefficient transition and intrinsic weak derivative
  identification remain inputs. For canonical physical volumes, the normal
  FTC/Fubini estimate, twisted analytic latitude collar, throat-measure
  pushforward and exact `L²` trace identity are closed. The normal derivative
  is reconstructed exactly by the finite frame with a pointwise coefficient
  bound. Compact uniform coefficient/integrability control follows from the
  remaining tangent-lift continuity predicate; physical coarea remains;
- **T/C** at positive time, the diagonal circle heat semigroup is the
  operator-norm limit of compact finite Fourier truncations and is compact on
  the full circle Fourier Hilbert space; this is not a trace-class theorem or
  the full Janus Dirac heat kernel;
- **T/C** the quarter-twisted Program-P circle operator now identifies exactly
  with both PT-related D7 normal-root towers after the geometric rescaling
  `2 pi / circlePeriod`; each fixed sphere-level heat block is compact and the
  two physical `Z4` determinants have an explicit common-counterterm
  convergence certificate. A smooth all-holonomy Fredholm/Quillen family is
  still open.

The active branch now contains explicit reciprocal cross densities, their
actual spectral Frechet/Hessian/Helmholtz data, a pointwise square-root matrix
potential, a typed gravitational-stratum ledger with a generic worldvolume
placeholder, a finite Gram-tensor compatibility map with genuine `K/J`, and an
exact reduced Noether-proxy classification. These now also close global
fixed-frame diagonal-field subgates. General Lorentz tensor metric variation,
integrated boundary flux cancellation, covariant
Bianchi/constraints, full stability, anomalies, normalization and finite
counterterms remain open. The scoped ledger is
`docs/program_p_explicit_covariant_candidate.md`.

## P-D — Invariant pairings and global coefficient modules

Focused head:

```text
lake build JanusFormal.Branches.FundamentalGeometryPEInvariantPairings
```

Pointwise results:

- **T/X** `Z4` charge neutrality forbids same-quarter quadratic masses and allows the conjugate-quarter cross pairing;
- **T/X** scalar/vector/tensor low-rank pairing dimensions are computed in finite and symbolic models;
- **N** finite signed-permutation symmetry leaves two rank-five tensor quadratic forms;
- **T/X** adding a generic continuous rotation reduces the tensor self-pairing to the Frobenius contraction up to scale;
- **N** repeated irreducible sectors retain multiplicity-space matrices.

Global correction:

- **T** invariant background-dependent pairing families are closed under multiplication by invariant scalar coefficients;
- **T/N** an explicit finite Lean model has the same one-dimensional pointwise pairing shape at every background but no single constant global proportionality factor;
- **T/N** invariant-fiber dimensions can jump between isotropy strata;
- **N** pointwise `dim Hom = 1` does not imply one constant natural coupling;
- **O** construct the actual structured jet groupoid, invariant scalar algebra and global equivariant pairing module;
- **O** restrict the coefficient class by differential order, polynomial degree, weight, scale symmetry, Helmholtz conditions or a parent law.

Canonical correction document:

```text
docs/program_pd_global_pairing_modules.md
```

Last focused CI: **green**.

## P-E — Finite jets, adapted frames and SpinC lift data

Focused head:

```text
lake build JanusFormal.Branches.FundamentalGeometryPEJetUniversality
```

Operator-by-operator statement:

> Fix natural source and target bundles. A regular local natural operator is locally represented by a smooth finite-jet evaluator. Under holonomic jet realization, naturality is equivalent to equivariance of that evaluator, and the evaluator is unique when realization is surjective.

Categorical correction:

> For ordinary finite-order natural or gauge-natural bundles, the classical category has jet-group actions as objects and equivariant maps from finite jet prolongations as morphisms. Composition uses holonomic prolongation. It is not the ordinary category of linear representations with plain fiber maps.

For decorated SpinC immersions the analogous equivalence is conditional on a structured jet groupoid over the background-jet space, an effective descent theorem and separation of global topological data.

### Proven local and algebraic chain

```text
regular local operator
  -> finite jet evaluator
  -> action groupoid and orbitwise descent
  -> source/gauge quotient (B,F)
  -> B = II in adapted coordinates
  -> smooth local adapted orthonormal frame
  -> varying-frame connection law and normal transport
  -> O(T) x O(N) overlap cocycle
  -> SO(T) x SO(N) determinant-one subcocycle
  -> central Spin-lift and determinant-root defects
  -> SpinC diagonal cancellation
  -> concrete circle Spin(2) double cover
  -> explicit U(1) ≃ SO(2) matrix equivalence
  -> metric-derived Euclidean Koszul connection
  -> projected-seed varying-normal atlas
  -> one-chart rank-two SpinC bundle/connection
  -> valid-chart low-order residual/SpinC action groupoid
  -> canonical groupoid arrows between actual overlapping chart extractions
  -> fixed-base descent of invariant low-order observables
  -> smooth descended observables when a smooth coefficient realization exists
  -> conditional multi-chart SpinC Cech and abelian-connection packages.
```

Current theorem evidence:

- **I** Peetre–Slovák supplies local finite-order factorization only under regularity/locality hypotheses;
- **T** naturality/equivariance equivalence and evaluator uniqueness in the formal action model;
- **T** holonomic factorization of composite evaluators;
- **T** action-groupoid laws and orbitwise descent;
- **T** concrete second-order immersion and abelian connection orbit classifications;
- **T** unique universal reduction through `(B,F)`;
- **T** pointwise and smooth local adapted-frame construction;
- **T** connection-corrected `B = II` and residual equivariance;
- **T** moving-frame second-jet law, connection cancellation and normal transport;
- **T** adapted-frame Čech cocycle and determinant-one `SO(T) x SO(N)` reduction;
- **T** central double-cover defects, determinant-root two-torsion and SpinC diagonal cancellation;
- **T** concrete circle squaring with kernel `{±1}`, exact fibers and diagonal quotient;
- **T** explicit group equivalence `U(1) ≃ SO(2)` and matrix-valued rank-two Spin double cover;
- **T** equivalence with Mathlib's rank-two Clifford Spin model;
- **T** smooth Euclidean Koszul connection existence from a smooth positive-definite metric;
- **T** projected-seed varying-normal atlas and overlap coefficient laws;
- **T** canonical one-chart rank-two SpinC Cech bundle and supplied-potential connection;
- **T** valid-chart low-order residual/SpinC action-groupoid realization;
- **T** canonical low-order action-groupoid arrow between two actual valid
  projected-seed chart extractions on an overlap;
- **T** unique chart-independent value of an invariant low-order observable at
  a fixed Euclidean base point;
- **T/C** such an observable descends to a globally smooth function when it
  admits a smooth realization on the continuous reduced-jet coefficient space;
- **T/C** multi-chart SpinC Cech transition presentation from a supplied
  oriented cocycle, lifts, phases and matching diagonal defects, with pointwise
  laws but no transition continuity/smoothness or bundle total space;
- **T/C** local abelian connection potentials obey affine first-jet descent and,
  when all supplied additive shifts are flat, their curvatures glue uniquely to
  a global smooth curvature function whose actual derivative satisfies the
  cyclic abelian Bianchi identity;
- **T/N** local finite order need not give one global uniform order;
- **T/N** smooth dependence is not automatically polynomial;
- **N** equivariance plus finite-dimensionality does not by itself imply finite generation for nonreductive jet-group actions;
- **T/N** naturality does not imply ellipticity or field-content selection.

Exact remaining locks:

- **O** define the actual Janus category and source/target natural bundles, then
  verify locality, regularity and the required holonomic realizations;
- **O** construct the required higher-dimensional Clifford Spin covers;
- **O** derive the conditional Cech inputs from the actual projected-seed atlas,
  determinant transitions and Janus characteristic classes, then construct the
  nontrivial global Janus vector and principal bundles;
- **O** prove characteristic-class matching between the Spin and determinant-root defects;
- **O** identify the global determinant-line connection and attach every natural sector action;
- **O** construct the full differentiable structured jet groupoid and effective descent;
- **O** prove the higher-order jet-isomorphism and integrability theorem;
- **O** classify smooth equivariant maps across isotropy strata.
- **O** classify the required elliptic symbols and specify any bounded
  background region used for a uniform-order theorem.

Canonical documents:

```text
docs/program_pe_categorical_jet_equivalence.md
docs/program_pe_low_order_structured_background.md
docs/program_pe_second_fundamental_form_jet.md
docs/program_pe_smooth_adapted_frames.md
docs/program_pe_spinC_cocycle_lift.md
```

Latest merged theorem-code head: `96e60eb4df1db049f8488858c5a6b1fdb717b224`
(PR 10). Its theorem head passed focused Lean/Python validation locally; no
independent post-merge workflow is claimed here.

## P-F — Compatibility pullback, Helmholtz and Noether

Corrected bridge:

```text
compatibility map K
  -> linearization J
  + self-adjoint target pairing/Hessian H
  -> pulled-back Hessian J^T H J
```

- **T/C** the pulled-back finite model is self-adjoint and satisfies quadratic Helmholtz;
- **T/C** gauge invariance `K R = 0` yields a linearized Noether identity;
- **T/C** one abstract synthesis packages `K R = 0`, `B K = 0`, pulled-back
  self-adjointness, gauge-Hessian degeneracy and restricted Helmholtz for the
  supplied compatibility complex;
- **T/C** the actual Fréchet second variation of a nonlinear pullback is
  `H(Ju)(Jv) + dL(D²K(u,v))` and reduces to `H(Ju)(Jv)` at a target critical
  point;
- **T/C** the complete actual second variation is symmetric even off a target
  critical point; consequently the critical `J^T H J` is symmetric without a
  separate symmetry postulate for `H`;
- **T/C** a target critical point gives genuine pullback criticality, and the
  actual pullback Hessian annihilates `ker J` in both arguments and therefore
  `im R` whenever `J ∘ R = 0`; this is an abstract Fréchet theorem;
- **T/C** for any source submodule contained in `ker J`, that genuine critical
  Hessian descends uniquely as a symmetric bilinear form on the algebraic
  module quotient; continuity of the descent and a normed, topological or
  smooth quotient are not proved;
- **N** Gauss–Codazzi–Ricci–Bianchi compatibility alone does not imply Helmholtz;
- **N** off a target critical point, nonlinear second variation has an additional gradient-times-second-jet term;
- **O** construct the actual Janus compatibility map/jet complex, target
  pairing and global action primitive; no concrete compatibility object is
  supplied by these Fréchet theorems.

# Programs A/B/C and absolute scale

The strongest existing conditional chains transport dimensionless ratios and charge normalizations. The final absolute-scale prediction still requires all of:

- one selected parent/renormalized action;
- one unique stable vacuum;
- microscopic normalization and finite counterterms;
- equality of the spectral, LL, bulk and bimetric charge units;
- no observed-radius input.

# Supported heads and validation

| Entry | Status |
| --- | --- |
| `FundamentalGeometryDiracSpectral` | focused CI green |
| `FundamentalGeometryPEJetUniversality` | PR 10 merged; active follow-on adds smooth low-order observable descent and conditional multi-chart SpinC/connection Cech gates |
| `FundamentalGeometryPEInvariantPairings` | focused CI green |
| `FundamentalGeometryD`, `D7`, `D8`, `D9`, `D10`, `P`, `P-F` | focused CI green on consolidated main/active branch |
| D9 | supported symbol/linear-BRST head; global Fredholm realization open |
| D11 | supported naturality/finite-jet head; global Fredholm realization open |

See `current_status.md` and `janus_branch_registry.md` for the exact operational status.

# Shortest honest research path

```text
1. construct the actual decorated Janus category and field space;
2. choose induced/auxiliary/bulk metric formulation without double counting;
3. package local adapted frames and overlap cocycles in manifold bundles;
4. identify Clifford Spin covers and construct the global SpinC lift;
5. prove characteristic-class matching and attach the determinant connection;
6. construct the structured SpinC/PT/Z4/BRST jet groupoid and descent data;
7. prove the higher-order structured jet-normal-form/integrability theorem;
8. classify invariant scalar functions, global pairing modules and smooth equivariant evaluators;
9. derive one concrete compatible Euler family from a parent or microscopic law;
10. prove nonlinear Helmholtz, Noether and variational-cohomology closure;
11. compute anomalies in the same regulator and field content;
12. fix action normalization and finite counterterms microscopically;
13. compute the renormalized effective action and prove one stable vacuum;
14. close charge compatibility and the absolute scale.
```
