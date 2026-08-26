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
Program MF — weak primitives and audited emergence
          ↓
Program M — candidate-theory specification and meta-selection
          ↓
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

Program M is an upstream comparison protocol, not a claim that abstract
criteria uniquely select Janus. See
[`program_m_meta_theory_selection.md`](program_m_meta_theory_selection.md).

The ordering is logical, not chronological. P-B and P-C are independent filters; P-A may supply the Euler family used by P-C; P-E supplies the local operator/jet category and its structured symmetry data; P-D classifies pointwise pairing shapes together with their invariant coefficient module; P-F explains one route by which compatibility geometry can inherit a variational pairing.

# Program D

## D0/D8 — Global geometry and normal lift

- **T/C** compact fundamental strips project continuously and surjectively onto the actual smooth spacetime and throat mapping-torus quotients, so both are compact;
- **T/C** smooth coefficient fields on the quotient and throat form real vector spaces, admit smooth PT-equivariant throat restriction, and embed into completed `L²` spaces for finite Borel measures; PT is an involutive `L²` isometry for PT-preserving measures;
- **T/C** a finite global smooth tangent-generating family feeds a complete first-jet graph `H¹`; uniform coefficient/mass bounds and holonomic coercivity are automatic, and a geometric frame-control contract implies the static energy-to-graph bridge. The differential normal has an exact total-space `Diffeomorph` and unconditional canonical causal strata; joint `C∞` latitude regularity makes compact finite-frame normal reconstruction unconditional, while an exact spherical-radial/planar-polar calculation closes coarea and the canonical physical trace. Intrinsic Sobolev identification and causal classification for arbitrary general throat metrics remain open.
- **T/C** arbitrary smooth inclusion-preserving diagonal diffeomorphisms act on all global coefficient sectors with exact pullback laws and natural throat trace; smooth orbits have a manifold tangent generator;
- **T/C** PT/exchange acts simultaneously on a unified independent packet with two arbitrary smooth general Lorentz metrics and every current non-metric sector; all retained non-metric throat boundary values have exact trace equivariance and preserved Dirichlet data. Both metrics restrict to smooth symmetric throat tensors, with nondegeneracy iff there is no tangential radical. Restriction is pointwise PT-natural, nondegeneracy/no-radical is preserved and reflected, and a functional metric-reference relation transports full Dirichlet equality. The retained intrinsic metric/musical, equal-sector pair and nondegenerate throat trace are genuine PT fixed points by cover isometry and descent uniqueness. General BV variations and antifields restrict smoothly to the throat with BRST/trace commutation and PT-matched Dirichlet transport. In the bulk, their genuine background-raised pairing supplies the general-tensor ultralocal `1/2 ⟨h⁺,h⁺⟩` master Hamiltonian: exact affine derivative/gradient, intrinsic action-`4` witness, `(h⁺,0)` generation, PT/exchange covariance and pointwise CME. Local tangent/cotangent trivializations, smooth inversion of the finite-dimensional musical matrix and trace invariance discharge the bulk continuity contract and every `L¹` obligation; canonical-volume action/bracket integrability and integrated affine derivatives are unconditional, with exact measure-preserving PT covariance and integrated CME. The retained nondegenerate intrinsic trace likewise has a genuine pointwise inverse, PT/exchange-covariant bilinear pairing and odd bracket, plus its throat ultralocal contractible action with exact affine quadratic expansion and `HasDerivAt`, an explicit nonzero intrinsic-metric witness, boundary-BRST generation and pointwise CME. The same local-matrix argument discharges the throat continuity contract and all its `L¹` obligations, so action/bracket integrability and integrated affine derivatives are unconditional there too. Classification/inversion of arbitrary general restrictions and a general functional, derivative-dependent or nonlocal tensor CME remain open;
- **T/C** on arbitrary covariant two-tensor fields, analytic PT pullback is an
  exact involution preserving symmetry, nondegeneracy and Lorentz inertia;
  nested Hom coordinates discharge the local contract and give an
  unconditional smooth dependent tensor section. The tied musical
  equivalence now pulls back with the same tensor, yielding an involutive PT
  action/exchange on general smooth Lorentz metrics and pointwise covariance
  of the holonomic scalar density. Integration against the canonical quotient
  Lorentz measure has exact integrability transport and unconditional PT
  invariance. At fixed metric, the affine scalar line has exact pointwise and
  integrated quadratic expansion and action derivative under the explicit
  three-coefficient integrability contract; its first variation is PT-covariant
  pointwise and after integration, with iff integrability transport. The
  tangent family remains supplied explicitly. Separately, every
  `SmoothGeneralLorentzMetric` now has a statically constructed finite nonzero
  relative volume measure. `P0EFTJanusMetricVolumeDensityHessian4D` proves the
  genuine pointwise mixed second variation of `sqrt |det g|` along
  fixed-determinant-sign affine matrix curves as
  `sqrt |det g| * (1/4 tr(g⁻¹h) tr(g⁻¹k) -
  1/2 tr(g⁻¹h g⁻¹k))`, symmetric in `h,k`; it is
  globalized by
  `P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolumeHessian4D` through
  `globalMetricVolumeRatio` and `generalMetricTensorPairingAt` to a frame-free
  continuous/integrable density and symmetric integral.
  `P0EFTJanusMappingTorusConformalRelativeLorentzVolumeHessian4D` constructs
  the positive exponential conformal metric line
  `scale(t)=baseScale*exp(t*u)`. Its exact ratio is `rho=scale²`, its first two
  derivatives are `2*u*rho` and `4*u²*rho`, and the latter is exactly the
  frame-free Hessian on the velocity plus the first variation on the
  acceleration, `2*u²*rho + 2*u²*rho`. For a fixed smooth scalar integrand,
  the resulting varying-volume action is `C²`, using the shared compact
  finite-measure differentiation helper
  `P0EFTJanusCompactParametricIntegralC2`. This remains a one-parameter
  conformal result, not `C²`/Fréchet dependence on a metric-section space:
  there is no section chart/topology or general metric variation. With the
  integrand fixed, that gate alone is not the general Einstein--Hilbert
  curvature variation.
  `P0EFTJanusMappingTorusHomotheticEinsteinHilbertHessian4D` closes the genuine
  curvature variation on the positive constant-homothety slice of the
  intrinsic metric: Christoffel and Ricci are invariant,
  `R(scale*g0)=scale⁻¹*R0`, while the volume ratio is `scale²`. The true
  Einstein--Hilbert action equals its reduced affine-scale polynomial and has
  a symmetric Hessian. Along the positive exponential metric curve, the action
  is `C∞` (thus `C²`); its second derivative is the affine Hessian on the
  velocity plus the first variation on the acceleration, and at `t=0` is
  `u²/(2κ) * (Rtot - 8*Λ*Vol)`. Spatially varying conformal factors, the
  general metric-space Fréchet Hessian and the nine-block Jacobi operator
  remain open. `P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D`
  separately globalizes the Maxwell pairing of two arbitrary smooth abelian
  potentials, hence its diagonal density and action, for every
  `SmoothGeneralLorentzMetric`. The transition laws `F₁=JᵀF₂J` and
  `g₁=Jᵀg₂J` give smooth integrable frame-free fields. In four dimensions the
  pairing/density factor `scale⁻²` cancels the relative-volume factor
  `scale²`, so the fixed-potential conformal action is `C∞`, constant and has
  zero symmetric conformal Hessian.
  `P0EFTJanusMappingTorusFrameFreeMaxwellGaugeOrbitHessian4D` adds global
  exact-gauge invariance in either pairing slot and for the action. The
  pulled-back exact-gauge Hessian is zero; the certified derivative order
  gauge then arbitrary-potential gives a zero kernel, and log-conformal then
  arbitrary-potential gives a zero mixed block.
  `P0EFTJanusMappingTorusFrameFreeMaxwellPotentialHessian4D` closes the
  fixed-metric Hessian between two arbitrary smooth potential variations as an
  integrable symmetric bilinear form, with exact line/mixed derivative
  certificates and a two-sided exact-gauge kernel.
  Arbitrary-metric--potential mixing, general Fréchet dependence, Candidate-A
  interaction/chart/core and Jacobi/Fredholm identification remain open. For arbitrary smooth D8
  self-diffeomorphisms, simultaneous metric/scalar/tangent-family and
  inverse-pushforward measure transport gives finite action covariance, iff
  integrability and sector exchange. The smooth tensor pullback, transported
  musical equivalence and Lorentz inertia now construct that metric certificate
  unconditionally for every smooth D8 self-diffeomorphism. On a supplied smooth orbit,
  the action has zero derivative, identified under the exact non-vacuous
  first-variation contract with the scalar diffeomorphism Noether pairing.
  The true `sharp(dφ)` and an exact divergence/boundary-flux interface also
  identify the general scalar first variation with the weak covariant Euler
  pairing plus flux, prove stationarity equivalence at zero flux, and specialize
  to the intrinsic D8 metric. The corresponding intrinsic contravariant scalar
  stress is pointwise natural under every smooth D8 diffeomorphism. The
  canonical latitude collar now has an exact scalar Green--Wronskian current,
  with Euler-residual derivative and pointwise/measured conservation for
  equal-mass solutions. It is realized as a genuine quotient-tangent current
  along the collar, carried by the intrinsic unit-spacelike normal; its metric
  normal flux is exactly the Wronskian, remains locally conserved and at the
  throat equals the concrete normal-`mvfderiv` pairing. Its energy
  `(φ')² + m²φ²` has derivative exactly
  `2φ'` times the Euler residual, hence fiberwise/measured conservation and
  zero endpoint jump for Euler solutions, plus nonnegativity when `m² ≥ 0`.
  It is exactly twice the normal-normal component of the general scalar stress
  on the normal-projected collar jet; this component has zero derivative and
  is locally constant under the collar Euler equation. This is a local collar
  stress-energy identity only. Separately, the total holonomic atlas glues the
  scalar stress divergence globally and proves its vanishing under Euler, while
  the canonical cut bulk carries the exact oriented measured Green--Stokes
  formula. Its residual is precisely the two-sheet flux period, closed in the
  Dirichlet, PT-fixed and PT-projected sectors and provably nonzero in general.
  Extending these results to a covariant four-dimensional Noether current with
  enough test ghosts and arbitrary admitted metrics remains open;
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
  closed image and open nonzero complement. Any supplied continuous intrinsic
  normal quadratic form now produces the complete open/closed causal and joint
  stratification with scaling laws. For the restricted spacetime metric, the
  preferred latitude-normal fiber equivalence yields an anchor-independent
  global fiber-linear orthogonal lift. Its square is exactly `scalar^2` in every
  transported chart, discharging
  `CanonicalGlobalNormalMetricSquareLocalRegularity` and proving global
  continuity. The named global spacelike, timelike, null, non-null and joint
  strata therefore have unconditional open/closed laws, cover and joint-in-null
  inclusion. The generic dependent continuous-lift record remains a separate
  optional bridge, not a prerequisite for this direct canonical stratification.
  The explicit latitude
  tangent has been constructed on the true cover and its raw
  ambient derivative is exactly `(e₀, 0)`. The intrinsic ambient derivative is
  now publicly factored through product coordinates, and the product derivative
  is the equivalence induced by the global product diffeomorphism. The exact
  product and ambient images are computed, and both the ambient image and
  canonical tangent are nonzero. For the actual intrinsic cover Lorentz
  tensor, the canonical tangent has exact square `1`, is orthogonal to every
  fixed-throat differential tangent, and is therefore spacelike and non-null.
  Its pushforward realizes that canonical local quotient-normal lift. The
  induced orthogonal splitting proves that the retained intrinsic metric has
  no tangential radical and a nondegenerate smooth throat restriction. One
  deck turn has the exact normal sign law and preserves the local quadratic
  model and orthogonal-lift square. The quotient latitude curve law extends to
  every integer winding with even/odd normal-sign parity, together with its
  dependent tangent `HEq` and scalar quadratic-model invariance. The named
  cover normal is `HEq` to its raw derivative after zero-latitude transport.
  The projection chain rule now identifies the pushed canonical quotient
  normal with the quotient-latitude tangent by `HEq`. The scalar-action
  cocycle between dependent tangent fibers now supplies the global algebraic
  lift above; its exact chart square closes local regularity and the direct
  causal stratification, while dependent continuous packaging remains optional;
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
  unconditional `Spin(4) → SO(4)` surjectivity and provide a lifting function;
- **T** the twisted `Pin⁻(4)` projection has kernel `{±1}`, is a covering with
  local sections, and the canonical continuous Čech cocycle constructs the
  genuine ambient principal bundle;
- **T** the real-normal half-angle gauge, all-winding laws, inverse/triple
  cocycle, pointwise path independence and continuity for continuous nonzero
  horizontal normals are exact; the intrinsic normal lift and its genuine
  tangent-trivialization coordinates are jointly `C∞`;
- **T** the twisted `PinC(4)` principal/spinor bundles, determinant line,
  Hermitian pairing and D9 smooth spinor bundle/sections/connections are
  constructed; the oriented SpinC descent remains impossible by
  nonorientability;
- **C** a P-independent topology ledger separates Spin/PinC existence, lift classification, cocycle, monodromy and lifted boundary conditions;
- **N** a real codimension-one line does not itself carry a literal quarter-turn;
- **N** a square-root line or `Z4` lift is extra global structure, not a canonical functor of the underlying line;
- **C** the explicit cover-product-to-quotient-tangent coordinate map now
  identifies the canonical latitude normal representative with its genuine
  quotient-trivialization presentation, with an exact equality to
  `canonicalLatitudeNormalCoordinate` at the throat. This presentation
  sub-lock did not close `T01` by itself; the terminal foundation/pairing
  certificate is now closed separately by
  `program_p_t01_global_foundations_pairings_terminal_gate`.

## D2 — Focused twisted Dirac spectral geometry

Focused head:

```text
lake build JanusFormal.Branches.FundamentalGeometryDiracSpectral
```

Current results:

- **T/C/X** monopole-spectrum arithmetic and product pairing;
- **T/C** an explicit separated product-mode model gives a positive spectral gap and PT invariance of the squared spectrum;
- **T/C** in each fixed normal-root sector, finite circle-mode packets of the
  concrete geometric SpinC zero and first signed sphere blocks synthesize
  injectively into genuine smooth sections and intertwine the actual Dirac;
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
- **T/C** the Program-P facade now realizes every signed sphere/Fourier label
  geometrically, proves Fourier--monopole completeness and obtains the exact
  global unitary; after the orientation-correct zero-mode permutation, the
  geometric `2D + m²` Hessian model intertwines with its self-adjoint
  Fredholm maximal multiplier on the finite core;
- **O** lift this fixed-background result to the variable
  metric/gauge-coupled family, then compute the actual eta invariant and full
  determinant.

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
- **T/C** the complete multiplicity-aware D10 Gaussian is summable at every
  positive time; physical PT is an isospectral chirality-reversing
  permutation, so the infinite chiral trace vanishes and arbitrary finite
  cutoff nets converge to zero. On the complete D10 Hilbert space it is a
  compact operator with a summable rank-one nuclear expansion, and finite
  spectral truncations converge to it in operator norm;
- **T/C** a separate basis-dependent reference regulator now acts on the exact
  completed bulk `L²`--SpinC--D10--LL product and is compact, injective and
  nuclear at every positive time; bulk Dirichlet compactness/zero trace and
  the exact physical SpinC/D10 heat certificates are retained. Exact D9
  continuum heat is nuclear under its summability hypothesis (finite packets
  unconditionally), while exact LL Hessian heat is compact only in finite
  dimension;
- **I/O** no equality of that reference regulator with the global Hessian heat
  is asserted. D9 high-energy growth, an elliptic LL heat realization and the
  global unbounded Janus Fredholm/Quillen family remain physical-Hessian
  obligations.

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
- the fixed-background D8 category with all smooth self-diffeomorphisms as
  morphisms, its contravariant smooth-field section functor and the actual
  contravariant general-Lorentz-metric pullback functor, with exact
  identity/composition laws.

The moduli category of all Janus backgrounds, global structured jet groupoid,
regularity hypotheses, descent theorem and invariant-theory classification
remain open.

# Program P

Canonical closure register:
[`program_p_operational_todo.md`](program_p_operational_todo.md).
Global status: **1/14 terminal gates**.
Validation on 2026-08-26: the complete Program-P facade and local import
closure compile as `.olean`; the `T01` terminal certificate and one hundred ten
nonterminal `T02` support gates are integrated.  Besides the carrier, generic
`C²` extraction, actual SpinC/LL throat packet and low-order `(II, F)` orbit,
these include actual bulk/throat metric jets, the realized bulk
Christoffel/`U(1)²` background core, all typed nonminimal carrier slots (nine
jets after sector expansion) and the conditional true bulk-carrier assembly
from a compatible `GlobalCandidateAActionData`, a supplied chart and explicit
external normal data.
The actual sectorized `U(1)²` potentials have intrinsic fixed-throat pullbacks,
centered `C²` covector germs and jets in the exact `EuclideanR3` gauge slot.
Their coefficient expansion reconstructs the intrinsic covector exactly on
the centered tangent-trivialization base set and, for Candidate-A, equals the
centered-frame coordinate expression of the ambient bulk pullback at every
such point, including the inverse tangent trivialization.  Common centered tangent frames
satisfy the exact zero-order contragredient transition law.
The tangent transitions also satisfy identity, inverse and exact triple-overlap
cocycle laws, with the corresponding dual cocycle on covectors.  These remain
only zero-order fiber/frame statements.  The transition and its inverse are
`C∞` on each overlap when read as continuous linear maps.  The coefficient and
reconstructed-covector representatives are `C∞` on each full centered
`baseSet`, and the induced dual action is `C∞` on the double overlap.  The
transported first representative and the second representative have equal
`HasMFDerivWithinAt` certificates for every candidate first derivative on that
overlap.  In the extended throat chart centered at the overlap point, the
explicit first-order law
`dC₂ = D₁₂ ∘ dC₁ + (dD₁₂) · C₁` is also proved.  It remains a
fixed-chart statement, not intrinsic jet descent.
A two-parameter local jet carrier now separates frame anchor from chart center,
equals the original Candidate-A extractor when both coincide, and realizes
that law in its genuine `firstDerivative` field.  A generic second-order
continuous-linear-map Leibniz lemma then proves the four-term transformation
of its `secondDerivative`: transported `D²C₁`, two mixed terms and
`D²D₁₂·C₁`.  The same laws now hold in the exact `EuclideanR3` carrier.
For two different extended base charts and one fixed tangent frame, their
representatives agree as germs and the resulting three-parameter jet obeys the
full first- and second-order chain rules, including the transition Hessian.
The base-chart transition jets satisfy the exact Jacobian/Hessian cocycle on
triple overlaps.  These laws are combined with the varying frame transition
from a centered source chart and transported to the exact `EuclideanR3`
three-parameter gauge carrier.  The frame law is now valid in an arbitrary
source chart, and composition with a second chart gives the exact transition
through order two between arbitrary frame--chart pairs.  Base-chart unit and
inverse laws also hold at the germ, Jacobian and Hessian levels.  The combined
semidirect transition now obeys its exact triple cocycle, including the
five-term fiber Hessian, and has unit and inverse laws through order two.
The arbitrary local frame--chart presentations now carry the exact
value/Jacobian/Hessian direct relation and its explicitly generated setoid.
All actual extracted gauge jets are directly related, hence define one
presentation-independent class in the pointwise quotient.  The direct relation
is reflexive, symmetric and transitive; its generated closure is proved equal
to it, so the pointwise quotient has no additional zigzag identifications.
The framed raw carrier is now normed and finite-dimensional.  Its exact
semidirect transition operators are continuous linear, satisfy the groupoid
laws and vary `C∞` on an open cover.  They define a smooth Mathlib vector
bundle; the quotient classes identify with its fibers, and the actual throat
`U(1)²` gauge second jets form a global `C∞` section.
The latest eight gates also build the chart-indexed constant-fiber second-jet
core and generic smooth-section descent. The three actual LL fields therefore
give separate global `C∞` second-jet bundle sections with exact zero-jet values.
Covariant rank-two throat metric jets now have arbitrary frame/chart extraction,
exact first/second-order overlap and groupoid transport, a smooth vector-bundle
core and global `C∞` sections, including both induced metric sectors. Eighteen
further gates (92 + 18 total) complete SpinC second jets through arbitrary
trivialization/chart extraction, exact overlap and cocycle laws, semidirect
groupoid transport, a smooth `VectorBundleCore`, and global `C∞` sections for
every smooth SpinC section and the physical sectors. Only the common
physical/background/normal bundle remains absent.
Under sectorwise transversality, the actual induced-metric one-jet produces a
pointwise Koszul quadratic.  The raw transported derivative is symmetric in
its metric slots, its explicit symmetrization equals the raw derivative, and
the Koszul identity is proved directly for that raw derivative.  The refined
true throat carrier combines these actual background slots with its actual
metric/SpinC/LL jets and externalizes only `normalQuadratic`, its symmetry and
`physicalNormal`.  The former whole-background assembly remains historical.
No smooth global Levi--Civita connection, smooth descent of the remaining
physical jet slots or canonical normal geometry follows from these separate
gauge/LL bundle gates.
The integrity audit is green at `1/14`; `T02` remains open.

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
- **T/C** on the supplied reduced Candidate-A FLRW dust branch, the exact
  `3 x 3` constraint minor stays nonzero on a nonempty open parameter locus of
  an explicit affine family, so the three constraint covectors are independent
  there and on a neighbourhood of the witness. Its exact nonlinear constraint
  curve contains distinct equal-energy points, so this reduced witness is not
  a strict isolated vacuum. Generic phase-space rank,
  covariant/ADM derivation and Boulware--Deser exclusion remain open;
- **T/N** different parent problems can preserve the reduced diagonal terms while changing the same-parity mixing;
- **N** changing the parent action, boundary conditions or normalization changes the reduced action;
- **T/C** the abstract nine-sector Sobolev action has a complete sectorial
  `C²` assembly. Candidate A, matter, Robin, LL, BV and Einstein--Maxwell lines
  instantiate the exact second-derivative criteria, including all-finite-measure
  variants under visible joint-continuity hypotheses. Identifying these
  fixed-frame models with one intrinsic Janus field topology remains open;
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
- **T/C** the exact nine-block Candidate-A action now has its actual Fréchet
  Euler form on every regular common `C²` chart; its Jacobian satisfies
  nonlinear Helmholtz, the normalized radial primitive reconstructs the same
  action, arbitrary paired smooth `U(1)²` ghosts have constant physical gauge
  orbits, and global functional null actions/boundary ambiguities are constants;
- **N** a Hessian at one background does not determine a global nonlinear action;
- **T/C** the concrete D8 time flow has a jointly analytic action map,
  restricts analytically to the throat and
  acts on all eight blocks of the current independent-field package, with exact
  group/inverse/PT laws and compatibility with all five induced fields; an
  explicit periodic matter mode gives a complete field configuration with a
  distinct half-period pullback, so the full-package representation is
  nontrivial. Its set-theoretic orbit quotient on the
  complete package has the exact invariant-function equivalence;
- **T/C** Candidate-A change of variables for its five measured action blocks
  is reduced to seven supplied density pullback identities. The
  interaction identity is reduced to plus-metric musical pullback, root
  conjugation and regular-basis transport; the canonical time-flow measure
  equality gives the corresponding fixed-measure reduction. A concrete
  conformal `GlobalFieldConfiguration` time orbit now has exact zero/add laws,
  but it is not lifted to action data or a chart. The canonical-throat GHY
  block vanishes identically, while SpinC matter, LL and finite-BV ambient
  covariance remain. The fixed holonomic Christoffel germ has now been
  differentiated and antisymmetrized on arbitrary vectors; cancellation of
  the symmetric `D²`/`D³` transition jets proves
  `J (R₁(u,v)z) = R₂(Ju,Jv)(Jz)` and its endomorphism corollary. Ricci/scalar
  contraction now proves chart independence of scalar curvature, and the
  unconditional total holonomic cover glues it to a genuine smooth global
  scalar. This fills the scalar-curvature slot of every legacy
  Einstein--Hilbert metric. A standalone frame-free scalar-curvature action
  consumes any supplied finite nonzero action measure. For every
  `SmoothGeneralLorentzMetric`, a positive smooth chart-independent ratio
  against the explicit intrinsic reference defines a finite nonzero relative
  Lorentz-volume measure and recovers the canonical measure at the intrinsic
  metric. The Maxwell pairing of arbitrary potential pairs and its diagonal
  action are frame-free, smooth and integrable. The conformal action and exact
  gauge orbits are constant; exact-gauge--arbitrary-potential and
  log-conformal--arbitrary-potential mixed blocks vanish in the certified
  derivative order. The fixed-metric arbitrary-potential Hessian is now an
  explicit symmetric bilinear form with exact line/mixed derivative
  certificates and a two-sided exact-gauge kernel. This still leaves
  arbitrary-diffeomorphism covariance of the fixed reference, general
  `C²`/Fréchet dependence, Candidate-A interaction and
  arbitrary-metric--potential Maxwell data open. At a critical configuration,
  the span of every supplied differentiable nonlinear diffeomorphism-flow
  generator is now an exact two-sided Hessian kernel; the Hessian descends
  both by this span and by its sum with the physical `U(1)²` directions;
- **O** construct a normed atlas covering every raw global tangent, derive the
  componentwise local Euler/stress equations and diffeomorphism BRST/BV
  identities, and build the full horizontal local variational bicomplex.

### Candidate A implementation checkpoint

New controlled subgates are now checked:

- **T/C** compatible symmetric coefficients on the countable `Z^4` Fourier
  lattice decompose into an explicit Lorentz--Gram image plus their zero-mode
  residual; a maximal integer-coordinate pivot gives a uniform inverse bound
  on completed weighted `ell^2` Hilbert spaces. The reconstruction is bounded,
  the order-one symbol is defined on its maximal domain, its compatible
  zero-free image is closed, and the zero-mode obstruction remains in the same
  weighted space. This Fourier-coefficient model remains deliberately
  separate from the physical mapping torus. The latter now has its own
  covariant curvature--Bianchi complex and faithful gauge `L²` complex with
  exact `H⁰`, quotient and closed-range completion; no Fourier identification
  is used;
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
- **T** on the explicit global root-admissible domain, two intrinsic general
  Lorentz metrics on the same tangent bundle now carry a smooth relative root
  whose square is exact and whose matrix coefficients/densities agree with
  Candidate A. The conformal positive branch proves the domain nonempty; no
  universal real root outside that domain is asserted;
- **T** one global configuration/tangent now combines these metrics, genuine
  SpinC matter, `U(1)^2`, ghosts, auxiliaries, LL and D9/D10 without a duplicate
  metric slot. Its finite-product `H¹`, throat trace, closed Dirichlet kernel
  and common bulk/SpinC/D10/LL domains are constructed;
- **T/C** the global boundary completion uses the true Gaussian throat,
  finite explicit null faces/joints, the same Palatini flux and the canonical
  divergence-free LL frame. Its total residual vanishes on the PT-fixed or
  Dirichlet scalar sector; unrestricted scalar flux is intentionally retained;
- **T/C** along a supplied continuous square-root lift, pointwise Sylvester
  equivalences identify each lift germ with its local IFT branch and force the
  inverse-Sylvester derivative; existence of that continuous lift and its
  Sylvester regularity remain hypotheses, so no global admissible root domain
  is claimed;
- **T/C** on the full positive-diagonalizable locus, a presentation-independent
  global selector is continuous, locally IFT-stable and has the exact
  inverse-Sylvester derivative. It now supplies the unique continuous exact-
  square global lift of every local IFT chart on exactly that locus; no atlas
  lift on Jordan strata, nonpositive spectra or the general physical domain is
  claimed. It glues at `{I}` to the polynomial root on the
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
  presentation existence is closed on the Hermitian split-positive sector by
  Mathlib's unitary spectral theorem, including every `PosDef` matrix, with an
  exact diagonal presentation and Sylvester-regular root. After proving split
  positive charpoly/minpoly facts and exposing Jordan--Chevalley, the general
  non-Hermitian step is reduced to the single exact
  `PositiveRealNonHermitianJordanChainBasisResidual4`: select an invertible
  real matrix of chain vectors and its `Fin 4` partition. Inverse matrix,
  unified presentation, exact root and Sylvester bijectivity are unconditional
  downstream; only that chain-basis construction remains;
  root existence is already unconditional on the
  full PSD raw locus via `CFC.sqrt` and on the genuinely non-PSD positive
  quadratic locus `(A-λI)(A-μI)=0`, `λ,μ>0`, through the exact affine root
  `(A+√λ√μ I)/(√λ+√μ)`. A repeated size-two Jordan witness proves this is a
  strict extension. Every positive single-eigenvalue relation `(A-λI)^4=0`
  is now closed by an exact cubic Taylor root; a strict size-four block is
  proved non-Hermitian, non-PSD and outside the quadratic locus. The distinct
  positive double-double relation `(A-λI)²(A-μI)²=0` is also closed by an
  explicit degree-at-most-three Hermite interpolant. Divisibility by both
  squared factors and `minpoly`, exact evaluation and the matrix square are
  proved; the canonical Jordan `2+2` witness lies outside PSD, quadratic and
  single-eigenvalue quartic loci. The positive `3+1` relation
  `(A-λI)³(A-μI)=0`, `λ≠μ`, is now closed by a cubic matching the order-two
  jet at `λ` and the value at `μ`; cubic-times-linear divisibility, minpoly
  congruence and the exact matrix square are proved. Its canonical Jordan
  witness lies outside every earlier positive locus. Hermite interpolation
  also closes `2+1+1`, and a four-node Lagrange cubic closes
  `1+1+1+1`. Splitting and degree four extract the positive charpoly roots;
  Cayley--Hamilton plus their exhaustive equality partition selects one of
  these five annihilator profiles. Raw root existence is therefore
  unconditional on `PositiveRealSplitCharpoly4`; a Jordan-chain presentation
  remains separate only for an explicit normal form, while basis-free
  polynomial-centralizer reasoning closes global Sylvester regularity. The
  canonical frontier witness `J₂(t) ⊕ 1 ⊕ 1`, `t → 0⁺`, has an exact Hermite
  root with divergent `1/(2√t)` coefficient and norm, no finite continuation,
  and a collapsing `E₀₁` Sylvester mode. This obstruction is invariant under
  every fixed real similarity. The two-parameter collision
  `J₂(t) ⊕ J₂(s)` has two independent degenerating Sylvester modes and no
  finite extension at the double-zero corner. The explicit moving polynomial
  shear `P(t)=I+tE₂₀` also has an exact inverse, transported root and mode,
  nonconstant target, divergent coefficient and no finite continuation. The
  singular diagonal scaling `P(t)=diag(t,1,1,1)` regularizes that canonical
  divergence to a finite nonzero nilpotent root limit, while its inverse blows
  up and its Sylvester mode degenerates. The explicit type-changing path
  `I+tE₀₁ → I` has an exact smooth affine root and constant Sylvester
  eigenvalue `2`; the contrasting path `t(I+E₀₁) → 0` has root and Sylvester
  eigenvalue both tending to zero. These retained explicit witnesses are now
  assembled in one proof-carrying frontier certificate. Arbitrary singular frames, the general
  Jordan-type classification/branch atlas and arbitrary matrix `0/0` paths
  remain open. For
  nonpositive spectra, determinant/simple
  negative-eigenvalue obstructions, positive-determinant counterexample,
  paired-negative constructions and the exact Jordan parity/zero-block
  criterion are closed. Pure complex-conjugate `2×2`, `2+2` and non-semisimple
  Jordan-chain roots are also explicit with their cut/zero behavior; only the
  raw relations `(A-aI)²=-b²I` have an explicit affine root, including the
  repeated complex pair. The remaining presentation/classification bridges
  concern positive Jordan-chain/Sylvester data and the exact nonpositive or
  complex Jordan necessity/sufficiency residuals; the complete physical domain
  remains open;
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
  coefficient. This flat-chart contract remains conditional. On the canonical
  quotient, however, curved scalar covariance, the global Euler stress identity
  and the cut-bulk Green--Stokes formula are now proved below; a general
  covariant parent action and its coupled PDE system remain open;
- **T/C** on the compact smooth D8 quotient, the fixed-frame scalar action
  uses the same scalar for value and genuine manifold differential and the
  same positive diagonal metric for inverse contraction and volume. Its
  affine scalar variation is exact pointwise and after integration at fixed
  metric/measure under an explicit integrability contract. For a general
  Lorentz metric, an exact divergence/boundary-flux interface now yields the
  weak covariant Euler decomposition, stationarity equivalence under zero flux
  and the intrinsic D8 specialization; its contravariant stress is pointwise
  diffeomorphism-covariant and its arbitrary measured cotangent pairing is
  invariant under diffeomorphism plus sector exchange. One unconditional
  certificate packages the pointwise, measured, two-sector and integrated-
  variation laws. Separately, the normal-frame covariant scalar second jet
  satisfies `div T = (□φ - V'(φ)) sharp(dφ)` and is conserved under Euler for
  both retained potential conventions. A pointwise metric-compatible,
  torsion-free connection-jet interface transports this identity to arbitrary
  coordinates with exact `∂T + ΓT + ΓT` cancellation. That interface is now
  realized algebraically from every symmetric nondegenerate metric and
  metric-symmetric first jet by the local Levi-Civita formula, including
  `∂g⁻¹ = -g⁻¹(∂g)g⁻¹`, torsion freedom and covariant/contravariant metric
  compatibility. On every supplied smooth holonomic quotient patch, a genuine
  `SmoothGeneralLorentzMetric` now yields smooth nondegenerate local metric,
  inverse, coordinate derivative and Christoffel coefficients. Any genuine
  smooth quotient scalar pulls back to a `C∞` representative. Its gradient,
  raw Hessian, covariant jet, Euler residual, raised gradient and canonically
  realized stress divergence are `C∞`; Schwarz gives Hessian symmetry and the
  exact identity `div T = EulerResidual · raisedGradient` closes Euler stress
  conservation at every patch coordinate. On two supplied overlap
  representatives, agreement of the metric first jet and scalar second jet
  now forces equality of Christoffels, covariant jet, Euler residual, raised
  gradient and stress divergence. The true quotient transitions are now
  analytic, a field-independent covering holonomic atlas is constructed, and
  these local data glue with
  `div_g T = EulerResidual · raisedGradient`; hence `div_g T = 0` follows from
  the scalar Euler equations on the canonical quotient. This does not yet
  construct the full coupled covariant parent theory.
  The concrete normal
  throat flux vanishes pointwise and integrally for homogeneous Dirichlet
  variations. Genuine interval-integral IPP closes the canonical latitude
  collar and identifies its normal `mvfderiv` boundary term. The intrinsic
  gradient-normal pairing equals that derivative and realizes an exact
  oriented collar divergence/boundary interface, including measured
  Dirichlet stationarity. The canonical cut bulk now realizes the former
  adapter by an exact global Green--Stokes theorem: its boundary functional is
  the concrete oriented tangent-normal flux. Dirichlet, PT-fixed and
  PT-projected sectors close the flux; the unrestricted formula correctly
  retains a possibly nonzero oriented period. The associated
  scalar Green--Wronskian current has the exact antisymmetric Euler-residual
  derivative, is pointwise and measured constant for equal-mass Euler
  solutions, has the expected antisymmetric endpoint jump and vanishes for
  homogeneous Dirichlet Euler pairs. It is now a genuine tangent current along
  the quotient collar, carried by its intrinsic unit-spacelike normal; its
  metric normal flux is exactly the Wronskian, is locally conserved and at the
  throat equals the concrete normal-`mvfderiv` pairing. The collar energy
  `(φ')² + m²φ²` has
  derivative `2φ'` times the Euler residual, is fiberwise and measured
  constant on Euler solutions, has zero endpoint jump and is nonnegative for
  `m² ≥ 0`. It is exactly twice the general scalar stress component `T_nn`
  on the normal-projected collar jet, and `T_nn` is locally constant under the
  collar Euler equation. This remains only a local collar stress-energy result.
  The canonical cut bulk is nevertheless a global `C∞` manifold with boundary:
  its descended Green current, intrinsic Lorentz metric/volume, normal
  divergence and oriented measured Green--Stokes formula are constructed.
  Under Euler, the exact residual is the two-sheet oriented flux period; it
  vanishes in the proved Dirichlet, PT-fixed and PT-projected sectors, while a
  formalized Wronskian counterexample rules out universal zero flux. Agreement
  with the full abstract bulk-boundary functional, globalization to a smooth
  covariant stress divergence and Noether current, and a unit normal for every
  admitted general metric remain open; the intrinsic canonical latitude normal
  itself is already constructed;
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
  gauge-coordinate, internal-ghost and auxiliary sectors. On the throat the
  rotations descend with exact `so(3)` bracket and explicit scalar/Koszul and
  LL maps; the throat differential is odd, Leibniz and square-zero, so its LL
  completion is unconditional. Positive diagonal throat metrics have an exact
  log-coordinate action, positive integral curves and square-zero BRST; one
  finite field/antifield master model is promoted to smooth fields on the real
  throat with pointwise CME, nonzero integrated action, exact first variation
  and an integrated odd antibracket/CME on analytic ultralocal functionals.
  The canonical throat measure is unconditionally PT-preserved, so the
  integrated master action, first variation, represented functional value,
  odd bracket and CME have unconditional PT covariance. The same constant
  finite `32`-dimensional fibre now defines smooth fields, square-zero BRST, a
  nonzero canonical-volume action and pointwise/integrated CME on the actual
  spacetime quotient. Its canonical volume is unconditionally PT-preserved,
  so the spacetime master action and integrated CME are also PT-covariant.
  Its affine first variation, exact integrated directional derivative and odd
  bracket/CME on represented analytic ultralocal spacetime functionals are
  closed; their exact fibre PT laws and integrated first-variation, value,
  bracket and CME covariance are unconditional. This phase is now coupled to
  the actual smooth positive diagonal/log metric cone, including ghosts,
  antifields, corrected BRST, nonzero action, pointwise/integrated CME and PT.
  General symmetric tensor variations now have a separate safe first BV level:
  smooth field/antifield pairs, an odd square-zero doublet, background-raised
  pointwise pairing and graded-skew Darboux antibracket attached to the general-
  Lorentz packet. Its involutive analytic PT/sector exchange commutes with BRST
  and preserves the pairing and odd bracket pointwise. The resulting bulk
  ultralocal `1/2 ⟨h⁺,h⁺⟩` action has an exact affine `HasDerivAt` equal to its
  antifield-gradient pairing, an intrinsic action-`4` witness, BRST generation,
  PT covariance and pointwise CME. Local metric-matrix inversion proves every
  smooth bulk pairing density continuous and `L¹`, so canonical-volume
  action/bracket integrability and the integrated affine
  `HasDerivAt`/gradient are unconditional; PT covariance and CME remain exact.
  Certified functional observables and their odd bracket now support a genuine
  rank-one nonlocal bulk master, with exact derivative, functional CME,
  generated square-zero BRST and a nonzero intrinsic witness. Variations and
  antifields have a genuine smooth throat trace; its square-zero boundary BRST
  commutes with restriction, PT/exchange matching transports the complete
  metric-BV Dirichlet packet, and packet-level pointwise odd-bracket covariance
  persists. The nonlinear global bridge now also reuses the existing smooth
  metric flow-to-ghost contract and supplies its missing Maxwell analogue:
  one-form and two-tensor pullbacks are functorial, and the Maxwell
  infinitesimal generator is a genuine fiber derivative with a smooth global
  realization. A generic Lie-representation interface and its coadjoint
  antifield action reduce nilpotence to `[L_c,L_d]=L_[c,d]`; this identity is
  unconditional for scalars. The existing coefficient-plus-pulled-measure
  density convention now has finite functoriality, a square-zero two-ghost
  action and unconditional integrated scalar covariance. The fixed-throat
  scalar bracket also now supplies a coadjoint algebraic antifield action,
  square-zero obstruction and invariant field-antifield pairing. For
  Maxwell/metric fields the bracket identity is a consequence of Cartan
  evaluation. The Maxwell action is now globally smooth and bilinear, and its
  representation/bracket are closed. Its field and algebraic
  coadjoint-antifield obstructions and evaluation pairing are BRST closed,
  without a geometric/integrated Maxwell dual. Their Cartan residuals are genuine fiber covector/tensor
  objects (the metric one symmetric and tensorial in both test fields). The
  finite-frame assembly now gives the global smooth bilinear metric action,
  its Lie representation and exact bracket law. The concrete combined
  Maxwell/metric Cartan datum now produces algebraic coadjoint antifields for
  Maxwell and the two-metric product, with square-zero and invariant
  pairings. The existing integrated geometric metric pairing now
  supplies a linear realization of every smooth metric antifield in that
  algebraic dual. Coadjoint equivariance is now equivalent to the explicit
  integrated skew-adjointness identity for the metric Lie action. The finite
  smooth bulk tangent frame now assembles a smooth covariant dualizer with
  pointwise pairing `Σᵢⱼ h(vᵢ,vⱼ)²`; canonical full support proves integrated
  separation and bulk injectivity. Only the bulk skew identity remains. On the actual
  fixed throat, the pre-existing tensor operations are now bundled as a real
  module and the intrinsic integrated pairing likewise defines a canonical
  linear realization in the algebraic dual. Its injectivity is equivalent to
  separation by the pairing and is now proved by the concrete finite-frame
  smooth positive dualizer, without diagonal definiteness. Coadjoint
  equivariance remains equivalent to integrated skew-adjointness for any
  supplied throat representation.
  The unconditional throat realization and these criteria are integrated in
  both the nonlinear BRST certificate and the global BRST frontier.
   The global frontier additionally carries the complete nonlinear
   certificate, the bulk geometric metric dual and the functorial tensorial
   algebraic coadjoint closure for the canonical Maxwell action and every
   supplied metric Lie action.
   A separate canonical tensorial packet now instantiates this closure with
   the concrete Maxwell and metric Cartan representations.
   The bulk geometric bridge is scoped to one supplied representation and its
   integrated skew identity.
  On genuine throat tensors, bilinear separation and integrated
  skew-adjointness now construct the faithful geometric coadjoint bridge
  directly through a global frontier gate. A nonzero symmetric Lorentzian
  tensor with nilpotent raised endomorphism and zero quadratic trace formally
  rules out diagonal definiteness as the generic proof route. The same model
  proves bilinear separation on all symmetric tensors. A new positive
  smooth-dualizer gate discharges localization and full-support promotion
  completely: it implies integrated separation and dual injectivity, and
  yields the coadjoint bridge only with a supplied integrated skew identity.
  The existing finite smooth generating frame now defines
  the positive energy `Σᵢⱼ h(vᵢ,vⱼ)²`, proved to separate tensor pairs without
  a global basis. The finite covariant rank-one dualizer and its exact
  sum-of-squares trace identity are now proved abstractly. The remaining
  bundlewise contraction theorem now proves all frame coefficients and both
  sector energies smooth, so continuity is discharged automatically by a
  stronger global BRST gate.
  Frame contractions are now genuine smooth covector sections, their outer
  and symmetric products are genuine smooth tensors, and smooth scalar
  multiplication is available. The finite weighted symmetric sum is assembled
  and specialized to both intrinsic throat sectors. Its exact pointwise
  trace-pairing identity is proved through an intrinsic rank-one contraction
  lemma, avoiding transport across the local tangent-space wrappers. Thus only
  integrated skew-adjointness remains in this global coadjoint gate.
  The tensor and Maxwell pullback generators are additive on differentiable
  orbits and homogeneous in the field slot, yielding field-linear maps under
  an explicit orbit-differentiability contract. The canonical intrinsic metric
  has zero generator along the complete time-translation subgroup, registered
  by the global BRST frontier; realization of the unrestricted action by
  concrete flows remains open. In
  the Maxwell sector, bilinear smooth
  contractions separate potentials through the finite tangent frame, and a
  bilinear action satisfying Cartan evaluation now yields the bracket
  representation automatically. The generic residual is tensorial in its
  second field, produces a cotangent-fiber map via `TensorialAt.mkHom`, and is
  specialized to each component of the actual smooth D8 potential. Their
  Hom-bundle regularity is proved uniformly; the resulting global action is
  smooth and bilinear, packaged as `GaugePotentialCartanActionData`, and
  upgraded to the canonical Lie representation with its bracket theorem. The
  induced algebraic coadjoint antifield has zero obstruction and its
  evaluation pairing is BRST invariant; no geometric/integrated Maxwell dual
  is claimed.
  Reusing the existing
  smooth tensor/two-vector contraction gives
  the metric analogue: finite-frame evaluation separates tensors and Cartan
  evaluation forces the metric bracket law. Its finite local formulas are now
  assembled into a global smooth bilinear action, packaged as
  `symmetricTensorCartanActionData` and upgraded to the canonical metric Lie
  representation with its bracket theorem. Together with the Maxwell datum,
  this gives the concrete tensorial representation and closes its algebraic
  Maxwell/two-metric coadjoint BRST certificate. No geometric or integrated
  tensorial dual is inferred. Canonical time/rotation invariant-measure IPP
  is now public and yields exact integrated skew on LL coefficient fields.
  It does not prove the intrinsic tensor-pair identity for arbitrary ghosts;
  fixed-background skew needs Killing and measure-preserving scope, or
  simultaneous transport of the background.
  The time-translation bulk ghost and all three canonical bulk rotation
   ghosts now restrict exactly to their throat ghosts by the derivative of the
   canonical inclusion. This does not imply tensor skew. The rotation pullback
   orbit is concrete, and the intrinsic raised pairing and two-sector pairing
   are pointwise natural under pullback. Its canonical-measure integral is
   invariant under every finite rotation, and its scalar derivative at angle
   zero vanishes by constancy. A public generic chain rule differentiates every
   fixed-fiber `SmoothThroatField` composed with the rotation as its `mvfderiv`
   along the throat ghost. It does not derive tensor pullback. Tensor-pullback
   angle differentiability, the pairing chain rule and an independent
   generator/action identification remain before skew or coadjoint transport;
   the throat tensor orbit for time is not yet bundled.
  Each finite throat rotation is now a genuine smooth diffeomorphism with a
   smooth pullback on symmetric throat tensors and exact zero-angle identity;
   the ambient Minkowski form and intrinsic cover Lorentz tensor are exactly
   rotation invariant. Pointwise quotient/throat pairing naturality and finite
   integrated invariance are closed, as is the zero derivative of the
   integrated scalar curve. The fixed-fiber field chain rule is public but
   does not differentiate tensor pullback. Tensor-pullback angle
   differentiability, the pairing chain rule and the generator/action bridge
   remain before skew or coadjoint transport.
  On the bulk metric pair, the genuine time-flow orbits,
  intrinsic-background fixity, preserved canonical integral and zero
  derivative of the invariant scalar pairing orbit are explicit. Pairing
  pullback naturality follows from conjugation and trace invariance. The
  pointwise generator/action bridge and differentiation through the
  integrated pairing remain before skew.
  The Maxwell curvature pairing was audited and is gauge-degenerate, so it is
  not used as a one-form antifield dual. The exact
  supplied affine nine-block diffeomorphism-symmetry contract implies
  assembled-action invariance and the Euler/Noether identity. The same
  certificate separately records nonlinear-packet square-zero and boundary
  stability, without identifying its differential with the action. Constructing
  the affine contract remains an action obligation. A complementary nonlinear
  complete-flow interface now handles field-dependent diffeomorphism
  generators and derives exact action invariance plus Euler horizontality
  from termwise invariance. Transported-measure covariance now reduces
  exactly to the fixed-measure nine-block contract under measure preservation,
  with a scalar-action instantiation for every measure-preserving
  diffeomorphism using its canonical metric pullback. The geometric chart
  flow and all nine exact Candidate-A
  block covariances remain open. Linearized nonlinear Noether gives
  `H(v,G)+E(DG·v)=0`, and therefore a two-sided Hessian kernel at critical
  configurations, including through any supplied dense global-tangent/chart
  bridge. The span of the differentiable nonlinear-flow generators is now a
  two-sided kernel submodule, with exact flow-only and combined `U(1)²`
  Hessian quotients.
  The native finite
  null-generator reparametrization theorem is now connected exactly to the
  ninth `finiteBV` block, with only the two density-integrability hypotheses
  left explicit; it is not yet the affine fixed-measure ghost action required
  by the nine-block contract. The retained PT-fixed nondegenerate intrinsic throat metric now has
  an actual pointwise inverse; the resulting traced pairing and graded-skew odd
  bracket are PT/exchange covariant and compatible with the bulk-gradient
  traces. The pairing is bilinear, and its ultralocal `1/2 ⟨h⁺,h⁺⟩` action has
  the exact quadratic expansion on every affine smooth throat-antifield line;
  its `HasDerivAt` is precisely the pairing with `antifieldGradient`. The
  intrinsic metric in both sectors gives action `3 ≠ 0`. The same action
  generates `(h⁺,0)` and obeys the pointwise CME. Local trivializations and
  continuous inversion of the finite-dimensional musical map prove global
  continuity of every smooth pairing density and discharge all `L¹`
  obligations. Canonical-volume action/bracket integrability, the integrated
  quadratic expansion and true `HasDerivAt` equal to the gradient pairing are
  therefore unconditional; PT/exchange covariance and the represented
  integrated CME remain exact. The analogous certified throat functionals
  yield a rank-one nonlocal master with exact derivative, functional CME,
  generated square-zero BRST and a nonzero throat witness. Lorentzian
  preservation of affine variations, arbitrary general-throat
  inversion/classification, derivative-dependent kernels, completed spaces and
  arbitrary BV functionals remain open;
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
  exactly with sector/coupling exchange; extension of the proved canonical
  normal derivative to general-metric Israel/null conditions remains open;
- **T/C** the genuine bulk differential `dφ` now evaluates on a representative
  of the differential normal quotient, transforms with the one-loop normal
  sign, pairs globally with a twisted normal section, and yields an action and
  weak stationary balance. Its splitting is algebraic pointwise; the canonical
  latitude unit normal is smooth, while arbitrary-metric unit normals, Israel
  jumps and null riggings remain open;
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
  bound. Joint `C∞` latitude regularity and the exact tangent-map identity
  close compact uniform coefficient/integrability control unconditionally.
  The positive collar is explicitly homeomorphic to the band
  `x₀ ∈ Ioc(0,sin 1)`; the exact quotient/time and reciprocal-cosine steps,
  followed by spherical radial and planar polar disintegration, prove physical
  coarea and yield the unconditional canonical trace bound/operator. Its
  homogeneous Dirichlet kernel is closed, complete and nonempty, with exact
  smooth zero-trace agreement. A nested finite `ℓ²` renorming closes the same
  jets in a genuine Hilbert space continuously linearly equivalent to the
  original graph norm. Its transported Dirichlet kernel has a contractive
  orthogonal projection, an exact orthogonal decomposition and an exact
  continuous linear equivalence with the graph-Dirichlet kernel; intrinsic
  Sobolev identification remains separate;
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
and the finite null-generator action now has actual inaffinity,
expansion-counterterm and endpoint-joint contributions with exact finite
reparametrization invariance. Its ambient area/generator geometry and
`NullFaceIntervalIntegrability` remain supplied. The canonical scalar cut-bulk
Green--Stokes formula and its Dirichlet/PT closures are proved; general
gravitational boundary-flux cancellation, covariant Bianchi/constraints, full
stability, anomalies, normalization and finite counterterms remain open. The
scoped ledger is
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
- **T** the effective deck structured-jet groupoid has a single isotropy stratum with trivial stabilizers, and every supplied representation sends its endomorphisms to identities;
- **O** extend this beyond deck isotropy to the SpinC fibers, invariant scalar algebra and global equivariant pairing module;
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
lake build JanusFormal.Branches.FundamentalGeometryPELemmaAudit
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

- **I/T** the Peetre–Slovák/Whitney reduction now has a complete written analytic proof, while its Lean-kernel formalization remains explicitly open;
- **T** the corrected five-lemma abstract/local audit is assembled in Lean, including the constructive Lemma 2 equivalence and finite Lemma 3/4 fragments;
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
- **T/C** the physical `K/J` operators and gauge Sobolev/cohomology are now
  constructed on the intrinsic Janus field/domain package, and the regular
  global action is assembled separately. Its actual chartwise Hessian is now
  the symmetric Frechet derivative of the exact Euler map. The physical
  tangent and physical common domain are now explicitly D10-free; a legacy
  extended tangent/domain retains a split D10 factor only for
  regulator/determinant work. The former whole-tangent-to-`ℓ²` equivalence is
  therefore not a physical target.
  For every certified chartwise paired `U(1)²` symmetry, the exact Noether
  identity now gives two-sided Hessian degeneracy and a canonical symmetric
  quotient. The D10-free bulk/SpinC/LL physical domain and the extended
  bulk/SpinC/D10/LL regulator domain are both concrete. The complete SpinC
  coefficient tower now has both signed
  first-order branches at the actual period. Its square recovers the old
  geometric `D²` weights, and properness proves that `2D + m²` is Fredholm for
  every mass coefficient, allowing a finite resonant kernel. The maximal
  squared SpinC domain is now unitarily the zero tower plus the positive D10
  domain, with exact unbounded-operator conjugacy and graph-energy
  preservation; this remains a spectral comparison, not physical field
  content. The LL Riesz identity is now appended on its positive-energy
  completion using exactly the canonical divergence-free frame of the global
  action; its smooth pairing is the actual LL mixed Hessian. Equality between
  the native real `ℓ²` pairing and the real part of the complex pairing proves
  self-adjointness of the enlarged physical operator without an extra
  coherence hypothesis. The D9 gauge–ghost symbol defines its maximal,
  generally unbounded `ℓ²` multiplier without an upper symbol bound. A
  positive gap away from finitely many characteristic modes gives a dense
  self-adjoint closed operator whose maximal-domain realization itself has
  closed range and finite kernel and cokernel. The corrected D10-free
  D9/two-sector signed-SpinC target, and its `llField` enlargement, have the
  same properties. Candidate-A matter now directly uses the primitive SpinC
  sections. Its smooth and graph quadratic actions agree on the finite
  spectral core; the graph second Fréchet derivative is exactly `2D + m²`
  and is Fredholm. The `llField` same-action/Fredholm statement is exact.
  The remaining `llAuxMetric × llMeasure` directions now also have an exact
  symmetric Hessian derived from the global action, an injective dense Hilbert
  graph completion and a bounded Riesz representative agreeing on the smooth
  core. The pure-measure radical is closed and its action-faithful Hilbert
  quotient is explicit. The descended operator is injective exactly when
  this radical is the full weighted kernel; vanishing LL energy weights can
  obstruct that equality, and closed range still needs coercivity. The full
  graph Riesz operator is now proved bounded self-adjoint. A generic Hilbert
  reduction and its LL specialization show that closed range plus
  finite-dimensional radical automatically imply finite-dimensional
  cokernel; these are the only two independent off-shell LL estimates left. The
  fixed canonical GHY control is identically zero and therefore has its exact
  zero same-action Hessian; the mobile sourced Robin summand is retained.
  Exact linear symmetries, including a supplied smooth-diffeomorphism
  symmetry, combine automatically with `U(1)²`.
  For a supplied differentiable nonlinear flow, the exact linearized Noether
  identity now retains the field-dependent `E(DG·v)` term and reduces to
  left/right Hessian degeneracy precisely at critical configurations. The
  span of all pointwise generators and its sum with the physical `U(1)²`
  directions now carry exact symmetric Hessian quotients.
  The authoritative obligation ledger is the
  [`HESSIAN-GLOBAL-01` closure map](hessian_global_01_closure_map.md); lists in
  this roadmap are dependency history only.
  H05/P1 is now closed by
  `regular_general_metric_c2_einstein_hilbert_gate`: the unrestricted local
  general-metric family is `C²` and its physical value is exactly the existing
  intrinsic Einstein--Hilbert action. The live dependency chain starts at P2.
  `HESSIAN-GLOBAL-01` remains an open analytic `FRONTIER`. The local-chart
  interface is no longer structurally blocked, but the existing zero-Hessian
  no-go forbids deriving the terminal Fredholm realization from `C²`
  regularity alone. The open-domain local-chart API is available; two earlier model mismatches
  are also removed: D10 was deleted from the physical target and
  matter was migrated directly to primitive SpinC. Typed abelian and
  diffeomorphism gauge fermions also provide distinct `c/c̄/B`, nilpotent
  BRST, exact `sΨ`, symmetric Hessians and the existing FP principal symbols
  at D9 covector level. Their two sector-indexed Abelian triples plus the
  diffeomorphism triple (nine global smooth species), D10-free
  enlarged tangent, real-module structures and universal square-zero
  nonminimal differential are now explicit. The gauge-fixed tangent is
  restricted to zero legacy coefficient ghost/auxiliary directions, so these
  species are not duplicated. The paired global rule
  `sA = -dc`, its finite-measure `sΨ`, and the bridge to the actual
  Candidate-A metrics, Maxwell potentials and nonminimal fields are now
  explicit as well. The global smooth Lorenz
  codifferential exists for every supplied general metric, its actual
  Faddeev--Popov composite is `δ_g d`, and the canonical specialization has
  exact `δ(d c)=+□c`. Intrinsic paired potentials now inject linearly into the
  corrected minimal physical tangent. Their Lorenz feature has a dense
  injective graph completion whose bounded symmetric Riesz representative has
  the exact Lorenz kernel and agrees with the reduced on-shell BRST Hessian;
  the graph is now a global linear Hilbert chart with an explicit `C∞`
  quadratic action and exact constant second Fréchet derivative. Its common
  smooth core injects jointly into that chart and the minimal tangent. Only
  the differential Green/adjoint formula still awaits a genuine Stokes
  theorem. The induced Levi-Civita derivative has its
  complete rank-three overlap law, and its direct chartwise contraction now
  glues to the smooth global divergence. Together with the existing trace
  differential this closes the complete smooth de Donder one-form and its
  local formula. The resulting operator is now bundled linearly; its smooth
  inverse-metric contraction integrates to a symmetric bilinear form with
  exact quadratic polarization. Finite-frame `L²` coordinates and the raised
  feature give it a faithful refined Hilbert graph with dense injective smooth
  range. A bounded symmetric cross-form extends the Lorentzian pairing exactly
  to this graph, and the associated quadratic action is `C∞` with that constant
  second Fréchet derivative. Two metric copies and the Lorenz graph now form a
  physical metric-plus-Abelian gauge `C²` subchart; its common smooth core
  injects into the corrected typed tangent with nonminimal coordinates fixed
  at zero. The unbounded
  zero-quotient-Hessian no-go still rules
  out the historical D10-extended realization. The complete
  `llAuxMetric × llMeasure × llField` core now has an injective dense graph
  completion and a bounded symmetric Riesz representative equal to the full
  unchanged LL action Hessian, cross terms included. Its quadratic graph
  action is `C∞` with that constant second Fréchet derivative;
  coercivity/closed range remains unproved off-shell. At a stationary
  zero-flux background, the independent measure equation forces
  `llField = 0`; all auxiliary weights and cross projections vanish, and the
  quotient by the exact field-projection kernel is continuously equivalent to
  `LLH1Space`. Its quotient Riesz operator is the identity, hence Fredholm of
  index zero. This is an on-shell reduction, not off-shell LL coercivity. The
  gauge chart, primitive SpinC
  matter graph and complete LL graph now form one physical bulk graph product
  with a `C∞` quadratic action equal to the sum of the three graph actions and
  an exact block-diagonal constant Hessian. This quadratic sum is not yet
  identified with the pullback of the complete nonlinear covariant action. Its
  common smooth core is injective and dense for the actual product graph norm.
  At the physical metric and mass, an injective linear map records jointly the
  graph point and its exact `GlobalPhysicalFieldTangent` slots. This core-level
  bridge does not turn arbitrary completed graph vectors into smooth fields.
  The Abelian nonminimal extension now has an off-shell graph-feature
  completion: its injective smooth map reuses Lorenz and adds
  `B/c̄/c/δ_g d c`; its `C∞` quadratic action has the canonical-volume `sΨ`
  polarization as Hessian, and its core maps injectively to the corrected
  typed gauge-fixed tangent. Projected-operator closability is not claimed.
  The Abelian extended bulk now performs that nonduplicating replacement of
  the old Lorenz factor. Together with the de Donder pair, primitive SpinC
  matter and full LL graph, it has an injective dense core, a `C∞`/`C²`
  quadratic action with exact sector-sum second Fréchet and an injective typed
  core attachment. This sum is still not identified with the pullback of the
  complete nonlinear covariant action. The action-selected diagonal
  diffeomorphism graph now replaces both de Donder factors: its two-metric/
  one-triplet BRST core is square-zero, dense and injective, and its weighted
  `sΨ` has the exact bounded Hessian/Riesz/action. The resulting diagonal ×
  Abelian × matter × LL bulk product has an exact `C²` assembled Hessian and
  an injective graph/typed-core raccord, without a new axiom or duplicated
  nonminimal sector. This four-factor finite maximum-norm product now has an
  equivalent nested `WithLp 2` Hilbert realization, with the same
  dense/injective typed core and the same exact `C²` action. Its block Hessian
  has a bounded self-adjoint Riesz representative. This closes the aggregate
  diagonal BRST bulk Riesz step. Independently rescaling each finite null-face
  normalization now gives a Euclidean Hilbert boundary chart on which the
  exact GHY plus null/counterterm/joint action is constant; its same-action
  Hessian and self-adjoint Riesz representative are zero. This does not cover
  general boundary geometry.
  `P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D`
  makes the central comparison a theorem on this
  same smooth core: after projecting the corrected typed tangent into the
  legacy tangent with D10 exactly zero, any supplied existing variational-chart
  bridge gives the former graph-plus-residual comparison. The exact split in
  `P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D` proves that
  this residual is the physical seven-block Hessian plus the matter--LL
  same-action mismatch. The correct graph is therefore augmented by the
  retained physical Hessian, and equality is equivalent only to the
  matter--LL identification. A concrete matter-only
  covariant subchart is now available:
  `P0EFTJanusProgramPGlobalCandidateAMatterFiniteGraphVariationalChart4D`
  equips the finite SpinC range with its inherited graph norm, proves the nine
  exact action blocks `C²`, and identifies the genuine chart Hessian with the
  pulled `2D+m²` graph form. This closes the matter chart raccord only; the
  total diagonal bridge and its general-metric/boundary residual remain open.
  `P0EFTJanusProgramPGlobalCandidateABoundaryReparametrizationVariationalChart4D`
  now gives the analogous exact covariant chart for independent null-generator
  normalizations: every action block is `C²`, the pullback is constant and the
  genuine Hessian is zero. General normal displacement and boundary geometry
  remain outside this chart.
  Its generic chart-extension theorem also proves that adjoining these
  parameters to any covariant chart pulls the Hessian back through the first
  projection. The matter-plus-normalization instance therefore has exactly the
  matter `2D+m²` form and zero mixed boundary blocks.
  `P0EFTJanusProgramPGlobalLocalVariationalChart4D` now supplies the correct
  ambient interface for the next metric step. Physical Candidate-A data are
  required only on an open admissible set `U` of a normed model, with `0 ∈ U`;
  termwise `ContDiffWithinAt` regularity becomes ambient `ContDiffAt` at every
  admissible point. Its Euler form and symmetric Hessian act on the whole model
  tangent space. Existing whole-space charts embed through `U = univ` with
  exactly the same action, Euler form and Hessian. The intrinsic root
  inhabitant is supplied below; a complete nine-block action inhabitant is
  still required.
  `P0EFTJanusProgramPGlobalCandidateADiagonalLocalCovariantHessianResidualBridge4D`
  now connects this interface to the completed diagonal smooth core at any
  admissible base point. It reuses the closed BRST/matter/LL blocks and proves
  the exact local comparison; `U = univ` recovers the former core Hessian and
  residual exactly. The physical/matter--LL split prevents the erroneous
  cancellation of Einstein--Maxwell and boundary dynamics.
  The reused positive-split raw spectral and Sylvester bricks now also give a
  `C²` root branch on an open zero-centered perturbation domain around every
  admissible raw target, with the exact square identity. This removes the
  pointwise root-regularity sub-obligation without restricting to diagonal or
  Minkowski metrics. A generic continuation theorem also upgrades every
  continuous square-root lift with pointwise bijective Sylvester operator to
  `C²` whenever its target is `C²`; local branch gluing is no longer an
  obligation.
  The intermediate uniform-field lift is now closed by
  `P0EFTJanusContinuousMatrixFieldContDiffLocalRootBranch4D`: on every compact
  base, pointwise Sylvester bijectivity gives a bounded field-space
  equivalence and an open zero-centered `C²` root chart with exact square.
  The scalar strong layer is now realized by
  `P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D`: the closed
  equalizer of the already available `C⁰ → L²` and `H¹ → L²` maps is a Banach
  space `C⁰ ∩ H¹`, with exact smooth-core lift and no Sobolev-embedding axiom.
  `P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0CoreClosure4D` then takes
  the canonical closed smooth core, proving completeness, injectivity into the
  equalizer and dense smooth range without assuming a smoothing theorem.
  `P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0SmoothLeibniz4D` closes the
  exact smooth product rule `(fg, f·dg + g·df)` and packages the product as a
  bilinear map into that core.
  `P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0ProductExtension4D` then
  derives the uniform strong bound from `L∞·L² → L²` Hölder multiplication and
  extends it canonically to a continuous bilinear product on the complete
  core, agreeing exactly with smooth multiplication.
  `P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0MatrixProduct4D` then
  assembles the finite `4 × 4` product, proves exact compatibility with both
  smooth and continuous representatives, and makes squaring `C∞` with the
  expected Sylvester derivative.
  `P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0LocalRootBranch4D` then
  proves that the pre-existing pointwise inverse family is smooth for every
  general smooth regular root, assembles its finite coefficients into a
  bounded inverse on the strong core, and constructs an open zero-centered
  `C²` root chart with exact square identity. No diagonal restriction or new
  axiom is introduced.
  The arbitrary finite-size extension is now also green:
  `P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D`
  provides associative strong multiplication and smooth square/Sylvester
  calculus for every finite matrix size, while
  `...FiniteMatrixLinearEquivLift4D` promotes smooth pointwise-bijective finite
  operator families to bounded equivalences on the complete strong core. The existing finite smooth tangent
  generators then encode the intrinsic Candidate-A root through
  `P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D`. Their redundancy
  is represented by a smooth idempotent `P`, and the new strong finite-frame
  corner gates construct the closed complete algebra `P M_N P`, prove that the
  intrinsic root belongs to it, and furnish a generic Banach local-inverse
  certificate. Under bijectivity of the strong corner Sylvester at the center, its
  domain is open, contains zero, the branch is `C²` throughout that domain and
  its square is exact there. No global frame is introduced.
  `P0EFTJanusProgramPGlobalStrongH1C0AnalysisDomain4D` then applies it to the
  existing finite metric/gauge/ghost slot product, proving completeness,
  coordinatewise `L²` compatibility and the exact smooth-tangent lift. The
  intrinsic finite-frame encoding, strong corner algebra and local-root API
  are now closed. The `...StrongFiniteFrameSylvester*` gates also close the
  regularity transport: intrinsic pointwise Sylvester bijectivity implies the
  strong-corner bijectivity and activates the full open-domain `C²` root branch. This is
  a regular-stratum theorem, since `GlobalCandidateAGeometry` does not itself
  rule out singular roots. The explicit regular-geometry subtype and its local
  chart predicate are now constructed. The positive physical-selection gate
  proves intrinsic Sylvester regularity of the stored selected root and
  activates the local branch without a new regularity axiom. The local-root
  joint-regularity gate further proves that a strong `C²` target family gives
  an open pullback domain, a `C²` selected root, exact squaring and jointly
  continuous parameter--spacetime coefficients.
  The uniform order-two layer is now concrete: the complete scalar C² jet
  core has exact second-order Leibniz multiplication and a continuous map to
  the strong core; finite C² matrices have associative multiplication, smooth
  squaring and the exact Sylvester derivative. The canonical matrix branch is
  C² on an open domain and its complete coefficient jets are jointly continuous.
  The intrinsic finite-frame projector also defines a complete C² corner
  containing the selected root, and intrinsic Sylvester regularity gives the
  bounded corner equivalence and open-domain C² branch. This closes the
  higher-order local-root problem without a new axiom. The strong
  Einstein--Maxwell closure gate also makes finite-measure integration a
  continuous linear functional: strong `C²` lifts of the actual
  volume/curvature and volume/pairing now imply `C²` for the genuine
  Einstein--Hilbert and Maxwell action lines. Constructing the actual
  general-metric map into the C² core, its curvature/pairing lifts and the
  jointly `C²` nine-block action family remains.
  The dense diagonal graph core and typed raccord are already faithful. The
  historical spectral D9 packet `ι × Fin 8` remains only a reduced Fredholm
  model and must not be counted as the complete action-field multiplicity.
  Standalone scalar-FP closure is now additionally reduced to existing data:
  supplied completed-boundary
  inputs, a Lagrangian condition and the existing analytic-closure package
  give dense component domains and actual-adjoint-domain equality, with a
  dense/injective finite paired inclusion matching the true FP map on its
  admitted smooth core. No analytic-package inhabitant or total chart is
  constructed. The stronger existing graph/direct-coercive endpoint is also
  connected: canonical-normal PDE data, a graph estimate and shifted
  coercivity already yield unconditional Rellich, a bounded real resolvent,
  actual scalar adjoint-domain equality and exact FP agreement on admitted
  smooth vectors. They also reconstruct the global Green--Stokes datum with
  definitionally the same scalar core. Those endpoint data are not inhabited. Closure
  now also has the genuine mono-metric diffeomorphism FP operator
  `c ↦ B_g(L_c g)`, obtained by composing the existing Cartan metric action
  with de Donder. The one-component no-go excludes preserving both de Donder
  squares with one triplet. The new kinetic-adjoint bridge instead derives the
  unique weights `1/(2κ₊), 1/(2κ₋)` from the two existing Einstein action
  coefficients, proves the four-dimensional adjoint identity, constructs the
  global weighted condition and FP map, and isolates noncancellation of the
  total weight as the spatial ellipticity criterion. For each supplied metric,
  a complete mono-metric
  real-linearized off-shell `h/c/c̄/B` graph now realizes square-zero BRST,
  exact linearized `sΨ`, a
  symmetric Riesz/Hessian, `C∞`/`C²` action and injective typed nonminimal
  attachment. Closure
  now follows one dependency chain: construct the actual general-metric map
  into the C² variational chart and its curvature/pairing lifts, retain and realize the
  arbitrary-general-metric Einstein--Maxwell and general normal/boundary
  Hessians while closing only the matter--LL mismatch, then establish
  differential Green-adjoint/domain data,
  off-shell LL closed range and finite radical, correct nonduplicated
  multiplicities and the same-action Fredholm sum on an explicitly
  constructed nondegenerate elliptic realization. The exact
  generic null-boundary chart with an independent, uncancelled `Theta`
  coordinate must be built on regular `Theta ≠ 0` strata: the existing no-go
  excludes even `C¹` across `Theta = 0`. It does not exclude constrained
  subcharts with a proved cancellation. On those regular strata, the exact
  pointwise density Hessian is now the existing screen/gravitational
  coefficient times `(u,v) ↦ Theta⁻¹ u v`; its geometric integration remains.
  The normal sector now has a descended deck-equivariant collar family with
  exact zero section, local coordinate velocity and zero scalar acceleration.
  Each member is injective; its scalar lift is `C∞` on the cover and the
  descended `(point,parameter) ↦ normalGraph parameter point` is jointly
  `C∞`. After transport along the zero graph, its derivative at zero is the
  existing global orthogonal normal lift. The induced action/Hessian remains.
  The exact
  Parseval/unitary comparison between the independent integral geometric `L²`
  completion of the whole smooth SpinC core and the completed spectral norm
  is now closed. It is exact inside every finite level/sector/circle block;
  exact fundamental-domain Fourier cancellation additionally proves
  orthogonality for distinct circle modes in each fixed sector, uniformly
  across levels. The two opposite sectors are pointwise and integrally
  orthogonal for arbitrary levels and modes. The rotation Casimir and
  invariant round-sphere measure also prove exact orthogonality across levels
  at fixed sector/mode. These axes now assemble into a canonical Hilbert-sum
  linear isometry whose image is exactly the joint closed block span. Dense
  range is equivalent to surjectivity and already yields the conditional
  unitary. Each individual signed branch now also has exact first-order
  Parseval coordinates and closed completed image; each complete two-sign
  block has Parseval and exact `D²`. Radial Clifford parity now proves linear
  independence of each signed raw family, hence finrank `2p+1` per sign and
  `2(2p+1)` for the full block. The integrated gradient/Casimir identity now
  proves exact orthogonality of the two signs inside every fixed spectral
  block. Distinct signed sector/circle/level labels, and the zero tower versus
  every positive signed block, are now orthogonal too. They assemble into one
  signed Hilbert-sum isometry with exact closed range. Polynomial monopole
  approximation and temporal Fourier completeness reconstruct the signed Hopf
  frame uniformly, so the range contains the dense smooth core and therefore
  equals the whole geometric SpinC completion. This gives the unconditional
  ambient geometric unitary. The exact Hessian-label refinement is also
  closed: a PT involution corrects only the undoubled zero tower, the resulting
  unitary sends every coordinate vector to a true smooth first-order Dirac
  eigensection, and finite packets intertwine the genuine differential
  expression `2D + m²` with its self-adjoint Fredholm maximal multiplier.
  Its single null-curve construction gives the
  exact `2p+1` multiplicity, linear independence, ambient harmonicity and
  spherical energy `p(p+1)` for every `p`; no `p ≥ 4` level-by-level
  expansion remains. The corresponding null powers are genuine smooth
  quotient-bundle sections. Their uniform Dirac recurrence proves the exact
  geometric `D²` equation and generates the signed seeds. Every positive and
  negative label at every positive level is now tied to its genuine smooth
  first-order eigensection; the undoubled zero tower is likewise realized
  for either orientation of the period by the exact PT mode reindexing. The
  two signed branch spans are disjoint and exhaust each scalar/gradient seed
  block. Strict growth of
  `p(p+1)` separates the squared-Dirac eigenspaces, making the
  finite-support synthesis jointly injective across every positive level at
  fixed sector/circle mode, with exact diagonal `D²` intertwining. Smooth
  restriction, the all-level Lichnerowicz input, within-level multiplicity
  and inter-level linear separation are therefore closed. At every arbitrary
  fixed positive level, doubling cover time additionally identifies the two
  normal-root sectors with odd/even integer Fourier modes and proves joint
  injectivity across both sectors, every circle mode and every multiplicity.
  These two axes are now combined in one finite-support synthesis over every
  positive level, both sectors, every circle mode and every multiplicity. It
  is injective and exactly intertwines geometric `D²` with its diagonal
  coefficient operator.
  The Hopf zero tower is now adjoined in that same canonically indexed
  synthesis, which remains injective and `D²`-diagonal over the complete
  coefficient mode set. Every complete label has real and
  intrinsic-imaginary smooth representatives; `p = 1,2,3` are compatibility
  checks. The actual finite smooth eigensection span now has an injective
  dense coefficient analysis; its coefficient-induced Hilbert completion is
  canonically unitary to the full coefficient `L²`, and its maximal `H²`
  squared Dirac is exactly conjugate, coercive and bijective.
  Independently, the descended doubled Hermitian fiber pairing is smooth,
  integrable and positive definite against the canonical throat volume on
  every smooth primitive SpinC section. Its geometric Hilbert completion has
  dense smooth core without using spectral coefficients. Geometric
  Gram--Schmidt supplies an exact Euclidean Parseval isometry in every fixed
  multiplicity block and preserves the intrinsic `D²` eigenvalue.
  First-order SpinC
  diagonalization and completed Fourier extension are theorems,
  nine-block diffeomorphism
  invariance and identification of the actual bulk/metric–Maxwell–matter–
  ghost–boundary Hessian, excluding the closed LL factor but including its
  remaining nonspectral sectors, with the constructed elliptic Fredholm
  operator. A formal zero-Hessian
  obstruction shows that this last result does not follow for arbitrary
  couplings.

# Programs A/B/C and absolute scale

The integrated scale no-go proves that the available geometry, Dirac/LL,
local heat and charge laws preserve a common rescaling orbit. Any successful
input must break that orbit rather than merely reparameterize it.

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
| `FundamentalGeometryPEJetUniversality` | PR 10 merged; effective-deck jet head green, while Program P separately carries the actual twisted PinC/spinor bundles |
| `FundamentalGeometryPEInvariantPairings` | focused CI green |
| `FundamentalGeometryD`, `D7`, `D8`, `D9`, `D10`, `P`, `P-F` | focused heads green; Program-P physical K/J, global naturality and regular action assemblies are integrated |
| D9 | complete `ℓ²` Hilbert–Fredholm realization proved under uniform ellipticity; identification with the global gauge-fixed Hessian remains open |
| D11 | supported naturality/finite-jet head; global Fredholm realization open |

See `current_status.md` and `janus_branch_registry.md` for the exact operational status.

# Shortest honest research path

```text
0. complete the chosen D10-free gauge-fixed model: physical tangent/domain
   and target already exclude D10, matter is directly primitive SpinC, typed
   global nonminimal modules and the actual paired Abelian gauge-fixed action
   are available, intrinsic metric and paired-potential directions inject into
   the typed tangent, and the two exact de Donder graph actions plus Lorenz are
   assembled in a common physical gauge `C²` subchart. Together with the
   primitive SpinC and full three-slot LL graphs, they form a physical bulk
   graph product with a `C∞` quadratic sum and exact block-diagonal
   sectorwise same-action Hessian. This sum is not yet the pullback of the
   complete covariant action. Its common smooth core is graph-norm dense and maps
   injectively to the exact typed physical slots; the LL kernel is exposed and
    GHY is closed. The Abelian nonminimal off-shell feature completion/action
    at canonical volume and its typed core attachment are also constructed.
    Projected intrinsic FP closability follows conditionally from the existing
    scalar Green datum; the existing completed-boundary analytic package now
    also yields conditional componentwise actual-adjoint-domain equality, but
    no inhabitant of that package is constructed. The pre-existing
    graph/direct-coercive endpoint further removes separate adjoint-regularity
    and Rellich assumptions and is now identified with the smooth intrinsic FP
    operator, but its PDE/graph/coercivity data remain uninhabited. Its nonduplicating extended bulk
   replacement, equivalent nested-`L²` Hilbert chart, exact sector-sum `C²`
   action, self-adjoint aggregate Riesz representative and injective dense
   smooth core are constructed. The true mono-metric diffeomorphism FP map and complete
   off-shell BRST feature graph are closed. Their two Candidate-A copies now
   have the unique kinetic-adjoint weighted coupling to the single typed
   diagonal triplet; the shared off-shell graph and its insertion into the
   total bulk graph are constructed. LL is Fredholm of index zero after the proved stationary
   zero-flux quotient reduction, not off-shell;
1. extend the assembled diagonal bulk graph/typed smooth-core bridge through
   the constructed C² jet/root core by building the actual general-metric map,
   identify its quadratic action with the
   nonlinear action, then add same-action blocks for the normal and general
   boundary directions; the finite null-reparametrization Hilbert block is
   already closed, and the normal collar itself is
   already jointly `C∞` in throat point and parameter;
2. extend the chartwise Euler/physical `U(1)²` Noether closure to the raw-field
   atlas and one nonlinear exterior BRST/BV derivation with boundary descent;
3. extend the finite-core primitive SpinC same-action identity through the
   final chart, then identify the remaining metric/normal/mixed-Maxwell/
   null-boundary blocks and prove full-LL closed range plus finite radical
   off-shell. Construct explicitly the nondegenerate elliptic continuation,
   boundary realization and common domain required by the Fredholm no-go;
4. if physical heat agreement is required, prove D9 high-energy summability
   and an elliptic LL compact-resolvent/heat trace, then identify the closed
   nuclear reference regulator with the global Hessian after the action and
   operator field contents have been made compatible; this remains downstream
   of `HESSIAN-GLOBAL-01`;
5. lift the proved circle determinant metric/flat connection and PT/inflow
   cancellation to the full family, including local/global anomaly and
   equivariant trivialization;
6. construct the structured SpinC/PT/Z4/BRST jet groupoid and descent data;
7. prove the higher-order structured jet-normal-form/integrability theorem;
8. extend the proved finite six-invariant natural classification to the full
   elliptic operator class;
9. extend the proved nonlinear Helmholtz/global functional closure to the
   full local horizontal jet variational bicomplex;
10. supply a microscopic normalization and finite-part law; the current
   hypotheses provably cannot close scheme independence by themselves;
11. compute the renormalized effective action and prove one stable vacuum;
12. close charge compatibility and the absolute scale.
```

Update: `P0EFTJanusMappingTorusGlobalSmoothScalarWave4D` closes smooth global
packaging, linearity, and finite-measure integrability of the canonical scalar
wave. `P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D` adds its global
smooth product and local gradient Leibniz law. Next remain the covariant
product jet and exact algebraic wave-contraction rule are now closed. Next
the jet is identified with the actual second derivative, and the global
  smooth gradient pairing/wave-product rule is closed. The spatial conformal
  EH Hessian and raw curvature bridge through scalar curvature are closed. Its
  restricted Einstein--Maxwell product-core extension is also closed: the
  potential block is the existing fixed-metric Maxwell Hessian and the mixed
  conformal--potential block is the existing same-action zero Hessian.
  Arbitrary metric-direction mixing still lacks a concrete metric-section
  chart.
The first spatial-conformal metric jet is now closed by
`P0EFTJanusMappingTorusSpatialConformalMetricJet4D`; inverse and Christoffel
are closed, and the companion curvature jet reaches Riemann, Ricci and scalar curvature.
### Closed: spatial conformal Einstein--Hilbert Hessian

The exponential spatial conformal line now has an explicit integrated second
variation and symmetric polarized Hessian. The spatial conformal metric,
curvature, Palatini and algebra gates now also prove the exact standard
scalar-curvature transformation from the raw coordinate Ricci construction.
The exponential specialization is global and the conformal volume ratio
identifies the genuine frame-free metric-volume Einstein--Hilbert action with
that differentiated curve. Thus the spatial conformal EH Hessian is closed
geometrically, not only as a reduced formal density.

`P0EFTJanusMappingTorusSpatialConformalEinsteinMaxwellCoreHessian4D` packages
this block with the arbitrary-potential Maxwell Hessian as one symmetric
bilinear form on the restricted product core. Its cross value is explicitly
the already proved `conformalPotentialFrameFreeMaxwellMixedHessian`, hence
zero by the genuine two-parameter same-action theorem. No arbitrary
Lorentz-metric chart is introduced.
