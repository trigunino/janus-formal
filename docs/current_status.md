# Janus Formal — Current Status

This is the canonical status document for readers who did not follow the research conversation. It distinguishes compiled algebraic theorems, executable audits, conditional geometric interfaces and genuinely open Janus constructions.

## 1. Repository integration

The consolidated scientific stack was merged into `main` on 12 July 2026 through PR 5 at

```text
d4b893b06983c5b65f481c24e2e71f2ba6ddd1ba.
```

Programs P-D and P-E were then advanced and merged into `main` through PR 6 on 14 July 2026 at

```text
92ade09c4f9aaab064840f934a42a50fb59bd171.
```

The merged PR 6 stack contains:

- the corrected finite-jet operator category and holonomic composition;
- invariant pairing modules and isotropy-stratification counterexamples;
- an action-groupoid core and exact orbitwise descent;
- concrete immersion and abelian-connection jet quotients;
- the universal low-order quotient represented by `(B,F)`;
- pointwise and smooth local adapted tangent/normal frames;
- the connection-corrected identity `B = II` and residual equivariance;
- moving-frame laws, normal transport and overlap Čech cocycles;
- oriented reduction to `SO(T) x SO(N)`;
- central Spin-lift and determinant-root defects with SpinC diagonal cancellation;
- concrete circle, matrix `SO(2)` and Mathlib Clifford `Spin(2)` models;
- the first Gauss--Codazzi--Bianchi algebraic identities;
- exact Codazzi and abelian Bianchi jet quotients;
- direct-product splittings of `nabla II` and abelian connection second jets;
- the algebraic normal Ricci equation;
- finite-dimensional Fréchet--Riesz construction of the shape operators from `II`;
- canonical pointwise and smooth normal-frame transitions;
- transition-jet bridges from frame derivatives to normal gauge extraction;
- a direct construction of the normal-frame transition derivative.

Program P-E was advanced again and merged into `main` through PR 10 on
15 July 2026 at

```text
96e60eb4df1db049f8488858c5a6b1fdb717b224.
```

## 2. Validation

The current `main` head is

```text
96e60eb4df1db049f8488858c5a6b1fdb717b224.
```

The theorem commits below the PR 6 merge were validated by its focused Lean
and Python workflows. The PR 10 theorem head was validated locally before
merge; this document does not claim an independent post-merge CI run for
`96e60eb4`.

The previously recorded successful runs include:

```text
Program PE jet universality       run 29268187119   Lean/Python success
Programs D and P integration      run 29268187102   all listed jobs success
Janus deep alpha completion       run 29268187105   Lean/Python success
```

PR 6 extends focused validation to include:

```text
JanusFormal.Branches.FundamentalGeometryPEJetUniversality
JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusNormalFrameSmoothTransition
JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusNormalFrameTransitionJetBridge
JanusFormal.Branches.FundamentalGeometryPEJetUniversality.Gates.P0EFTJanusNormalFrameTransitionDirectConstruction
```

Supported focused Lean heads include:

```text
JanusFormal.Branches.FundamentalGeometryD
JanusFormal.Branches.FundamentalGeometryDiracSpectral
JanusFormal.Branches.FundamentalGeometryD7SpectralTheory
JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation
JanusFormal.Branches.FundamentalGeometryD9ImmersedSpinCEllipticComplex
JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly
JanusFormal.Branches.FundamentalGeometryD11NaturalImmersionOperators
JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple
JanusFormal.Branches.FundamentalGeometryPEInvariantPairings
JanusFormal.Branches.FundamentalGeometryPEJetUniversality
JanusFormal.Branches.FundamentalGeometryPFCompatibilityHelmholtz
```

A green Lean head means that every imported theorem and proof compiles. It does **not** turn uninstantiated status fields into geometric objects or prove the complete physical Janus theory.

### PR 10 merged update (15 July 2026)

The PR 10 theorem head, now merged into `main`, was validated locally with

```text
lake build JanusFormal.Branches.FundamentalGeometryPEJetUniversality
```

The integrated head compiles. Independent post-merge remote CI is not claimed
here. New proved, scoped constructions are:

- existence of the smooth finite-dimensional Euclidean Levi-Civita/Koszul
  coefficient from a smooth positive-definite metric;
- a projected-seed atlas for the varying intrinsic normal spaces, with smooth
  orthogonal overlap maps and coefficient transition laws;
- the canonical one-chart rank-two Clifford SpinC Cech bundle with the supplied
  smooth abelian potential as connection data;
- a valid-chart low-order residual/SpinC action groupoid extracted from actual
  Euclidean immersion, metric-Koszul and gauge-potential derivatives.

These do not assert the full differentiable Janus jet groupoid or a nontrivial
global Janus SpinC bundle.

The current follow-on branch also proves that two actual valid projected-seed
chart extractions at the same base point are related by the canonical residual
normal-frame action, packages that relation as an action-groupoid arrow and
proves its identity and Cech composition laws. For invariant observables it
also constructs the unique chart-independent value at that fixed base point.
If the observable admits a smooth realization on the normed continuous-jet
coefficients, the descended observable is globally smooth by fixed-chart local
gluing. This remains low-order Euclidean descent, not effective descent for the
full Janus structured-jet groupoid.

The same branch supplies two conditional multi-chart packages. Given an open
cover, oriented cocycles, chosen Spin lifts, phase transitions and matching
diagonal defects, Lean packages the resulting SpinC transitions with pointwise
identity, inverse and Cech laws. This is a supplied transition presentation,
not a continuity/smoothness theorem or a geometric principal-bundle total-space
construction. Given local abelian potentials and additive overlap shifts, Lean
proves the affine first-jet law and, when every overlap shift is curvature-flat,
uniquely glues the local curvatures to a global smooth curvature function. Its
actual Fréchet derivative satisfies the cyclic abelian Bianchi identity. These
packages do not
derive their input from actual Janus characteristic classes, determinant-line
transitions or logarithms, and therefore do not construct the global physical
Janus SpinC bundle or connection.

## 3. Stable architecture

```text
D0/D8  mapping-torus and one-sided-throat topology
D2/D7  twisted Dirac, eta, heat-kernel and determinant constraints
D9     gauge-fixed elliptic-symbol and BRST/ghost gates
D10    determinant-line, Quillen and anomaly interfaces
D11    natural-operator and finite-jet gates

P0     moduli-geometry no-go
P-A    relative action specification / parent-bulk reduction
P-B    anomaly consistency and discrete selection
P-C    Helmholtz inverse variational problem
P-D    isotropy-stratified pairing and invariant-coefficient modules
P-E    structured jets, adapted frames, SpinC lifts and integrability
P-F    compatibility pullbacks, Helmholtz and Noether identities

A/B/C  quantum scale, nonlinear junction and charge compatibility
E      observational falsification after theoretical closure
```

Current D7 frontier: the infinite monopole heat trace and the two physical
`Z4` renormalized determinants are constructed, and the spectral product
coefficients agree exactly with the universal `a0/a2/a4` formulas. The
order-four Euler--Maclaurin identity, its uniform fifth-derivative remainder
bound and the normalized small-time limit are now proved without an external
analytic hypothesis. For the normalized circle heat semigroup, the maximal
strong right-generator domain on the full Fourier Hilbert space is now exactly
the squared-eigenvalue weighted domain; this is also proved equal to the actual
iterated domain of `D ∘ D`, and the generator is uniquely `-D²`. Abstract
functional calculus remains open. At every positive circle time, the heat
operator now also has an operator-norm-convergent expansion into explicit
rank-one Fourier maps with summable operator norms; its nuclear trace equals
the existing spectral heat trace. A general Mathlib trace-class API and the
full Fredholm/Quillen family and the
field/ghost-weighted anomaly problem remain separate and open.

D10 now also contains a concrete symmetric finite Fourier family: its matrix
entries depend holomorphically on complex holonomy, every cutoff is
algebraically Fredholm of index zero, and the induced top-exterior determinant
line has rank one. PT covariance and invertibility at both quarter holonomies
are proved. This remains a finite-mode milestone, not the global unbounded
Janus Fredholm family, physical Hessian, eta holonomy or Quillen/Bismut--Freed
package.

On the normalized infinite circle, the common maximal domain is now independent
of holonomy, holonomy changes are exact bounded scalar perturbations, the
complexified family is entire on that common domain and `(D-i)⁻¹` is explicitly
compact. Equipping the closed graph with its inherited complete norm turns the
same operator into a bounded Fredholm map: its range is closed, kernel and
cokernel are the same finite zero-mode space, the index is zero, and the
top-exterior determinant fiber has rank one with a nonzero section. This is
now complemented by the canonical bounded transform: it is self-adjoint,
Fredholm of index zero and 1-Lipschitz in holonomy in operator norm. Its only
fundamental endpoint crossings are identified exactly, related by the
large-gauge mode shift, and have opposite PT orientations; both quarter
holonomies are invertible. Each bounded Fredholm operator now also has its
actual rank-one `Hom(det coker, det ker)` fiber with a nonzero Fourier frame,
and the two endpoint fibers are related by an explicit bijective large-gauge
transition. Their dependent union is now topologized as a genuine complex
line bundle with an
explicit global trivialization, large-gauge clutching and quotient descent.
In its chosen Fourier trivialization it also carries a positive Hermitian
metric, a compatible flat connection, isometric parallel transport and
unit-norm closed holonomy.  This remains a normalized circle/Fourier model,
not an identification with the analytic Quillen/Bismut--Freed package of the
global Janus family, its families-index curvature or eta invariant.

## 4. Topology and Z4

For

```text
J(T,rho) = (S3 x R)/((x,u) ~ (rho(x),u+T)),  T != 0,
```

the combined integer action is now constructed as a free, properly
discontinuous topological action. Its effective orbit quotient, covering
projection and charted-space structure are explicit; the equatorial `S2`
induces an analytic map of quotients. The algebraic `S³` and equatorial `S²`
are identified with Mathlib's standard analytic spheres, and the effective
spacetime and throat quotients now carry installed analytic `ChartedSpace` and
`IsManifold` instances. Their covering projections are analytic local
diffeomorphisms. The throat inclusion is analytic, a closed topological
embedding, and has injective manifold differential with rank-one normal
quotient. Time reversal is an analytic involutive diffeomorphism on both
quotients and intertwines that same inclusion. Both effective quotients are
compact. A global `IsSmoothEmbedding` instance is now constructed from an
explicit local normal complement and the closed embedding. The null/joint
stratification remains open. The expected fundamental group is `Z`, not `Z4`.

The complement of the concrete equatorial `S2` in the unit `S3` is now proved
to be the disjoint union of two nonempty open sign sides. Reflection and one
deck iterate exchange them. In the effective mapping torus, the image of
either side is exactly the full throat complement, the two images coincide,
and PT preserves that complement. Explicit normalized affine paths prove both
sign sides path connected and identify them exactly as the connected
components of the two poles. The positive cover side and its quotient image
are path connected, so the effective throat complement is path connected and
connected.

On the fixed throat, the even-winding quotient now gives an actual
two-sheeted topological covering. Its half-period deck map is continuous,
involutive and fixed-point free; every fiber is equivalent to `ZMod 2`.
Moreover, the pulled-back associated normal line has an explicit global
topological product trivialization. The exact deck-sign cocycle now also
constructs a genuine analytic real rank-one `VectorBundle` on the effective
throat, with one circuit acting by `-id`. Each of its fibers is noncanonically
linearly equivalent to the corresponding differential normal quotient. These
equivalences are now chosen simultaneously and assembled into one
base-preserving, fiberwise-linear equivalence of dependent total spaces, with
the exact one-loop sign. A smooth atlas on the differential quotient family
and smoothness of this global comparison remain open, together with the
non-null/null/joint strata.

The two quarter phases now define actual global complex line-bundle cores on
the same throat. Their real underliers are analytic vector bundles, and their
transition squares recover the real normal sign for every winding:

```text
one real-normal loop       -1
square-root multipliers    +i or -i
two lifted loops           -1
four lifted loops          +1
```

Thus `Z4` remains a lift/holonomy phenomenon: the two root lines are explicit
additional global choices, not a canonical functor of the real line. The
ambient Clifford gate now constructs an actual Spin element for every pair of
unit reflections, proves that its projection is their exact product, and
extends this construction to every finite list of pairs. Full surjectivity is
now unconditional: Mathlib's finite-dimensional reflection-generation theorem
supplies Cartan--Dieudonné and determinant parity, yielding both
`Spin(4) → SO(4)` surjectivity and a lifting function. Smooth coherent
atlas-wide lifts and the ambient Pin/SpinC principal bundles remain open.
For any oriented atlas, pointwise lifts are now automatic; their global Čech
completion is equivalent exactly to trivializing one kernel-valued cocycle.
Global orientation, that class, and continuity/smoothness remain.

## 5. Program P

The exhaustive remaining-work checklist is
[`program_p_exhaustive_todo.md`](program_p_exhaustive_todo.md).

### P0, P-A, P-B and P-C

- **P0:** a metric does not select a potential; a symplectic form does not select a Hamiltonian.
- **P-A:** the two-sector parent-bulk result now extends to an arbitrary finite boundary rank: the bulk Euler expression is the actual derivative, the reduced action has the Schur gradient and constant Hessian as its Fréchet derivatives, and exact square completion classifies the fixed-boundary stationary bulk mode as the unique global minimum/maximum according to the sign of the bulk coefficient; the Schur kernel is reciprocal/self-adjoint, while changing the parent can still change surviving mixing. In the concrete one-dimensional positive PT-flat proportional bimetric branch, the reduced interaction has its actual derivative, `c = 1` is stationary, its actual Hessian is twelve times the Fierz--Pauli mass combination, and for `beta1 > 0`, `beta2 >= 0` it is positive and `c = 1` is the unique global minimizer on `c > 0`; this is not the full Janus metric field theory.
  The parametrized global-field package now uses those same effective D8
  spacetime/throat bases, involutive PT actions and equivariant throat map.
  A nonempty PT-fixed diagonal witness on them has equal Minkowski metrics,
  zero matter and identity relative root. Explicit continuity predicates now
  cover every independent, induced and LL coordinate, and this same witness
  inhabits a continuous PT-matched effective configuration with the exact
  throat inclusion and root-square equation. This is topological only: it
  supplies by itself no smooth manifold, Sobolev spaces, boundary conditions, global
  root map, stationarity or stability.
  Independently, the new analytic cover atlas carries a genuine space of
  smooth finite-dimensional coefficient fields invariant under every deck
  iterate. Their descent to the same effective quotient is continuous and
  injective, and a constant two-metric/two-scalar/identity-root coefficient
configuration inhabits it. The quotient itself now has the analytic manifold structure, and both the spacetime quotient and fixed throat are compact. Smooth quotient/throat coefficient fields form real vector spaces; smooth fields inject into the genuine completed `L²` space for finite Borel measures, with Hilbert structure under explicit fiber hypotheses and an isometric PT equivalence for PT-preserving measures. Smooth throat trace, PT-equivariance and a nonempty exact Dirichlet condition are proved. A finite global `C∞` tangent-generating family is now constructed from a finite trivialization cover and a subordinate partition of unity. It feeds the completed first-jet graph `H¹`, whose smooth fields are dense and whose forgetting map to `L²` is continuous. For spacetime measure pushed forward from a finite throat measure, the continuous trace has exact norm bound `1`. The canonical spacetime/throat volumes now instantiate this complete graph `H¹`; existence of the physical trace is equivalent exactly to one smooth codimension-one inequality. The exact FTC/Fubini estimate, twisted analytic latitude collar, throat-measure pushforward and `L²` trace identity are proved. The normal derivative is reconstructed exactly by the finite global frame. Joint `C∞` latitude regularity proves `CanonicalLatitudeNormalLiftContinuous`, and the radial--polar Euclidean calculation now proves the coarea inequality. The canonical physical trace bound, continuous operator, smooth agreement and existence theorem are therefore unconditional. Intrinsic Sobolev identification remains open. A populated independent-field package includes positive diagonal metrics, matter, gauge-coordinate, ghost, auxiliary and LL/throat coefficients; metric/root/trace fields are uniquely induced. One simultaneous independent-field curve now gives the exact componentwise derivatives of both induced metrics, the principal root and both matter traces, with zero induced cross-response from gauge, ghost, auxiliary and LL directions. The abelian `U(1)^2` sector is upgraded to intrinsic smooth one-forms with `A ↦ A+dλ`, exact diffeomorphism covariance, nilpotent BRST `s(A,c)=(dc,0)` and a bridge to the independent ghosts. General covariant tensors now have an exact involutive analytic-PT pullback preserving symmetry, nondegeneracy and Lorentz inertia. Tangent and nested Hom-bundle coordinates discharge `AnalyticPTTensorPullbackLocalSmoothness` unconditionally, yielding an involutive smooth pullback on the smooth Lorentz domain. The attached musical equivalence now pulls back with the same tensor, giving an involutive PT action and sector exchange on `SmoothGeneralLorentzMetric`; the holonomic scalar density is pointwise PT-covariant with coherently transported field and frame. Integrated spacetime PT invariance, BV ghosts and the curved Euler--flux PDE remain open. Global scalar `p = d phi` is the genuine manifold differential with exact throat/PT chain rules. Its fixed-frame diagonal global action now uses the inverse and volume of the same metric, and its fixed-metric/measure scalar variation is proved pointwise and after integration under an explicit contract. Arbitrary smooth inclusion-preserving diagonal diffeomorphisms now pull back all independent sectors with exact action laws, natural throat trace and a manifold tangent generator for smooth orbits. The LL measure/flux fields define an actual finite-measure worldvolume integral on the compact throat with a nonempty zero branch. The admissible null-variation domain is the open set `Theta ≠ 0`, deliberately excluding the proved singular point.
  The integrated-invariance limitation in the preceding snapshot is now
  superseded: for `SmoothGeneralLorentzMetric`, coherent PT transport of the
  scalar and tangent family gives exact density covariance, iff transport of
  integrability and invariance of the action against the canonical quotient
  Lorentz measure. The tangent family remains supplied, and this reference
  measure is not claimed to be every general metric's own volume. At fixed
  metric, the affine scalar line now has an exact pointwise/integrated
  quadratic expansion and action `HasDerivAt` under the explicit integrability
  contract for its three coefficients. Its first variation is PT-covariant
  pointwise and after integration, with exact iff integrability transport.
  The normal-lift continuity cited above is now unconditional: the elementary
latitude map is jointly `C∞`, the bundled lift is exactly the collar tangent
map on a smooth vertical section, and the compact frame reconstruction package
is constructed. The positive collar is now homeomorphic and measurably
equivalent to the exact band `x₀ ∈ Ioc(0,sin 1)` of `S³`, with explicit
  `arcsin`/normalized-tail inverse. The weighted sphere formula is reduced by
  `Measure.toSphere_apply'` to the ordinary four-dimensional cone identity
  `CanonicalPositiveLatitudeEuclideanConeJacobianFormula`. That identity is now
  proved directly: an exact orthonormal split, spherical radial disintegration,
  planar polar coordinates and `∫₀¹ r³ dr = 1/4` close the source measure and
  Jacobian. Coarea and the complete canonical physical trace follow with no
  residual certificate or analytic assumption.
  The homogeneous physical Dirichlet graph-`H¹` space is now the kernel of
  that trace. It is closed, complete and nonempty, with exact membership and
  smooth zero-`L²`-trace characterizations. A nested finite `ℓ²`/`WithLp 2`
  renorming now closes the smooth-jet image in a genuine Hilbert space and is
  continuously linearly equivalent to the original graph norm, with exact
  agreement on smooth fields. The transported physical trace has a closed
  Hilbert Dirichlet kernel, a contractive orthogonal projection and an exact
  orthogonal decomposition; that kernel is continuously linearly equivalent
  to the original graph-Dirichlet space. This does not identify an intrinsic
  Sobolev space.
  PT/exchange additionally acts on the complete current independent-field
  package and all its componentwise smooth throat boundary data, with exact
  trace equivariance and preservation of the full Dirichlet condition.
  More precisely, the nonlinear ghost frontier now includes the intrinsic
  smooth tangent Lie bracket, a genuine three-generator exterior coefficient
  algebra, vanishing of the total cubic pure-ghost obstruction and exact
  cancellation of the scalar BRST square. Extension to general spacetime
  fields and a functional/global BV complex remains open. The spatial `so(3)`
  rotations are now explicit on the cover, tangent to `S³`, deck-equivariant,
  closed under their nonabelian Lie
  table, and equipped with an injective smooth descent contract to quotient
  ghosts. The three tangent `C∞` cover sections are now explicit, faithful and
  nonzero. Bracket naturality under quotient projection is now proved through
  a local radial diffeomorphism, yielding an unconditional faithful, nonzero
  and nonabelian closed quotient `so(3)` ghost triple. Its coefficient CE
  differential is now explicit on the exterior algebra and satisfies the odd
  parity, Koszul Leibniz, square-zero, generator and nonlinear-ghost rules, so
  the closed three-generator data are unconditional. A sign-consistent total
  map `D⊗id + action` is now globally odd, Koszul-Leibniz and square-zero and
  gives an unconditional `Z2` differential. The legacy minus sign is retained
  with the exact obstruction that its scalar square equals twice the iterated
  ghost action. The corrected differential now extends componentwise to the
  current linear matter, gauge-coordinate, internal-ghost and auxiliary
  sectors, with square zero on each sector, their product and the projection
  from `IndependentFields`. The three spatial rotations now preserve the
  equatorial throat, commute with deck, descend smoothly and retain the exact
  `so(3)` bracket. Their scalar/Koszul action and the three LL block maps are
  explicit. The throat Koszul differential is odd, Leibniz and square-zero,
  so `LLThroatBRSTCompletion` is now unconditional. The eight positive
  diagonal throat-metric magnitudes now have logarithmic ghost action,
  globally positive exponential curves and an odd Leibniz square-zero BRST,
  combined unconditionally with LL. The finite field/antifield seed is now a
  genuine `32`-dimensional BV master model: its canonical odd Darboux
  antibracket is explicit, the nonzero action `S(q,p)=p(dq)` is even, satisfies
  `(S,S)=0`, generates the square-zero odd BRST vector field and embeds exactly
  into the throat doublet. Fibrewise promotion to smooth fields on the actual
  throat gives a smooth square-zero BRST and master density, pointwise CME and
  Hamiltonian generation, plus a canonical integrated action with an explicit
  nonzero constant witness. Its exact affine first variation, gradient/BRST
  identity, odd antibracket on represented analytic ultralocal functionals and
  integrated CME are also proved. The canonical throat volume is now proved
  PT-invariant directly from its round-`S²` times fundamental-interval
  pushforward; consequently the integrated master action, first variation,
  represented functional value, odd antibracket and CME are PT-covariant
  without a measure hypothesis. This closure is only for the represented
  ultralocal BV sector on the actual throat. The same constant finite
  `32`-dimensional phase fibre is now also promoted to `C∞` fields on the true
  spacetime D8 quotient: its BRST is smooth and square-zero, restriction
  recovers the throat construction, and the canonical spacetime volume gives
  a finite nonzero master action with pointwise and integrated CME. The round
  `S³` reflection and signed-period reversal are now proved to preserve that
  canonical quotient volume; PT is therefore an involution commuting with
  BRST, and the integrated master action and CME are unconditionally
  PT-covariant. The exact affine first variation, integrated directional
  derivative and odd antibracket/CME on represented analytic ultralocal
  spacetime functionals are now proved as well. Their exact fibre PT laws and
  integrated first-variation, represented-value, odd-antibracket and CME
  covariance are unconditional. This only removes the base-space restriction;
  it is not a BV theory of general tensor metrics and
  supplies no bracket on arbitrary nonlocal/completed functionals. Independently, real translation of the
  mapping-torus coordinate now descends to a nontrivial complete analytic real action on the
  actual D8 quotient; every time slice is an analytic diffeomorphism and the
  full action map `ℝ × D8 → D8` is jointly analytic. Pullback
  restricts analytically to the throat and gives an exact complete pullback
  action on all eight blocks of the current `IndependentFields` package, with
  zero/addition/inverse laws, PT conjugation and compatibility with all five
  induced fields. An explicit descended periodic cosine field is sent to a
  distinct field by the half-period pullback. Embedding it in the first matter
  component produces a complete `IndependentFields` configuration moved by
  the same half-period, so the actual full-package representation is genuinely
  nontrivial. Integration of an arbitrary ghost remains open. An intrinsic positive fixed-patch energy replacement is
  also uniformly equivalent to the implemented localized graph density and
  gives unconditional uniform graph ellipticity; equality with the historical
  variable-`chartAt` density remains open.
  The canonical intrinsic tensor descended from the immersed cover is now
  certified everywhere Lorentzian without an external frame contract: the
  proof constructs the sphere-tangent/orthogonal equivalence, an orthonormal
  spatial frame and transports the exact `(3,1)` model through the quotient
  projection derivative. This tensor now instantiates an actual global
  `SmoothGeneralLorentzMetric`, with global nondegeneracy and exact pointwise
  scalar density, first variation and quadratic remainder. The false
  global-frame requirement is now removed by separating the frame-free scalar
  Lagrangian from its integration measure: every finite nonzero Borel measure
  gives an integrable action, and a constant massive field proves it is
  genuinely nonzero. The canonical Lorentz volume contract is now discharged
  without Dirac masses: `Measure.toSphere` on `S³` times Lebesgue measure on a
  fundamental time interval pushes forward to a finite nonzero quotient
  measure. A finite compatible Lorentz-density atlas glues uniquely to exactly
  that measure and instantiates a nonzero intrinsic action.
  On the positive-diagonalizable root locus, all four root characteristic
  coefficients are now unconditionally continuous. The key
  `c₃ = -tr(√A)` result avoids a varying eigenbasis by normalizing the positive
  spectrum into `[0,1]⁴`, descending the symmetric square-root sum through a
  compact quotient, and denormalizing. The rational reconstruction formula
  then proves global continuity of the matrix selector, local IFT stability
  and the exact inverse-Sylvester derivative on the whole positive-
  diagonalizable locus. The similarity-invariant index-two unipotent locus
  `(A-I)²=0` now has its canonical polynomial root, exact square, continuous
  stratum restriction and bijective Sylvester operator; it glues to the
  positive selector on the exact intersection `{I}`. This is now extended to
  the full locus `(A-I)³=0` by `I+N/2-N²/8`, with a strict index-three witness,
  similarity, a polynomial bilateral Sylvester inverse, continuous stratum
  restrictions and exact extension of the previous gluing. The final possible
  unipotent index in dimension four is now also closed by
  `I+N/2-N²/8+N³/16`, including a strict size-four witness and a polynomial
  bilateral Sylvester inverse. Thus every unipotent `4×4` Jordan stratum is
  covered. Rescaling now covers every single positive eigenvalue `λ>0` with
  `(A-λI)⁴=0`, including joint continuity, similarity, a bijective explicit
  Sylvester inverse and exact agreement with the unipotent selector at `λ=1`.
  The positive two-eigenvalue `2+2` primary stratum is also closed blockwise,
  with exact square, rebase by similarity, continuity and a finite-series
  Sylvester inverse. The positive `3+1` and `2+1+1` strata now have the same
  guarantees. Thus every real strictly-positive Jordan partition of four is
  covered when an explicit presentation is supplied. A single inductive
  presentation type now unifies all five partitions, with a selector, exact
  square, bijective Sylvester, per-stratum continuity and combinatorial
  exhaustivity. Raw-matrix Jordan presentation bridges and the final physical
  admissibility selection across all strata remain. The raw positive theorem is
  now reduced exactly: split positive charpoly implies the corresponding
  minpoly facts and Mathlib supplies Jordan--Chevalley, but no Jordan-basis or
  rational-canonical-form constructor. One named external bridge,
  `PositiveRealJordanBasisBridge4`, captures the remaining general input. On
  the Hermitian sector it is now discharged constructively: Mathlib's spectral
  theorem supplies `eigenvectorUnitary`, whose positive eigenvalues give the
  exact diagonal member of `PositiveRealJordanPresentation4`; this includes
  every `PosDef` matrix and yields the already closed square-root and Sylvester
  conclusions. On the non-Hermitian complement, the sole presentation-level
  input is now the strictly lower-level
  `PositiveRealNonHermitianJordanChainBasisResidual4`: choose one invertible
  real matrix of chain vectors, its intertwining equation and one of the five
  partitions of `Fin 4`. The matrix inverse, unified presentation, exact root
  and Sylvester bijectivity are all derived downstream. Constructing that chain
  basis remains the only positive raw presentation residue.
  At root-existence level the whole positive-semidefinite raw locus is now
  unconditional through Mathlib `CFC.sqrt`. A genuinely non-PSD locus is now
  closed as well: every raw relation `(A-λI)(A-μI)=0`, `λ,μ>0`, has the exact
  affine root `(A+√λ√μ I)/(√λ+√μ)`, including the repeated size-two Jordan
  case `λ=μ`. The explicit `canonicalJordan211Target λ λ λ` witness is proved
  non-Hermitian and non-PSD. This is now extended to every positive
  single-eigenvalue relation `(A-λI)^4=0`: the third-order Taylor polynomial of
  `sqrt` gives an exact raw root. The strict size-four Jordan block is proved
  non-Hermitian, non-PSD and outside every quadratic annihilator. A genuinely
  multivalue raw locus is now closed too: for distinct positive `λ,μ`, every
  relation `(A-λI)²(A-μI)²=0` has an explicit cubic Hermite root matching
  both values and derivatives of `sqrt`. Its residual polynomial is proved
  divisible by both squared factors, hence by `minpoly A`. The canonical
  Jordan `2+2` witness is non-Hermitian, non-PSD and outside both the quadratic
  and single-eigenvalue quartic loci. The distinct positive `3+1` relation
  `(A-λI)³(A-μI)=0` is now closed as well: its cubic matches the value, first
  derivative and second derivative of `sqrt` at `λ`, and the value at `μ`.
  Three vanishing residual jets give the cubic factor, coprimality gives the
  remaining linear factor, and minpoly evaluation proves the exact square.
  The canonical Jordan `3+1` witness is non-Hermitian, non-PSD and outside the
  quadratic, single-eigenvalue quartic and double-double loci. The remaining
  multiplicity profiles are constructive too: Hermite interpolation closes
  `2+1+1`, and four-node Lagrange interpolation closes `1+1+1+1`, always
  with `natDegree q ≤ 3`, minpoly divisibility and `q(A)²=A`. Splitting plus
  the degree-four charpoly extracts four positive roots with multiplicity;
  Cayley--Hamilton and an exhaustive equality partition select one of the five
  closed annihilators. Hence raw real-root existence is unconditional for
  `PositiveRealSplitCharpoly4`. Sylvester regularity is now unconditional too:
  the four polynomial profiles use the basis-free fact that `R=p(A)`,
  `R²=A` and `RX+XR=0` force `X` to commute with both `A` and `R`; positivity
  makes `R` invertible, so the Sylvester kernel is zero and finite dimension
  gives bijectivity. The single-eigenvalue quartic profile reuses its explicit
  finite Sylvester inverse. A real Jordan-chain presentation remains separate
  only when an explicit Jordan form is itself required.
  Outside the positive locus, determinant negativity and every simple
  negative diagonal eigenvalue are now exact no-go criteria; determinant
  positivity is proved insufficient by an explicit `4×4` witness. Paired
  negative diagonal and identical Jordan `2×2` blocks have explicit real
  roots. The full negative-block parity/zero-block criterion is formalized,
  with its raw-matrix equivalence reduced to one Jordan-classification bridge
  absent from Mathlib. Its sufficiency is nevertheless unconditional on the
  union of the PSD and raw irreducible-quadratic loci; the remaining exact
  residual separates criterion necessity from sufficiency off that union.
  Pure conjugate-complex spectra now have an exact real `2×2` principal root
  off the branch cut, an explicit cut closure, continuity, the precise zero
  singularity, direct `2+2` sums and a non-semisimple complex Jordan-chain
  root, all stable under similarity. The raw charpoly-to-presentation step is
  reduced to `PureNonrealJordanPresentationBridge4`. Independently of that
  presentation, every raw relation `(A-aI)²=-b²I`, `b≠0`, now has an explicit
  affine polynomial root, including the repeated complex `2+2` block.
  For every finite measure, the scalar integrability contract is now automatic
  on the affine-stable class with continuous fixed-frame covector components,
  including arbitrary nonzero constant scalars; general tensorial continuity
  remains open.
  The same independent variation now projects type-safely to the D9 slots it
  really supplies, and its diagonal metric image is proved non-surjective onto
  general symmetric D9 perturbations. Literal finite D10 product modes use the
  same period, exact PT pairing and the existing heat regulator. A genuine
  smooth section of the D8 normal line now fills the D9 normal slot in every
  valid local bundle chart; one-loop transition is `-1` and equals the square
  of either `Z4` multiplier. No canonical global scalar normal coordinate is
  claimed. Diffeomorphism ghosts, SpinC identification, general metrics and
  action/Hessian/domain agreement remain an explicit contract.
  The global LL action now has an exact simultaneous measure/flux cubic
  expansion and integrated derivative for every finite measure. Its algebraic
  Euler system is equivalent to the zero-flux branch. PT pullback is an exact
  involution and preserves its density, action, variation, Euler coefficients
  and stationarity for PT-invariant measures. The auxiliary LL metric
  has identically zero response in this selected action, so a genuine
  differential LL PDE still requires a richer action.
  More strongly, explicit quadratic and quartically deformed two-variable
  extensions have the same proportional branch, the same genuine longitudinal
  derivatives and the same complete transverse two-jet, with Hessian
  `2 kappa`, all along that branch. A nonzero `lambda * y^4` term still makes
  them distinct off the branch, so even the local transverse Hessian does not
  select the nonlinear extension. This is a reduced reconstruction no-go, not
  a full metric action.
  The two-scale PT-flat lift now has an exact directional first variation for
  arbitrary independent variations, including explicit bulk, interaction and
  reduced boundary channels. Both Euler components characterize stationarity,
  while unfixed boundary coefficients can stationarize any scale pair. A
  separate quadratic candidate has genuine Frechet gradient and Hessian,
  diagonal interaction kernel, positive relative quotient under positive-sign
  assumptions, and a strict negative pure-kinetic Hessian direction for the
  published reduced sign `kappa = -1`. These remain reduced conditional/no-go
  statements, not the missing covariant Janus action or ghost analysis.
  A general normed trace/lift interface now gives the genuine Frechet and
  directional variation of independent two-sector bulk-plus-boundary actions.
  Stationarity is exactly interior bulk vanishing plus lifted boundary balance;
  an accessible nonzero boundary flux obstructs it. The interface does not
  construct the physical GHY/null/corner/junction data.
  A supplied differentiable Helmholtz boundary flux now admits a normalized
  counterterm with genuine derivative `-flux`; it cancels the exact boundary
  one-form, is unique up to a constant, and a non-Helmholtz flux blocks any
  global `C^2` primitive of this type. This does not derive a physical GHY
  flux. For induced fields, the actual chain rule gives
  `E_bulk + E_induced ∘ D(induced)`; an exact diagonal counterexample proves
  that imposing both slot equations separately can overconstrain the system.
- **P-B:** four explicit finite candidates realize every anomaly/Helmholtz truth pattern, so anomaly cancellation is an independent consistency filter rather than a dynamics principle.
- **P-C:** finite quadratic and polynomial Helmholtz reconstruction is formalized, including the exact three-sector PT-plus-reciprocity criterion. For the finite quadratic Euler family, self-adjointness of the actual Jacobian is equivalent to the coefficient Helmholtz swaps; these data construct a normalized cubic polynomial primitive with the prescribed actual Fréchet derivative, and derivative equality alone recovers its formal coefficients. A Poincaré--Helmholtz theorem reconstructs an action from a symmetric differentiable Euler one-form on an open convex configuration domain; on the whole space, under a global actual-gradient hypothesis, additive linear gauge invariance is equivalent to Euler horizontality. More generally, for a supplied complete differentiable one-parameter flow, full-orbit invariance is equivalent to annihilation of its field-dependent generator by the actual Euler derivative; horizontal Helmholtz data give an invariant normalized radial primitive. The quotient geometry now supplies one concrete nontrivial complete analytic time flow, but not the arbitrary-ghost/full-field gauge group or PDE identity; the nonlinear Janus Euler family, Noether system and variational cohomology remain open.
  The set quotient by complete-flow orbits is constructed. For any target,
  functions on this quotient are equivalent to configuration-space functions
  invariant under the flow; the real-valued specialization gives the same
  equivalence for actions, including the radial action. The concrete D8 time
  pullback now separately instantiates this construction on the complete
  current `IndependentFields` package, with an exact orbit setoid and the same
  invariant-function equivalence. No topology or smooth structure is put on
  either orbit quotient.
  In a supplied reduced two-metric chart, the relative quadratic action now has
  its actual Frechet derivative: independent variations recover both Euler
  components, diagonal/sign-linked variations recover their sum/difference,
  and finite diagonal translation symmetry yields the reduced Noether identity.
  This is not yet the covariant diffeomorphism/Bianchi system.
  In a supplied metric--metric--matter chart, existence of one common `C^2`
  action is now equivalent to reciprocity of all three cross-block pairs; a
  genuine bilinear primitive proves sufficiency, and an explicit mismatch gives
  a conditional no-go. Since M30 does not specify its interaction densities or
  matter dependence, no mismatch is attributed to it. With a supplied boundary
  Euler term, diagonal symmetry yields only
  `E_plus + E_minus + boundary_flux = 0`; separate conservation additionally
  requires zero exchange and zero boundary flux.
  On the full plus--minus--matter product, three diagonal and three cross-block
  conditions are exactly equivalent to symmetry of the nonlinear actual Euler
  derivative. On an open convex domain they reconstruct a normalized common
  action, while one supplied failed cross block gives a global `C^2` no-go.
  For a supplied field-dependent diagonal generator `K(q)`, infinitesimal
  invariance is exactly the formal constraint `E(q) ∘ K(q) = 0`; a cancelling
  two-sector example shows that this combined identity still need not split.
  Those earlier generic results construct neither an M30 density nor a Janus
  diffeomorphism generator or covariant Bianchi/constraint algebra.

#### Candidate A active-branch checkpoint

- **T/C** the two symbolic M30 cross-density slots are instantiated as
  reciprocal halves of one elementary-symmetric interaction; matter dependence
  is explicitly absent and weighted double counting is excluded;
- **T/C** the full four-eigenvalue interaction has an actual Frechet gradient,
  second derivative and symmetric Helmholtz Jacobian;
- **T/C** a pointwise `4 x 4` square-root matrix realizes the same Newton
  invariants, specializes to the spectral formula and is similarity invariant;
- **T** around the independent diagonal Minkowski metric pair, the concrete
  identity-root IFT branch is composed with the actual map
  `(g_plus,g_minus) -> g_plus^-1 g_minus`. Its full pair derivative is proved,
  including metric inversion, and its square equals that relative metric
  on an explicit open domain obtained from the IFT chart target. The selected
  root is continuous throughout that domain and unique among roots remaining
  in the chart source. On the explicit open nonempty overlap with the global
  positive diagonal domain, it is now proved equal to the global principal
  root. This does not extend the branch beyond the diagonal sector;
- **T** at the Minkowski diagonal, one genuine two-metric affine curve now
  differentiates the complete Candidate-A interaction density: the plus
  determinant measure, the unconditional relative-root branch and the full
  matrix spectral potential are composed by the Frechet product/chain rules,
  with the resulting covector expanded explicitly. This remains pointwise and
  local; it is not the global two-sector functional variation;
- **T** throughout the entire explicit Minkowski IFT target domain, the
  inverse-chart estimate gives a uniform local Sylvester perturbation bound;
  a Neumann correction proves its invertibility at every selected root. The
  root, determinant measure, full spectral potential and Candidate-A density
  therefore have actual Frechet derivatives at every domain point. On the
  open intersection stable under metric-pair exchange, both sector densities
  are differentiable and their sum is exactly exchange invariant. This is the
  complete local-chart two-sector variation. It is now integrated over an
  arbitrary measured base under an explicit uniform-domain and dominated
  differentiation contract, with exact exchange invariance and full PT
  invariance for a measure-preserving base involution. The same construction
  is instantiated on the effective D8 quotient for any supplied PT-invariant
  Borel measure. The domination and invariant measure are hypotheses, and this
  IFT chart remains local;
- **T/C** a separate global fixed-frame diagonal Lorentz domain is open,
  connected and causally compatible through one common strict timelike
  direction; its nonnegative closure and spectral frontier are exact. The
  positive root and full Candidate-A chain are smooth there. On its one-sided
  diagonal faces, numerator zero sends the root to zero and degenerates
  Sylvester, denominator zero sends it to infinity, and the positive branch
  cannot switch inside the component; `0/0` and general matrices remain open. On the same
  smooth D8 metric fields, positive exponential curves give the exact
  pointwise density derivative at every parameter and the integrated
  functional derivative under an explicit domination contract. General
  non-co-diagonal Lorentz fields remain open;
- **T/C** one symmetric nondegenerate `4 x 4` metric now supplies both the
  exact inverse and `sqrt(|det g|)` in a scalar-density curve on an open
  fixed-sign component; its actual pointwise variation is the pairing with an
  explicit symmetric stress tensor, and an explicit dominated-differentiation
  contract lifts this stress variation to one or two integrated sectors. A
  separate continuous flat-chart gate makes the scalar covector the actual
  Frechet derivative of the same differentiable field and proves the
  pointwise and integrated holonomic scalar variation. A further flat-chart
  gate varies metric and holonomic field simultaneously pointwise, using the
  same objects for measure, inverse, value and `p = d phi`, and proves the
  exact stress/field split. That simultaneous variation now has a genuine
  integrated derivative under an explicit dominated local-Lipschitz contract.
  At fixed metric the holonomic density variation decomposes pointwise into
  the flat scalar Euler operator plus an explicit flux divergence. Under
  integrability and the named zero-integrated-flux condition, the first
  variation and any already-justified action derivative equal the weak Euler
  pairing. Automatic domination, derivation of flux cancellation from boundary
  conditions, curved covariance, covariant matter PDE and conservation remain
  open;
- **T/C** on the compact smooth D8 quotient, the fixed-frame scalar action
  ties value, genuine manifold differential, inverse metric and metric volume
  to the same scalar/metric fields. Its affine scalar curve has an exact
  pointwise and integrated first variation at fixed metric and measure under
  an explicit integrability contract. A covariant Euler--flux identity is not
  claimed;
- **T/C** the finite Gram tensor has actual first/second derivatives, is
  positive definite on the injective immersion domain, and gives a concrete
  compatibility map `K` and Jacobian `J`;
- **T/C** the Saint--Venant symbol complex now reconstructs compatible
  coefficients on the countable `Z^4` Fourier lattice, isolates the zero mode
  and is realized on completed weighted `ell^2` Hilbert spaces: the
  reconstruction is bounded, the order-one Lorentz--Gram symbol has its
  explicit maximal domain, its compatible zero-free range is closed, and the
  zero-mode obstruction stays at the same weighted scale. A second completed
  coefficient model adds the exact graph-Sobolev weight of one symbol order:
  the normalized Lorentz--Gram map is a Hilbert-space contraction and equals
  the physical symbol exactly after source/target weighted encoding. The
  canonical target identity Hessian is continuous, self-adjoint and positive;
  its actual pullback `J†J` is symmetric and nonnegative, has precisely the
  zero Fourier mode as kernel, and is positive definite after removing it. A
  bounded idempotent zero-mode projection now splits the Hilbert space, and
  the actual normed quotient by `ker J` is continuously linearly equivalent
  to its closed zero-free representatives, where this Hessian is
  nondegenerate.
  Identification with global Sobolev bundle sections, Fourier-series
  differentiation, global PDE and boundary exactness remain open;
- **T/C/N** typed non-null, null and joint gravitational slots are explicit;
  the compact-throat LL action and zero branch are actual integrals, while LL
  PDEs, full stratification and physical bulk-flux cancellation remain open;
- **T/N** additive translation of reduced scale variables is classified and
  fails for a concrete positive interaction; any relation to the covariant
  diagonal diffeomorphism still requires a separate bridge;
- **O** general tensorial Lorentz square-root domain, metric Euler equations, physical
  GHY/null/joint variation, Bianchi/constraint algebra, exact stability,
  anomalies, normalization and finite counterterms.

Canonical candidate document: `docs/program_p_explicit_covariant_candidate.md`.

### P-D — pairings and coefficient modules

Formalized/audited:

- `Z4` and PT selection rules;
- low-rank scalar, vector, tensor and spinor pairing dimensions;
- multiplicity-space freedom for repeated sectors;
- closure under invariant scalar coefficients;
- failure of pointwise multiplicity one to imply one constant global coupling;
- jumps of invariant-fiber dimensions across isotropy strata.

The correct global object is an equivariant pairing module over the invariant scalar algebra, not only a pointwise Hom-space.

### P-E — structured jets

#### 5.1 Categorical and groupoid core

The current `main` stack proves, in the declared models:

- local finite-jet factorization under the stated Peetre--Slovak hypotheses;
- naturality/equivariance and evaluator uniqueness;
- holonomic composition;
- action-groupoid, orbit and stabilizer laws;
- reconstruction of equivariant sections on one transitive orbit from isotropy-fixed values;
- a concrete valid-chart low-order residual/SpinC action-groupoid realization;
- the need for separate compatibility across isotropy strata.

The operator category is not an ordinary category of fixed linear representations with plain fiber maps.

#### 5.2 Low-order quotient

For an adapted immersion two-jet, the chain rule gives

```text
Q_tangent -> Q_tangent + C
Q_normal  -> Q_normal.
```

The source orbit is classified by the normal tensor. Abelian connection one-jet gauge orbits are classified by curvature. The combined quotient is `(B,F)` and has the universal invariant-factorization property.

#### 5.3 Adapted geometry and `B = II`

Lean constructs:

- tangent image and orthogonal normal complement;
- coordinates with `di(x)=(x,0)`;
- smooth tangent/normal projectors;
- smooth local adapted orthonormal frames by projected Gram--Schmidt;
- the connection-corrected second derivative;
- the flat-adapted identity `B=II`;
- residual `O(T) x O(N)` equivariance;
- moving-frame corrections, normal transport and overlap Čech laws;
- determinant-one reduction to `SO(T) x SO(N)`;
- canonical pointwise normal-frame transitions;
- smooth adjoint-formula transitions on overlaps;
- transition jets and their direct derivative construction.
- a projected-seed varying-normal atlas with smooth transition and coefficient laws;
- constructive smooth Euclidean metric-Koszul connection existence.

These constructions package a genuine projected-seed normal atlas, but not yet
the complete global Janus frame/normal bundle over the full background space.

#### 5.4 SpinC and rank-two Clifford model

Lean proves:

- central `±1` lift defects;
- two-torsion determinant-root defects;
- diagonal SpinC cancellation when the defects match;
- the circle-squaring cover and kernel `{±1}`;
- `U(1) ≃ SO(2)`;
- equivalence with Mathlib's even-unitary Lipschitz `CliffordAlgebra.spinGroup` for the negative Euclidean plane;
- the Clifford-valued rank-two central double cover and SpinC diagonal quotient;
- the canonical one-chart Cech principal bundle and a connection from the
  supplied global smooth gauge potential;
- conditional multi-chart SpinC Cech transition packaging from supplied
  pointwise cocycles, lifts, phases and matching defects, without transition
  continuity/smoothness or a principal-bundle total-space construction;
- conditional abelian connection overlap descent from supplied local
  potentials and additive gauge shifts, with unique global smooth curvature
  descent under the flat-shift condition and a cyclic Bianchi identity for its
  actual Fréchet derivative.

Higher-dimensional Clifford covers, derivation of the supplied cocycles from
actual Janus bundles, nontrivial/global Janus principal-bundle construction,
determinant-line identification and characteristic-class matching remain open.

#### 5.5 Codazzi and abelian Bianchi exactness

The current `main` stack proves:

- Gauss curvature symmetries from symmetric `II`;
- Codazzi and abelian Bianchi skew/cyclic identities;
- exact classification of Codazzi fibers by fully symmetric third-order corrections;
- exact classification of connection second-jet fibers by symmetric gauge third jets;
- canonical `1/3` sections and universal quotient properties;
- exact splittings

```text
j1(II)  ≃  Sym3(T*) tensor N  x  ClosedCodazzi,
j2(A)   ≃  GaugeJet3_sym       x  Closed(nabla F).
```

The Codazzi tensor is only the quotient component of `nabla II`; the fully symmetric third-order component remains independent data.

#### 5.6 Normal Ricci equation and Riesz shape operators

The algebraic Ricci stage starts from

```text
<A_xi x,y> = <II(x,y),xi>.
```

Lean proves self-adjointness of `A_xi` and the tangent/normal antisymmetries of

```text
<[A_xi,A_eta]x,y>.
```

The current `main` stack goes further: for a symmetric bilinear finite-dimensional `II`, it constructs `A_xi` by Fréchet--Riesz representation. Finite-dimensional bilinear continuity is supplied automatically by Mathlib. The Weingarten relation, self-adjointness, commutator symmetries and the algebraic Ricci reconstruction therefore follow from `II`, rather than from independently assumed shape operators.

Still open:

- identify the proved projected-seed/fixed-model family with the actual global
  Janus `II` bundle over the full structured-jet base;
- insert the genuine ambient mixed curvature and normal-connection curvature;
- prove the manifold-level Ricci equation.

### P-F — compatibility pullback

A self-adjoint target Hessian pulls back to a self-adjoint quadratic Helmholtz
operator; gauge invariance gives the linearized Noether identity. The abstract
compatibility-complex synthesis now packages `K R = 0`, `B K = 0`, pulled-back
self-adjointness, gauge-Hessian degeneracy and restricted Helmholtz in one
theorem. It assumes the algebraic complex and pairing; the actual nonlinear
second-variation chain rule is also proved in normed spaces as
`H(Ju)(Jv) + dL(D²K(u,v))`, reducing to `H(Ju)(Jv)` when the target gradient
`dL` vanishes. Schwarz symmetry makes this complete second variation symmetric
even off criticality and therefore makes the critical `J^T H J` symmetric
without a separate symmetry postulate for `H`. At a target critical point the
pullback is genuinely critical, and its actual Hessian annihilates `ker J` in
either slot; hence it annihilates `im R` when `J ∘ R = 0`. These are abstract
Fréchet statements. For every source submodule contained in `ker J`, this
critical Hessian descends uniquely and symmetrically to the algebraic module
quotient. Continuity of the descended form and any normed, topological or
smooth quotient structure are not proved. No concrete Janus compatibility map
or complex is constructed; the global variational primitive remains open.

## 6. Current supported chain

```text
actual decorated Janus data
  -> regular local finite-jet presentation
  -> structured action groupoid and holonomic operator category
  -> low-order quotient (II,F)
  -> smooth local adapted frames and oriented overlap cocycle
  -> canonical normal-frame transition jets and gauge extraction
  -> Spin/determinant defects and rank-two Clifford SpinC model
  -> first Gauss--Codazzi--Bianchi quotient stages
  -> split data: Sym3 + Codazzi and gauge3 + nabla F
  -> Riesz shape operators from II
  -> algebraic normal Ricci equation
  -> actual ambient/normal/determinant connection jets
  -> higher structured jet-isomorphism theorem
  -> stratified invariant coefficient and pairing modules
  -> compatible Euler family
  -> Helmholtz + Noether + anomaly consistency
  -> action class, microscopic normalization and effective potential
  -> stable vacuum and absolute scale
```

The repository does **not** yet contain the full differentiable Janus structured-jet groupoid, a global Janus SpinC principal bundle, the geometric higher-order jet-isomorphism theorem, the concrete nonlinear Janus Euler family, a selected microscopic action, a unique vacuum or an absolute no-fit scale.
