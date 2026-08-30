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

The currently checked-out branch is `dev-branch`, at

```text
9a8b540d01d339c756d69202033a22ed49a38334.
```

The local worktree contains the later Program-P gates described below. On
28 July 2026, the complete Program-P façade compiled `10039/10039` jobs and
`scripts/audit_janus_program_p.py` passed with terminal count `0/14`.

On 26 August 2026, `T01` became the first closed terminal gate. The shared
global tangent/pairing realization, intrinsic L2 completion and
`program_p_t01_global_foundations_pairings_terminal_gate` compile directly and
as `.olean`; the integrity audit is green at `1/14`, with no business axiom.
The full Program-P façade and its complete local import closure are green.
One hundred twenty-four nonterminal `T02` support gates are now compiled and integrated.  In
addition to the stratified carrier, generic `C²` constructor, actual SpinC/LL
throat packet and low-order `(II, F)` orbit, they extract both actual metric
jets, the realized bulk Christoffel/`U(1)²` background core and all typed
nonminimal carrier slots (nine jets after sector expansion).  The two actual
sectorized `U(1)²` potentials are also pulled back through the fixed-throat
inclusion, expanded in a centered tangent trivialization and transported to
the exact `EuclideanR3` gauge-connection jet type.  Their finite coefficient
expansion now reconstructs the intrinsic covector exactly on the centered
trivialization base set and, for Candidate-A, is exactly the centered-frame
coordinate expression of the ambient bulk pullback: bulk potential composed
with the fixed-throat differential and the inverse tangent trivialization.  At
common points, two centered tangent frames obey
the exact contragredient transition law.  This is only a zero-order fiber/frame
overlap.  The tangent transitions are identity at a repeated anchor, invert
under anchor exchange and satisfy the exact triple-overlap cocycle; their
covector transports satisfy the corresponding dual cocycle.  The transition
and its inverse vary `C∞` on each overlap as continuous linear maps.  The local
coefficients and reconstructed covectors are `C∞` on the full centered
`baseSet`, and the induced dual action is `C∞` on the double overlap.  After
transporting the first representative, equality on the overlap now yields
the same `HasMFDerivWithinAt` certificate for every candidate first derivative
there.  In the extended throat chart centered at an overlap point, the exact
first-order Leibniz law is now proved:
`dC₂ = D₁₂ ∘ dC₁ + (dD₁₂) · C₁`.  This formula is deliberately
chartwise and does not assert intrinsic jet descent.  A two-parameter jet
carrier now separates the tangent-frame anchor from the base-chart center,
agrees exactly with the original Candidate-A extractor on the diagonal, and
packages this law in its actual `firstDerivative` slot.  A separate generic
continuous-linear-map Leibniz gate now differentiates such an application
twice.  Consequently the actual `secondDerivative` slot obeys the full
four-term fixed-chart law: transported `D²C₁`, two mixed `dD₁₂·dC₁`
terms and `D²D₁₂·C₁`.  This law is also transported to the exact
`EuclideanR3` gauge carrier.  With the tangent frame fixed, a genuine `C²`
transition between two extended base charts now identifies the representatives
as germs; a three-parameter jet then satisfies the exact first- and second-order
chain rules, including the Hessian of the chart transition.
The base-chart transition itself now forms a genuine second-order jet cocycle
on triple overlaps.  A centered-source synthesis combines the frame and chart
changes through order two, and the three-parameter chart law is also available
in the exact `EuclideanR3` physical gauge carrier.  The frame law now holds in
an arbitrary source chart and composes with a second chart to give exact
order-zero, first- and second-order laws between arbitrary frame--chart pairs.
Unit and inverse identities complete the base-chart transition groupoid through
order two.  The full semidirect frame--chart transition now satisfies its exact
triple cocycle: combined germ and value, Jacobian law and five-term fiber
Hessian law.  Its identity and inverse laws also hold through order two.  An
arbitrary valid frame--chart pair with a raw second jet now forms a local
presentation.  The exact value/Jacobian/Hessian compatibility laws generate an
explicit setoid, and all actual extracted gauge jets are directly compatible.
Their generated pointwise quotient therefore has a canonical class independent
of the valid local presentation.  Direct compatibility is now proved reflexive,
symmetric and transitive through order two; induction on `Relation.EqvGen`
shows that the generated and direct setoids coincide, so no extra zigzag
identifications remain.  The raw framed carrier is now a finite-dimensional
normed space; the exact semidirect transport is continuous linear, satisfies
the groupoid laws and varies `C∞` on the open frame--chart atlas.  These data
form a Mathlib `VectorBundleCore` with `IsContMDiff`, hence a genuine smooth
vector bundle.  The pointwise quotient is identified with its fibers, the
actual extracted `U(1)²` gauge jets agree with every local trivialization, and
their descended section is globally `C∞`.
Eight additional gates provide a chart-indexed constant-fiber second-jet
`VectorBundleCore`, generic local-to-global smooth-section criteria and exact
overlap for every finite-dimensional `SmoothThroatField`.  Thus the LL
auxiliary metric, measure and field now define three separate global `C∞`
second-jet bundle sections, with gauge-fixed wrappers and exact zero-jet
values. Seventeen further gates complete covariant rank-two throat metric jets:
arbitrary frame/chart extraction, exact first/second-order overlaps and
cocycles, semidirect groupoid transport, a smooth `VectorBundleCore`, and a
global `C∞` section for every smooth symmetric tensor and both induced metric
sectors. Eighteen further gates (92 + 18 total) complete SpinC second jets:
arbitrary trivialization/chart extraction, exact zero-/first-/second-order
overlaps and cocycles, semidirect groupoid transport, a smooth
`VectorBundleCore`, and global `C∞` sections for every smooth SpinC section and
the physical sectors. Seven further gates provide the generic common product
atlas/core, smooth product cores and smooth product-section assembly, then
instantiate them for the four gauge jets, three heterogeneous LL jets, two
metric jets and two SpinC jets. The resulting common physical second-jet core
and Candidate-A section are globally `C∞`. The normal/background bridge remains
a separate stronger target. The bounded linear local
functionals fixed by every genuine transition of this common physical bundle
now form a finite-dimensional subspace and admit unique finite coefficients.
The homogeneous quadratic class represented by continuous symmetric invariant
bilinear forms now has the same finite-coordinate classification; polarization
proves that diagonal evaluation is injective. Constants, linear terms and these
quadratic terms now assemble into a complete degree-at-most-two class whose
evaluation and scalar coefficient decomposition are both injective. Higher-degree
homogeneous cubics represented by continuous symmetric invariant trilinear
forms now also have a finite basis, unique coefficients and injective diagonal
evaluation by polarization. The complete degree-at-most-three class is now
assembled with injective evaluation and unique scalar reconstruction; parity
and dilation at `x`, `-x`, `2x`, `-2x` separate its linear and cubic parts.
Homogeneous quartics represented by continuous symmetric invariant
quadrilinear forms now also have a finite basis, unique coefficients and
injective diagonal evaluation through three small polarization steps. The
complete degree-at-most-four class is assembled with injective evaluation and
unique scalar reconstruction. On 29 August 2026 the global terminal `T02`
certificate fixed this degree-at-most-four class as the explicitly bounded
admissible class and assembled bundle smoothness, transition invariance,
evaluation injectivity, reconstruction and unique coefficients. The integrity
audit is therefore green at `2/14`. Degree five and general smooth invariant
functionals remain stronger targets outside the bounded `T02` contract.
Given a
compatible `GlobalCandidateAActionData` witness and a supplied chart, a separate
external-normal contract assembles the true `BulkPhysicalSecondOrderJet`
conditionally.  Under sectorwise `HasNoTangentialRadical`, the transported
actual induced-metric value is invertible and its pointwise Koszul quadratic is
formed from the actual first derivative.  Symmetry of that raw derivative in
its metric slots, equality of its explicit symmetrization with the raw tensor,
and the raw Koszul identity are proved pointwise.  A realized throat-background
core combines this quadratic with the pulled-back `U(1)²` jets.  The refined
true `ThroatPhysicalSecondOrderJet` assembly therefore externalizes only
`normalQuadratic`, its symmetry proof and `physicalNormal`; the earlier
whole-background assembly remains as a historical gate. These gates do not
construct a smooth global Levi--Civita connection, extract canonical normal
geometry, give an unconditional structured-background extraction or exhaust
the invariant basis.

## Program M foundation checkpoint — 19 July 2026

Program M's foundational layer is consolidated and paused pending a stable
geometric integration target from Program P. Its coefficient language is now
explicitly signed-capable: unsigned/nonnegative assignments are restrictions,
while a nontrivial involution and odd charge law remain optional added
structure. The compiled `MF-PBRIDGE-002` adapter maps every nonzero odd real
charge to P's binary `JanusCharge` plus a separate positive magnitude, without
supplying a metric, throat, physical mass interpretation or action. The next
test is a comparison of the same adapter on non-throat and throat geometries.
See [`program_m_status.md`](program_m_status.md).

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
JanusFormal.Branches.ProgramMFoundations
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
MF     relational foundational pilot; every emergence theorem remains open
M      candidate-theory specification, equivalence, consistency and predictivity gates

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
the existing spectral heat trace. The full product-throat operator now has the
same concrete nuclear certificate, its nuclear norm is bounded by its trace,
and its positive-time family is `C∞` in operator norm. At every derivative
order, its explicit degeneracy-resolved diagonal sum equals the nuclear trace
derivative and obeys PT. These facts close the
trace-class properties required by Program P despite the absence of a general
Mathlib trace-class API. The complete multiplicity-aware D10 Gaussian is now
also summable at every positive time. Its physical PT permutation preserves
the squared spectrum, reverses root chirality, makes the infinite chiral trace
zero and sends the net of arbitrary finite spectral cutoffs to zero. This
Gaussian is now also realized on the complete D10 Hilbert space as a compact
operator with a summable rank-one nuclear expansion; finite spectral
truncations converge to it in operator norm. This closes the physical D10
continuum block. A separate global nuclear reference regulator now covers all
completed ambient sectors; its identification with the physical Hessian and
the full Fredholm/Quillen family remain open.

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
stratification is closed from the orthogonal-lift contract; constructing that
lift remains open. The expected fundamental group is `Z`, not `Z4`.

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
the exact one-loop sign. The transported differential quotient family now has
its smooth vector-bundle atlas and an exact smooth total-space comparison.
Any continuous intrinsic quadratic form on it canonically yields open
spacelike/timelike/non-null strata, a closed null stratum and a closed joint
frontier contained in the null locus, with exact scaling laws. For the actual
intrinsic quotient Lorentz metric, the pushed unit latitude normal now defines
the preferred fiber equivalence instead of an arbitrary pointwise choice. The
anchor-independent global fiber-linear lift represents every quotient class
and is orthogonal to throat tangents. In every transported normal chart its
metric square is exactly `scalar^2`; hence
`CanonicalGlobalNormalMetricSquareLocalRegularity` is discharged and the
metric square is globally continuous. The directly defined global spacelike,
timelike, null, non-null and joint strata consequently satisfy their
open/closed laws, total cover and joint-in-null inclusion unconditionally. The
canonical unconditional wrapper is a `def`. Packaging the same data into the
generic dependent `ContinuousOrthogonalDifferentialNormalLift` record remains
a separate optional bridge and is not needed by this direct stratification.
The explicit latitude curve
now supplies an actual cover tangent normal whose ambient coordinate
derivative is `(e₀, 0)`. The sphere ambient map and its smoothness are now
public, and the intrinsic ambient derivative factors exactly through the
public product-coordinate derivative. That derivative is now identified with
the continuous-linear equivalence induced by the global product
diffeomorphism. The canonical latitude normal has exact product image and
ambient image `(e₀, 0)`; the ambient image and the tangent vector are both
nonzero. For the actual intrinsic cover Lorentz tensor, its square is exactly
`1` and it is orthogonal to every tangent in the differential of the fixed-
throat inclusion; it is therefore spacelike and non-null. Its pushforward now
also supplies the explicit canonical local quotient-normal lift described
above. That local orthogonal splitting proves that the retained intrinsic
Lorentz metric has no tangential radical anywhere on the effective throat;
its smooth symmetric throat trace is therefore genuinely nondegenerate and
is packaged on the nondegenerate throat-metric domain. One deck turn now
reverses the quotient latitude parameter and its tangent normal by the exact
dependent sign law; the sign-clutched coordinate change preserves both the
local scalar-square model and the square of the orthogonal lift. The curve law
itself now extends to every integer winding through
`normalSignRepresentation`: even windings act trivially and odd windings flip
the latitude parameter. The dependent tangent `HEq` and scalar quadratic-model
invariance extend to every winding as well. The chosen global lift is a
fiberwise-linear operator family, not a nonzero global normal section; its
metric-square continuity and direct causal stratification are unconditional as
above. At cover level, the
named latitude normal is now `HEq` to its raw curve derivative after exposing
the zero-latitude transport. The projection chain rule and its dependent
base-point transports now identify the pushed canonical quotient normal by
`HEq` with the quotient-latitude tangent. Explicit base-point transport turns
this into an ordinary equality in one tangent fiber and commutes with scalar
multiplication. Therefore the canonical quotient normal obeys the exact sign
cocycle for every integer winding. This supplies the anchor-independent global
algebraic lift and the preferred equivalence used by the closed local-regularity
proof. Only the optional generic dependent continuous-lift record is separate.

The ambient quotient atlas now also has an unconditional pointwise
orthonormal reduction. At each base point a genuine reference lift is chosen,
the Euclidean quadratic form is transported by the actual tangent transition,
and the strict tangent cocycle proves overlap compatibility. This is an
atlas-wide pointwise object. A global Whitney embedding now supplies a positive
pullback metric; its Gram--Schmidt frames, inverse frames and genuine
orthogonal overlap maps are jointly `C∞` on their true chart domains. This
inhabits the smooth orthonormal-reduction contract.

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
global choices, not a canonical functor of the real normal line. The ambient
Clifford development is now complete at the topological bundle level.
Cartan--Dieudonné and determinant parity give `Spin(4) → SO(4)` surjectivity,
while nonorientability proves that an honest oriented Spin/SpinC Čech
realization on the mapping torus is impossible.

The appropriate twisted construction is no longer open. The concrete
`Pin⁻(4)` projection has kernel `{±1}`, is a covering with local sections, and
its continuous canonical Čech cocycle defines the ambient principal bundle.
The reference order-four generator projects to the explicit `O(4)` reflection.
The winding, inverse and triple-overlap laws are exact on the genuine chart
refinement, and the ambient winding equals the throat
`localTransitionWinding`.

The real-normal restriction is also explicit. The canonical latitude normal
lift is jointly `C∞`; its coordinates in genuine tangent trivializations are
`C∞` and nonzero. The normalized half-angle Clifford vector `e+n` supplies a
zero-cochain that intertwines every integer winding, is pointwise independent
of chart and path, and is continuous for every continuous nonzero horizontal
normal field. The one-sided sign is carried by the central `-1`, reverse
overlaps are exact inverses, and one loop squares to that central sign.

The subsequent `PinC(4)` quotient, determinant character and line, winding
twist, complex spinor representation, ambient spinor bundle, Hermitian
pairing, D9 half-spinor bundle and its smooth section/connection interfaces
are all constructed in the Program-P façade. This does not contradict the
oriented SpinC no-go: these are twisted `PinC` bundles built from the genuine
`Pin⁻` cocycle.

The normal-presentation comparison sub-lock is now closed:
`P0EFTJanusMappingTorusCanonicalLatitudeNormalPresentationComparison4D`
defines the explicit cover-product-to-quotient-tangent coordinate map and
proves, at the throat, the exact equality
`canonicalLatitudeNormalCoordinate_eq_sectionPresentation`. This is a `T01`
Pin⁻/presentation bridge; it did not close the terminal typed
foundation/pairing certificate by itself. That certificate was closed
separately on 26 August 2026.

## 5. Program P

### Checkpoint d'intégration — 28 juillet 2026

- Façade Lean : build vert `10039/10039`.
- Agrégat analytique scalaire : build focalisé vert `9317/9317`; son théorème
  marque la fermeture des imports, pas l'instanciation des interfaces physiques.
- Audit d'intégrité à ce checkpoint historique : vert, compteur alors `0/14`.
- Nouveaux résultats : spectre SpinC signé abstrait réalisé sur une base de
  Hilbert complète avec domaine maximal dense, auto-adjonction, gap quart,
  Fredholm et indice nul; jauge Pin⁻ demi-angle explicite et entrelacement de
  tous les windings; courbes LL anisotropes et cisaillements lisses de vrais
  repères générateurs; assemblages `C²` neuf secteurs et critères concrets pour
  Candidate A, matière, Robin/LL/BV et Einstein--Maxwell, y compris toute mesure
  finie sous les hypothèses de continuité jointe affichées. Dans chaque secteur
  de racine fixé, la synthèse SpinC géométrique du bloc bas-énergie
  zéro/premier signé est désormais injective pour tout paquet fini de modes
  du cercle et entrelace le vrai Dirac.
- Les paquets
  `GEO/FIELD/ANALYSIS/BOUNDARY/KJ-01/KJ-02/NATURAL/ACTION/EULER/NOETHER/`
  `HELMHOLTZ/VARCOH-GLOBAL-01` sont
  fermés : géométrie Candidate A sur le domaine global admissible de la
  racine, configuration et tangent uniques, produit `H¹`/trace/domaines
  fermés, bord canonique, complexe covariant physique, cohomologie de jauge
  `H⁰`, classification naturelle finie, action régulière assemblée, Euler et
  Helmholtz chartwise, Noether physique `U(1)²` et cohomologie fonctionnelle
  globale. `DIRAC-GLOBAL-01` et `REGULATOR-GLOBAL-01` sont maintenant `DONE`
  à leurs portées déclarées : synthèse Dirac géométrique signée, puis
  régulateur nucléaire de référence compact et injectif sur tous les secteurs
  ambiants complétés. `BRST/QUILLEN/ANOMALY-GLOBAL-01` conservent leurs
  certificats de frontier intégrés. `HESSIAN-GLOBAL-01` est maintenant une
  `FRONTIER` concrète : l’obstacle d’interface pour les domaines ouverts est
  levé et le paquet Einstein--Hilbert à métrique générale est désormais fermé
  par une famille locale `C²` exactement égale à l'action intrinsèque au point
  physique. L’accord du régulateur avec une
  Hessienne physique compatible et la trivialisation d’anomalie restent à
  construire. `SCHEME-GLOBAL-01` est
  formellement bloqué par deux témoins de liberté de schéma et requiert une
  donnée microscopique.
- Registre autoritatif : [carte de fermeture `HESSIAN-GLOBAL-01`](hessian_global_01_closure_map.md).
  Toute liste de résidus ci-dessous est historique et cède devant ce registre.
- `HESSIAN-GLOBAL-01` reste ouvert comme `FRONTIER`, et non `DONE`. L’API de
  carte locale sur un domaine admissible ouvert est désormais fermée, et les deux
  incohérences de modèle les plus nettes sont corrigées. Le tangent, le
  domaine et la cible physiques sont désormais D10-free; l’ancien agrégat D10
  reste réservé au régulateur/déterminant.
  Le paquet `P0EFTJanusProgramPRegularGeneralMetricC2EinsteinHilbert4D` ferme
  aussi H05/P1 : courbure Riemann/Ricci/scalaire fidèle, densité et intégrale
  sur la mesure finie commune, `0 ∈ U`, action `C²` sur `U` et accord exact
  avec `intrinsicEinsteinHilbertAction`, sans ansatz métrique restreint.
  P2 possède maintenant la famille normale induite, son ouvert uniforme,
  l'inverse, la densité et la mesure intrinsèques, mais l'action GHY existante
  reste attachée au bord canonique fixe. P3 a les adaptateurs et cœurs denses,
  mais attend encore l'unique pont hors-shell divergence produit–cut-bulk. P4
  ferme le résidu mixte matière–LL et la sous-somme Fredholm SpinC×LL
  stationnaire ; les blocs typés restants et l'indice total restent ouverts.
  Les obligations exactes sont maintenues uniquement dans la carte ci-dessus.
  La matière Candidate-A utilise
  directement les sections SpinC primitives et possède une action graphe dont
  le second Fréchet est exactement `2D+m²`, Fredholm, avec accord sur le cœur
  spectral fini. Les gauge fermions D9 abélienne/difféomorphisme ont de vrais
  types distincts `c/c̄/B`, un BRST nilpotent, `sΨ`, un Hessien symétrique et
  les symboles FP attendus. La divergence métrique et le de Donder complet
  sont maintenant de vraies 1-formes globales lisses, sans postulat nouveau.
  Le de Donder est en outre une application linéaire. Sa contraction
  métrique intégrée est une forme bilinéaire symétrique qui polarise exactement
  la fonctionnelle quadratique associée; le frame tangent fini fournit
  maintenant la caractéristique relevée qui étend exactement ce pairing à un
  graphe Hilbert raffiné. Le Hessien borné symétrique ainsi obtenu est le
  pairing lorentzien original sur le cœur lisse, et l'action quadratique du
  graphe est `C∞` avec ce second Fréchet constant. Les potentiels intrinsèques
  Candidate-A s'injectent désormais fidèlement dans le tangent physique
  minimal. Le Lorenz possède une complétion graphe dense et injective, un
  Riesz borné symétrique de noyau exact, et son pairing est le vrai Hessien
  BRST réduit on-shell. Son extension abélienne off-shell ajoute sans dupliquer
  le potentiel les vrais champs `B/c̄/c` et la caractéristique FP `δ_g d c`.
  Son cœur BRST lisse s'injecte dans une complétion de caractéristiques définie
  comme la fermeture de son image. Son Hessien et son représentant de Riesz
  bornés sont symétriques, et son action quadratique `C∞` a pour second
  Fréchet constant exactement la polarisation du `sΨ` spécialisé à la mesure
  lorentzienne canonique. La closabilité de l'opérateur différentiel projeté
  n'est pas encore affirmée.
  Le produit bulk abélien étendu remplace désormais, sans le dupliquer, le
  facteur potentiel/Lorenz par ce graphe off-shell. Avec les deux graphes de
  Donder, la matière SpinC primitive et LL, son cœur est injectif et dense,
  son action est `C∞`/`C²`, son second Fréchet est la somme exacte des Hessiennes
  sectorielles et son application cœur-vers-tangent typé est injective. Cette
  action reste une somme quadratique de secteurs, pas encore le pullback de
  l'action covariante non linéaire complète.
  Pour une métrique fournie, le secteur difféomorphisme possède aussi son
  graphe off-shell réel linéarisé mono-métrique `h/c/c̄/B`: BRST carré nul,
  égalité exacte à son `sΨ` linéarisé,
  complétion de caractéristiques injective et dense, Riesz/Hessien symétrique,
  action `C∞`/`C²` et inclusion non minimale typée injective. Cette porte ne
  choisit volontairement pas comment les deux de Donder Candidate-A se
  couplent à l'unique triplet diagonal. La porte diagonale suivante réalise
  maintenant le choix dérivé par l'adjoint cinétique : un seul cœur à deux
  perturbations métriques et un triplet possède BRST carré nul, graphe dense
  injectif, Hessien/Riesz/action exacts issus du `sΨ` pondéré et raccord typé.
  Ce facteur remplace les deux de Donder dans le produit abélien/matière/LL ;
  le nouveau produit bulk a une action `C²`, le Hessien assemblé comme seconde
  dérivée exacte et une application graphe/tangent typé injective. Son produit
  imbriqué `WithLp 2` est maintenant un Hilbert réel complet, continûment
  équivalent au chart à norme max ; le cœur reste dense/injectif et le Hessien
  possède un représentant de Riesz borné auto-adjoint exact.
  Le secteur fini des normalisations de faces nulles est aussi fermé sur
  `EuclideanSpace ℝ NullFace` : l'action exacte GHY + faces/contre-termes/joints
  y est constante, donc son Hessien et son Riesz auto-adjoint sont nuls. Cela
  ne couvre pas la géométrie de bord générale.
  Le raccord central
  `P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D`
  est maintenant explicite sur le même cœur lisse. Il
  projette le tangent typé corrigé vers le tangent physique minimal, l'inclut
  dans l'ancien tangent avec coordonnée D10 nulle, puis, pour tout habitant du
  pont de carte variationnelle déjà défini, compare le vrai second Fréchet
  covariant au Hessien du graphe diagonal. La gate
  `P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D` corrige
  l'interprétation de cette identité : l'ancien résidu est la Hessienne
  physique à conserver, plus le seul défaut d'identification matière--LL.
  La cible exacte est donc « Hessien covariant gauge-fixé = graphe BRST/
  matière/LL + Hessienne physique », équivalente uniquement à l'annulation
  du défaut même-action matière--LL. Annuler tout l'ancien résidu aurait
  supprimé la dynamique Einstein--Maxwell/bord.
  `P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D`
  porte maintenant cette comparaison directement sur le tangent physique
  minimal D10-free. L’ancien pont étendu est conservé seulement comme
  factorisation démontrée à coordonnée D10 nulle.
  La gate
  `P0EFTJanusProgramPGlobalCandidateAMatterFiniteGraphVariationalChart4D`
  construit toutefois un premier habitant non constant et sans axiome pour le
  sous-secteur matière : le cœur fini reçoit exactement la norme de graphe,
  les neuf blocs de l'action covariante sont `C²`, son pullback est le spectateur
  constant plus l'action quadratique SpinC, et son vrai `globalCandidateAHessian`
  est exactement le pullback du Hessien `2D+m²`. Cela ferme le raccord de carte
  matière, mais pas le pont diagonal total ni son résidu métrique/bord.
  La gate
  `P0EFTJanusProgramPGlobalCandidateABoundaryReparametrizationVariationalChart4D`
  raccorde aussi les normalisations des générateurs nuls à l'action covariante
  réelle : les neuf blocs sont `C²`, le pullback est constant et le vrai
  `globalCandidateAHessian` est nul. Sa portée reste la reparamétrisation de
  normalisation; elle ne traite ni déplacement normal ni géométrie de bord générale.
  Cette gate fournit aussi un prolongement générique de toute carte covariante :
  le Hessien étendu est exactement le pullback par la première projection et
  tous les blocs mixtes avec une normalisation sont nuls. L'instanciation avec
  la carte matière conserve donc exactement `2D+m²`, sans terme croisé de bord.
  `P0EFTJanusProgramPGlobalLocalVariationalChart4D` retire l’ancien obstacle
  d’interface : une famille locale ne fournit des données physiques que sur un
  ouvert `U` du modèle normé, avec `0 ∈ U`, et demande les neuf régularités
  `ContDiffWithinAt` seulement dans `U`. L’ouverture les convertit en vraies
  régularités ambiantes au point admissible; l’Euler et le Hessien de Fréchet
  agissent donc sur tout l’espace tangent du modèle et le Hessien est symétrique.
  Le fallback hors de `U` n’ajoute aucune donnée physique. Toute ancienne carte
  globale se replonge par `U = univ`, avec action, Euler et Hessien inchangés.
  `P0EFTJanusProgramPGlobalCandidateADiagonalLocalCovariantHessianResidualBridge4D`
  raccorde maintenant ce Hessien local au cœur lisse diagonal déjà construit.
  À tout point admissible, la Hessienne des neuf blocs se scinde exactement
  en Hessienne physique et Hessienne matière--LL. Le graphe augmenté conserve
  la première; son accord avec le Hessien covariant gauge-fixé équivaut à la
  seule identification même-action matière--LL. Le cas historique `U = univ`
  reste compatible et aucun bloc n’est dupliqué.
  La brique racine ponctuelle n’est plus limitée à une dérivée au centre :
  `P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D` construit,
  autour de tout target à spectre réel strictement positif scindé, un domaine
  de perturbations ouvert contenant `0`, une branche `C²` sur tout ce domaine
  et l’identité carrée exacte. Ce n’est ni diagonal ni Minkowski. Plus
  généralement, toute racine continue vérifiant l’identité carrée et la
  bijectivité de Sylvester point par point est automatiquement `C²` dès que sa
  cible l’est. Le recollement local n’est donc plus manquant.
  `P0EFTJanusContinuousMatrixFieldContDiffLocalRootBranch4D` ferme désormais
  l’étape intermédiaire `C⁰` sur toute base compacte : la régularité de
  Sylvester ponctuelle induit une équivalence bornée sur l’espace de Banach des
  champs matriciels continus, puis un domaine uniforme ouvert contenant `0`,
  une branche `C²` et l’identité carrée exacte.
  `P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D` réutilise ensuite
  les inclusions continues déjà prouvées `C⁰ → L²` et `H¹ → L²` pour construire
  leur égaliseur fermé. Ce véritable espace de Banach scalaire `C⁰ ∩ H¹`
  contient exactement le cœur lisse, sans plongement de Sobolev ni nouvel
  axiome. Pour ne pas supposer sa densité simultanée,
  `P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0CoreClosure4D` prend
  explicitement la fermeture de ce cœur dans la norme forte; elle est complète,
  injective dans l’égaliseur et l’image lisse y est dense par construction.
  `P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0SmoothLeibniz4D` réutilise
  ensuite le produit scalaire lisse existant et prouve la formule exacte du
  premier jet `(fg, f·dg + g·df)`, ainsi que sa bilinéarité vers ce cœur.
  `P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0ProductExtension4D` ferme
  aussi l’estimation forte par Hölder `L∞·L² → L²` et prolonge canoniquement ce
  produit en une application bilinéaire continue sur toute la fermeture,
  avec accord exact sur le cœur lisse et sans hypothèse supplémentaire.
  `P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0MatrixProduct4D` assemble
  maintenant cette multiplication sur les `4 × 4` coefficients : le produit
  matriciel est bilinéaire continu, son représentant `C⁰` est exactement le
  produit ponctuel, et le carré est `C∞` avec dérivée de Sylvester exacte.
  `P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0LocalRootBranch4D`
  réutilise alors l'inverse ponctuel déjà construit : pour toute racine
  matricielle lisse générale dont le Sylvester est bijectif point par point,
  ses coefficients inverses sont lisses et définissent une véritable
  équivalence bornée sur le cœur fort. Le théorème d'inversion fournit ainsi
  un ouvert `U` du Banach tangent entier, `0 ∈ U`, une branche `C²` et
  l'identité carrée exacte, sans cas diagonal ni nouvel axiome.
  La restriction artificielle aux matrices `4 × 4` est maintenant levée.
  `P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D`
  construit le produit fort associatif pour toute taille finie, avec accord
  lisse/continu et carré `C∞` à dérivée de Sylvester exacte.
  `P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D` encode ensuite la
  racine Candidate-A intrinsèque dans les générateurs tangents finis déjà
  disponibles. Comme cette famille est redondante, son identité est le
  projecteur lisse `P`, pas la matrice ambiante `I`.
  `P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCorner4D` et sa gate
  `...CornerAlgebra4D` construisent le coin fermé complet `P M_N P`, y placent
  exactement la racine intrinsèque et internalisent produit, carré et
  Sylvester. Enfin `...CornerLocalRoot4D` fournit une brique IFT Banach
  générique et, sous bijectivité du Sylvester fort au centre, une branche de
  racine sur un ouvert `U`, avec `0 ∈ U`, branche `C²` sur tout `U` et identité
  carrée exacte sur `U`. Cela n'impose ni repère global ni nouvel axiome physique.
  `P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixLinearEquivLift4D`
  relève maintenant toute famille lisse d'opérateurs matriciels finis
  ponctuellement bijectifs en une équivalence bornée sur le cœur fort. Les gates
  `...StrongFiniteFrameSylvesterRegularity4D`, `...SylvesterLocalRoot4D` et
  `...SylvesterCornerLocalRoot4D` appliquent cette brique au Sylvester
  Candidate-A : elles étendent l'opérateur par l'identité hors du coin, prouvent
  l'accord fort par densité, la commutation au projecteur, puis la bijectivité
  du Sylvester du coin à partir de la régularité intrinsèque ponctuelle. Le
  branche locale `C²` sur tout un ouvert `0 ∈ U` en découle donc sans nouvel
  axiome.
  La même gate formalise maintenant la restriction honnête : le sous-type
  `GlobalCandidateASylvesterRegularGeometry` porte exactement la preuve
  intrinsèque, et une carte locale déclarée régulière transmet cette branche à
  chacun de ses paramètres admissibles.
  `P0EFTJanusProgramPGlobalStrongH1C0AnalysisDomain4D` applique cette brique au
  type fini `GlobalBulkSobolevSlot` déjà existant : toutes les
  coordonnées bulk métriques, jauge et fantômes ont donc un produit complet,
  compatible dans `L²`, où le vrai tangent lisse se relève exactement. Le
  L'encodage covariant général, l'algèbre forte du coin, le transport de
  régularité et l'interface locale sont donc construits. La portée honnête est
  la strate ouverte des racines intrinsèquement Sylvester-régulières : le type
  non qualifié `GlobalCandidateAGeometry` contient aussi des racines singulières.
  `P0EFTJanusProgramPGlobalCandidateAPositiveSelectedRootSylvester4D` ferme le
  cas physique sélectionné : l’égalité de la racine stockée au sélecteur
  spectral positif implique sa régularité Sylvester intrinsèque et active la
  branche locale forte, sans ajouter cette régularité comme axiome.
  `P0EFTJanusProgramPGlobalCandidateALocalRootJointRegularity4D` montre en plus
  qu'une cible forte `C²` tire cette branche en arrière sur un ouvert et donne
  automatiquement des coefficients de racine conjointement continus en
  paramètre et point d'espace-temps, avec carré exact.
  La couche uniforme d'ordre deux est maintenant construite :
  `P0EFTJanusMappingTorusCanonicalPhysicalScalarC2JetCore4D` ferme le cœur
  scalaire complet valeur/premier jet/second jet et son Leibniz exact, puis
  `...ScalarC2ToStrongH1C0Bridge4D` l'envoie continûment vers le cœur fort.
  Les gates `...C2FiniteMatrix*`, `...C2LocalRootBranch4D` et
  `...C2LocalRootJointRegularity4D` donnent le produit matriciel fini
  associatif, le carré `C∞`, l'inverse de Sylvester, une branche locale `C²`
  sur un ouvert et la continuité jointe de chaque jet complet de coefficient.
  Enfin les trois gates `...CandidateAC2FiniteFrame*` construisent le coin
  intrinsèque complet `P M_N P`, y placent la racine sélectionnée et transportent
  la régularité Sylvester intrinsèque jusqu'à une vraie branche locale C² à
  carré exact. Aucun repère global ni axiome physique n'est ajouté.
  L'intégrale contre toute
  mesure finie est maintenant linéaire continue sur le cœur scalaire fort :
  des lifts forts `C²` du volume/courbure et du volume/pairing donnent les
  vraies lignes Einstein--Hilbert/Maxwell `C²`. Le chart local de racine
  d'ordre deux n'est donc plus manquant. Restent l'application métrique
  générale vers le cœur C² qui construit effectivement les lifts de
  volume/courbure et volume/pairing, puis les neuf données d'action `C²`.
  À la métrique Candidate-A, ce cœur s'injecte conjointement dans le graphe et
  dans `GlobalGaugeFixedPhysicalFieldTangent`, avec le triplet
  difféomorphisme maintenu nul. Le cœur LL complet
  `llAuxMetric × llMeasure × llField` possède lui aussi une complétion graphe
  dense et injective et un Riesz auto-adjoint égal au Hessien same-action,
  termes croisés compris. Il porte maintenant une action quadratique `C∞` dont le
  second Fréchet constant est exactement ce Hessien. À un fond stationnaire,
  l'équation de mesure force `llField = 0`; les poids auxiliaires et termes
  croisés s'annulent, et le quotient par le noyau exact de la projection champ
  est continûment équivalent à `LLH1Space`. Son Riesz quotient est l'identité,
  donc Fredholm d'indice zéro. Ce résultat est strictement on-shell/flux nul et
  ne prouve aucune coercivité ou fermeture d'image LL off-shell. Le contrôle
  opératoriel off-shell (bornitude, auto-adjonction, noyau/radical exact) est
  donc fermé. La réduction auto-adjointe montre toutefois que portée fermée et
  radical fini suffisent automatiquement au conoyau fini; seules ces deux
  estimées LL restent indépendantes.
  Les deux graphes de Donder métriques et le graphe Lorenz
  sont aussi assemblés dans un sous-chart physique commun
  métrique-plus-Abelien : son action est `C∞`, son second Fréchet est la somme
  exacte des deux pairings de Donder et du Hessien BRST Lorenz, et son cœur
  lisse s'injecte dans le tangent gauge-fixed typé en gardant les coordonnées
  non minimales nulles. Avec le graphe matière SpinC et le graphe LL, il forme
  maintenant un produit bulk dont l'action quadratique est exactement la
  somme des trois actions de graphe et dont le cœur jauge lisse × coefficients SpinC
  finis × LL lisse s'insère linéairement, injectivement et densément pour la
  vraie norme de graphe. À la métrique Candidate-A et à `matterMassSquared`,
  ce même cœur s'enregistre conjointement dans le graphe et dans les slots
  exacts de `GlobalPhysicalFieldTangent`, avec application conjointe injective.
  Aucune application de toute la complétion graphe vers le tangent lisse n'est
  affirmée. Ce sous-chart n'est pas le chart total. Manquent encore l'adjoint
  différentiel/Green et l'identification de cette somme quadratique au
  pullback de l'action covariante non linéaire complète. Le remplacement
  abélien nondupliquant est maintenant construit; restent son identification
  avec l'action covariante et la closabilité différentielle. Le bloc
  difféomorphisme diagonal existe, son couplage est fixé par l'adjoint
  cinétique pondéré et son insertion bulk est effectuée. Manquent encore les vrais
  blocs same-action normal et bord géométrique général, les blocs
  Einstein--Maxwell en directions
  métriques générales,
  les deux estimées LL off-shell et l'assemblage Fredholm same-action. Le cœur
  graphe/typé est déjà fidèle; la cible spectrale historique `ι × Fin 8` ne
  représente pas la multiplicité totale. Le no-go interdit toujours de
  réutiliser silencieusement l'ancienne cible D10-étendue et de déduire le
  Fredholm de `C²` sans strate elliptique non dégénérée explicite.
- `ADM/STABILITY/VACUUM-GLOBAL-01` ont maintenant des frontières intégrées :
  chaîne Legendre/contraintes/rang exacte en FLRW, noyau contraint et courbe
  isoénergétique exacts, minimum proportionnel unique et no-go de rang du vide.
  Aucun n'est marqué `DONE` : shifts et crochet fonctionnel, exclusion BD,
  stabilité du quotient et action effective microscopiquement fixée manquent.
- `MICRO-GLOBAL-01` et `SCALE-GLOBAL-01` ont maintenant des certificats de
  no-go intégrés :
  deux parents admissibles produisent des mixages réduits différents, tandis
  que géométrie, Dirac/LL, chaleur et charges gardent une orbite commune de
  redimensionnement. Il faut encore une loi microscopique sélectionnante, ses
  parties finies et un ancrage dimensionné indépendant; aucun rayon observé
  n'est injecté.
- Aucune nouvelle hypothèse physique ni axiome métier; axiomes transitifs
  constatés : `propext`, `Classical.choice`, `Quot.sound`.
- La liste exhaustive canonique des 24 paquets globaux et 14 portes reste
  [`program_p_operational_todo.md`](program_p_operational_todo.md).

The explicit nonabelian `so(3)` ghost triple and the corrected Koszul
differential are now closed for the entire currently implemented field/BV
package: linear matter/gauge/auxiliary sectors, positive diagonal metrics,
bulk and throat antifields, master actions, PT covariance, and boundary trace.
The nonlinear frontier also has one unified square-zero field/ghost/BV/boundary
packet, functorial intrinsic pullbacks on Maxwell one-forms and covariant
two-tensors, and a canonical coadjoint antifield representation. The Maxwell
pullback now has the same genuine fiber derivative, smooth global realization,
and linear flow-to-ghost contract already available for metric tensors. The
measured-density convention is now explicit: scalar coefficients form a
finite pullback representation, their two-ghost BRST square vanishes, and the
existing integrated scalar action is covariant when its measure is pulled
back simultaneously. On the fixed throat, the already proved scalar bracket
identity now also induces a coadjoint action on algebraic scalar antifields,
with square-zero obstruction and invariant boundary pairing. For
Maxwell/metric fields the global bracket identity
`[L_c,L_d]=L_[c,d]` is an automatic consequence of Cartan evaluation. For
Maxwell one-forms, the global smooth Cartan action is now constructed,
bilinear in the ghost and potential, and packaged as
`GaugePotentialCartanActionData`; its `SmoothGhostLieRepresentation` and
bracket law are therefore closed. The associated field obstruction,
algebraic coadjoint-antifield obstruction and canonical evaluation pairing
are BRST closed; no geometric or integrated Maxwell antifield dual is claimed.
The metric residual is likewise tensorial in both test fields, packaged as a
symmetric covariant fiber tensor and specialized to smooth Janus tensors.
Its finite-frame local formulas now reassemble into the global smooth
bilinear `smoothMetricCartanAction`, packaged as
`symmetricTensorCartanActionData`; the induced metric Lie representation and
bracket law are closed. The canonical Maxwell and metric Cartan data are now
combined concretely by `canonicalTensorialCartanActionData`, and their
Maxwell/two-metric algebraic coadjoint antifields have square-zero
obstructions and invariant pairings. Identification of these
algebraic duals with geometry has advanced: the existing integrated metric
pairing now defines a genuine linear morphism from smooth two-metric
antifields to the algebraic dual. Finite-frame positive dualizers now prove
injectivity/nondegeneracy in both the bulk and throat sectors. Coadjoint
equivariance remains the precise separate obligation and is now
reduced exactly to the integrated skew-adjointness identity
`B(L_c α,h)+B(α,L_c h)=0`; no additional functional-BV assumption is hidden.
The invariant-measure integration-by-parts theorem for the genuine canonical
time and three rotation generators is now public, and its coefficient-field
skew form is recorded in the global BRST certificate. This is an LL
coefficient result, not the intrinsic tensor-pair identity: with a fixed
background metric/measure, all-ghost skew is generally false outside a
Killing, measure-preserving subalgebra (or without transporting the
metric/measure).
The existing affine nine-block diffeomorphism-symmetry interface is now
recorded beside this packet: any inhabitant yields assembled-action invariance
and the true Euler/Noether identity, while nonlinear nilpotence and boundary
stability are independent packet theorems. The certificate does not identify
the packet differential with the chart generator or Candidate-A action.
The exact conversion between transported and fixed measures is now isolated:
nine-block covariance with a transported measure becomes the existing
fixed-measure invariance contract whenever their equality is supplied. For an
arbitrary measure-preserving smooth self-diffeomorphism this equality, and the
corresponding fixed-measure general-Lorentz scalar action invariance, are
theorems.  The five measure-dependent Candidate-A block equalities are now
reduced to a supplied field-level transport contract: interaction,
Einstein--Hilbert plus and minus, and Maxwell plus and minus follow from seven
supplied smooth-field pullback identities. The canonical-throat fixed GHY
control vanishes at its base parameter, while the mobile sourced Robin block
must be transported explicitly. Adding supplied equalities for the four
remaining matter/LL/Robin/finite-BV blocks constructs the complete nine-block
contract. For the interaction identity itself, pointwise
determinant/root/spectral naturality reduces the missing geometry exactly to
pullback of the plus musical metric, conjugation of `rootAt`, and transport of
the regular basis. The canonical measure specializes this reduction to the
installed time-translation diffeomorphisms without a new measure assumption.
A concrete conformal time orbit `ℝ → GlobalFieldConfiguration` is now
constructed by translating an explicit positive scale and its PT partner; its
zero and additive action laws are exact. It is not an action-data family or a
chart lift. Thus no concrete `GlobalCandidateAActionData`, variational chart,
arbitrary global-field pullback or full chart flow is constructed, and the
identity flow remains formally possible in the abstract interface.
In particular, the Candidate-A action-data gravity/Maxwell API still passes
through the legacy `RegularGeneralLorentzMetric.frameEquiv` global-frame
requirement on the nonorientable quotient, whereas the newer scalar geometry
and standalone fixed-potential Maxwell action are frame-free. The static
frame-free volume and fixed-potential Maxwell components are now closed for
every `SmoothGeneralLorentzMetric`. The remaining Candidate-A prerequisites
include general `C²`/Fréchet metric dependence, interaction and gauge-varying
or mixed Maxwell data, and the variational chart/core. The
genuine holonomic transition has a public third jet whose
two outer directions commute. The coordinate-basis components of the
endomorphism curvature used by the intrinsic Bianchi gate are proved equal to
the Riemann components used by Einstein--Hilbert. A single fixed holonomic
transition also satisfies the full Levi--Civita/Christoffel law as a
neighborhood `EventuallyEq`, after proving that its fixed and re-anchored
local inverses agree as germs. This law is now extended to arbitrary vectors,
differentiated with all Jacobian/connection product terms, and
antisymmetrized. The symmetric second and third transition jets cancel, giving
the unconditional tensorial law
`J (R₁(u,v)z) = R₂(Ju,Jv)(Jz)` and its endomorphism-valued corollary.
Ricci is now the trace of this arbitrary-vector curvature and its matrix obeys
the same Jacobian congruence as the metric. Inverse-metric contraction proves
chart independence of the local scalar curvature. The unconditional total
holonomic cover and local-inverse smoothness then glue it to the genuine
`globalSmoothScalarCurvature`; every legacy `RegularGeneralLorentzMetric`
therefore produces a `RegularEinsteinHilbertMetric`. The standalone
`frameFreeEinsteinHilbertAction` now integrates the computed scalar against
any supplied finite nonzero action measure. For every
`SmoothGeneralLorentzMetric`, the positive smooth chart-independent
`globalMetricVolumeRatio` weights the explicit intrinsic reference measure to
the finite nonzero `generalLorentzActionMeasure`, recovers the canonical
measure at the intrinsic metric, and gives
`generalLorentzFrameFreeEinsteinHilbertAction`. This closes only the static
relative-volume construction: covariance of the fixed reference under
arbitrary diffeomorphisms and `C²`/Fréchet dependence on the metric are not
proved. Candidate-A interaction, gauge-varying or mixed Maxwell regularity and
the frame-free variational chart/core remain open. No formal emptiness theorem
for the legacy type is claimed.
On the Hessian side, every supplied differentiable genuine nonlinear
diffeomorphism flow now gives, at a critical chart configuration, a
two-sided kernel equal to the span of its pointwise generators. The genuine
Hessian descends exactly both by this flow submodule and by its sum with the
physical `U(1)²` directions. This is conditional on the flow symmetry,
generator differentiability, criticality and the still-supplied chart; it
does not construct those data.
The ninth `finiteBV` functional is now separately closed under its genuine
finite null-generator reparametrization, reusing the generator/interval data
already carried by the global boundary package and requiring only the two
displayed density-integrability hypotheses. This does not inhabit the
nine-block affine ghost interface: existing finite-covariance results use a
nonlinear pullback and transported measure, whereas that interface currently
uses an affine chart orbit with fixed measure.
The already-proved arbitrary-path diffeomorphism invariance of the historical
eight-scalar matter action is now imported by the global BRST certificate;
this scoped result does not yet cover the Candidate-A SpinC matter block.
Derivative kernels, completed spaces, and arbitrary functionals remain a
strictly stronger open refinement.

The canonical remaining-work register is
[`program_p_operational_todo.md`](program_p_operational_todo.md).

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
configuration inhabits it. The quotient itself now has the analytic manifold structure, and both the spacetime quotient and fixed throat are compact. Smooth quotient/throat coefficient fields form real vector spaces; smooth fields inject into the genuine completed `L²` space for finite Borel measures, with Hilbert structure under explicit fiber hypotheses and an isometric PT equivalence for PT-preserving measures. Smooth throat trace, PT-equivariance and a nonempty exact Dirichlet condition are proved. A finite global `C∞` tangent-generating family is now constructed from a finite trivialization cover and a subordinate partition of unity. It feeds the completed first-jet graph `H¹`, whose smooth fields are dense and whose forgetting map to `L²` is continuous. For spacetime measure pushed forward from a finite throat measure, the continuous trace has exact norm bound `1`. The canonical spacetime/throat volumes now instantiate this complete graph `H¹`; existence of the physical trace is equivalent exactly to one smooth codimension-one inequality. The exact FTC/Fubini estimate, twisted analytic latitude collar, throat-measure pushforward and `L²` trace identity are proved. The normal derivative is reconstructed exactly by the finite global frame. Joint `C∞` latitude regularity proves `CanonicalLatitudeNormalLiftContinuous`, and the radial--polar Euclidean calculation now proves the coarea inequality. The canonical physical trace bound, continuous operator, smooth agreement and existence theorem are therefore unconditional. `P0EFTJanusProgramPGlobalAnalysisDomain4D` now connects the true tensor/scalar tangent coordinates to a finite product `H¹`, its continuous throat trace, closed Dirichlet kernel and common SpinC/D10/LL domains; the earlier coefficient-only Sobolev TODO is closed. A populated independent-field package includes positive diagonal metrics, matter, gauge-coordinate, ghost, auxiliary and LL/throat coefficients; metric/root/trace fields are uniquely induced. One simultaneous independent-field curve now gives the exact componentwise derivatives of both induced metrics, the principal root and both matter traces, with zero induced cross-response from gauge, ghost, auxiliary and LL directions. The abelian `U(1)^2` sector is upgraded to intrinsic smooth one-forms with `A ↦ A+dλ`, exact diffeomorphism covariance, nilpotent BRST `s(A,c)=(dc,0)` and a bridge to the independent ghosts. General covariant tensors now have an exact involutive analytic-PT pullback preserving symmetry, nondegeneracy and Lorentz inertia. Tangent and nested Hom-bundle coordinates discharge `AnalyticPTTensorPullbackLocalSmoothness` unconditionally, yielding an involutive smooth pullback on the smooth Lorentz domain. The attached musical equivalence now pulls back with the same tensor, giving an involutive PT action and sector exchange on `SmoothGeneralLorentzMetric`; the holonomic scalar density is pointwise PT-covariant with coherently transported field and frame. Integrated spacetime PT invariance, BV ghosts and the curved Euler--flux PDE remain open. Global scalar `p = d phi` is the genuine manifold differential with exact throat/PT chain rules. Its fixed-frame diagonal global action now uses the inverse and volume of the same metric, and its fixed-metric/measure scalar variation is proved pointwise and after integration under an explicit contract. Arbitrary smooth inclusion-preserving diagonal diffeomorphisms now pull back all independent sectors with exact action laws, natural throat trace and a manifold tangent generator for smooth orbits. The LL measure/flux fields define an actual finite-measure worldvolume integral on the compact throat with a nonempty zero branch. The admissible null-variation domain is the open set `Theta ≠ 0`, deliberately excluding the proved singular point.
  The global field/domain package forces one root-admissible configuration to
  feed both general Lorentz metrics, primitive SpinC matter, D9, the derived
  throat trace and a tangent without a duplicate metric or physical D10 slot.
  Its physical common closed domain contains bulk Dirichlet `H¹`, SpinC graph
  and LL completion; a separate extended domain adds D10 for regulator and
  determinant work. The regular Candidate-A action and its
  complete chartwise Euler map are now assembled on the same configuration.
  Its actual symmetric Frechet Hessian and complete D10 spectral regulator
  layers are integrated. `REGULATOR-GLOBAL-01` is now closed separately by one
  positive-time reference operator on the exact bulk `L²`--SpinC--D10--LL
  product: it is compact, injective and nuclear. The bulk also has a compact
  Dirichlet inclusion and Gram regulator, with an adjoint lift of zero trace;
  SpinC and D10 retain their exact physical nuclear heats. Exact D9 continuum
  heat is nuclear under its explicit summability hypothesis, while finite
  packets are unconditional. The exact LL Hessian heat is compact only in
  finite dimension. No equality between the reference regulator and the
  global Hessian is asserted: D9 growth, LL elliptic heat, dense geometric
  synthesis and identification of the remaining action blocks with the
  gauge-fixed Fredholm family remain under `HESSIAN-GLOBAL-01`.
  The 30 July closure audit makes this obstruction structural rather than a
  generic residual TODO. D10 has now been removed from the physical target
  and the Candidate-A/primitive-SpinC matter mismatch is closed directly.
  Typed nonminimal BRST gauge fermions are also available, and the paired
  Abelian one is now global, has an injective off-shell graph-feature map and
  a canonical-volume Hilbert feature completion with exact `C∞` same-action
  Hessian; its core is attached to the corrected typed gauge-fixed tangent.
  The nonduplicating extended bulk now replaces the old Lorenz factor by this
  off-shell graph and combines it with the de Donder pair, primitive SpinC
  matter and full LL graph; its core is injective/dense, its quadratic action
  is `C∞`/`C²` with the exact sector-sum Hessian, and its typed core map is
  injective. This does not identify the sum with the nonlinear covariant
  action. The same five factors now have a continuously equivalent nested
  `WithLp 2` Hilbert chart, including the SpinC graph with its `L²` graph norm.
  The transported action is `C²`, has the same constant second variation, and
  its bounded Riesz representative is self-adjoint; the smooth core remains
  dense and injective. This uses the symmetric paired ghost/antighost Hessian
  and does not assert standalone scalar-FP self-adjointness. Differential
  closability is supplied only by the intrinsic
  conditional Green-core adapter described next. For the intrinsic
  metric, each Abelian FP component is nevertheless now identified pointwise
  and in physical `L²` with the canonical mass-zero scalar Euler operator. Its
  adjunction defect is exactly the scalar skew-density integral, and pairwise
  smooth-core symmetry is equivalent to that integral vanishing. The new FP
  Green--Stokes bridge composes the existing unrestricted scalar Green data
  with this identity: the defect is then exactly the oriented cut-bulk current
  and vanishes on every existing Green-isotropic domain (in particular
  Dirichlet, Neumann, real Robin and PT-fixed). It adds no axiom and does not
  construct that scalar Green datum. Conditional on that datum, the existing
  mass-zero Green core is exactly each FP component; the established cutoff
  theorem makes its minimal core dense and its completed graph projection
  injective. The four `Sector × Fin 2` components now form a completed paired
  graph with dense actual smooth-ghost core and a single-valued ambient-range
  realization agreeing with the true paired FP map. Thus intrinsic projected
  closability is no longer an additional premise once the Green datum is
  supplied. The existing completed-boundary-triple and analytic-closure bricks
  are now specialized to that exact FP core: for any supplied Lagrangian
  boundary condition and analytic package, all four real components have a
  dense realization domain and componentwise equality between actual-adjoint
  and realization domains. Their finite paired inclusion is dense/injective
  and agrees with the true FP map on the admitted smooth core. No inhabitant of
  the analytic package is constructed, so the result is conditional and is not
  a total-Hessian domain theorem. The stronger existing graph/direct-coercive
  endpoint is now connected too: its canonical-normal PDE data, graph estimate,
  Lagrangian condition and shifted coercivity already imply Rellich, a bounded
  real resolvent and actual scalar adjoint-domain equality; its admitted smooth
  realization is exactly the intrinsic FP component. Its local-divergence datum
  reconstructs the global Green--Stokes datum with definitionally the same
  scalar core. This removes any separate Green, new
  adjoint-regularity or Rellich premise, but the endpoint data remain
  uninhabited. The unconditional full 4D
  `integral_eq_divergence` theorem is
  still missing; the total Hessian-domain identification and the
  general-metric measure-compatible adjoint bridge also remain open. The
  genuine general-metric diffeomorphism
  Faddeev--Popov operator is also now constructed, without hypotheses, as the
  existing de Donder operator composed with the existing global Cartan metric
  action `c ↦ L_c g`. For one supplied metric this operator now feeds a full
  mono-metric off-shell `h/c/c̄/B` feature graph with square-zero BRST, exact
  `sΨ`, symmetric Riesz/Hessian, `C∞`/`C²` action and injective typed
  nonminimal attachment. By itself it makes no paired Candidate-A choice; the
  kinetic-adjoint bridge now selects the unique Einstein-weighted condition
  and global FP composite, and the diagonal off-shell gate realizes that
  selection on one shared two-metric/one-triplet core before insertion into
  the Abelian/matter/LL bulk graph.
  The old
  D10-extended realization remains excluded by the zero-Hessian no-go.
  `HESSIAN-GLOBAL-01` is an open analytic `FRONTIER`. The open-domain
  local-chart interface is available, but the zero-Hessian no-go proves that
  `C²` regularity alone cannot yield the terminal infinite-dimensional
  Fredholm realization. Finite-measure integration is now a continuous linear
  functional on the strong scalar core, so strong `C²` lifts of the actual
  volume/curvature and volume/pairing imply `C²` for the genuine
  Einstein--Hilbert and Maxwell action lines. The complete C² jet/root core is
  now constructed; what is not yet built is the actual general-metric map into
  it for volume, scalar curvature and Maxwell pairing. The completed
  diagonal bulk graph still needs identification with the full nonlinear
  covariant action, the normal and boundary same-action blocks, the
  arbitrary-general-metric Einstein--Maxwell blocks and the final faithful
  Fredholm sum on an explicitly constructed nondegenerate elliptic analytic
  stratum.
  In particular one typed diffeomorphism triplet cannot reproduce the old sum
  of two independent de Donder squares. Its replacement projection is now
  fixed to `F₊/(2κ₊)+F₋/(2κ₋)` and realized by the shared off-shell graph;
  the remaining tasks concern full-action/domain closure, not a choice of
  signs or weights.
  The intrinsic paired potentials now inject into the corrected minimal
  tangent. The refined de Donder graph now extends the exact Lorentzian pairing
  and carries a genuine `C∞` quadratic action. Its two metric copies and the
  Lorenz graph form a common physical gauge `C²` subchart whose smooth core
  injects into the typed gauge-fixed tangent with nonminimal coordinates fixed
  at zero. The complete three-slot LL sector separately has a dense injective
  graph completion and a `C∞` quadratic action with exact constant same-action
  Riesz Hessian. LL stationarity itself forces `llField = 0`; the Fredholm
  criterion and index-zero corollary now derive this fact directly, without a
  separately supplied zero-flux hypothesis. After quotient by the exact
  field-projection kernel, the Riesz operator is the identity and is Fredholm
  of index zero. This does
  not supply off-shell coercivity/closed range or the final coupled Fredholm
  estimate. The full off-shell Riesz operator is now proved self-adjoint, and
  a generic reduction plus its LL specialization show that closed range and
  finite-dimensional radical automatically give finite-dimensional cokernel.
  These are the two independent LL estimates still missing.
  The integrated-invariance and canonical scalar Euler--flux limitations in
  the preceding snapshot are now superseded; nonlinear BV remains open. For
  `SmoothGeneralLorentzMetric`, coherent PT transport of the
  scalar and tangent family gives exact density covariance, iff transport of
  integrability and invariance of the action against the canonical quotient
  Lorentz measure. The tangent family remains supplied explicitly. Separately,
  every `SmoothGeneralLorentzMetric` now has a statically constructed finite
  nonzero relative volume measure. `P0EFTJanusMetricVolumeDensityHessian4D`
  proves the genuine pointwise mixed second variation of `sqrt |det g|` along
  affine matrix curves with fixed determinant sign:
  `sqrt |det g| * (1/4 tr(g⁻¹h) tr(g⁻¹k) -
  1/2 tr(g⁻¹h g⁻¹k))`, symmetrically in `h,k`.
  `P0EFTJanusMappingTorusFrameFreeRelativeLorentzVolumeHessian4D` globalizes
  it, via `globalMetricVolumeRatio` and `generalMetricTensorPairingAt`, to a
  frame-free continuous and integrable density with symmetric integral.
  `P0EFTJanusMappingTorusConformalRelativeLorentzVolumeHessian4D` now supplies
  the genuine positive exponential conformal line
  `scale(t)=baseScale*exp(t*u)`: its exact relative ratio is `rho=scale²`,
  with derivatives `2*u*rho` and `4*u²*rho`. The second derivative splits
  exactly into the frame-free Hessian on the velocity plus the first variation
  on the acceleration, `2*u²*rho + 2*u²*rho`. For every fixed smooth scalar
  integrand, the varying-volume action is `C²`; differentiation under the
  compact finite-measure integral is factored through the shared
  `P0EFTJanusCompactParametricIntegralC2` helper. This is only a result along
  that explicit one-parameter conformal line, not `C²`/Fréchet dependence on a
  metric-section space: no section chart/topology or general metric variation
  is constructed. The fixed-integrand gate alone is not the general
  Einstein--Hilbert curvature variation.
  `P0EFTJanusMappingTorusHomotheticEinsteinHilbertHessian4D` now closes that
  variation on the positive constant-homothety slice of the intrinsic metric:
  Christoffel and Ricci are invariant, `R(scale*g0)=scale⁻¹*R0`, and the volume
  ratio is `scale²`. The genuine Einstein--Hilbert action equals its reduced
  affine-scale polynomial, with a symmetric Hessian. Along its positive
  exponential metric curve, the action is `C∞` (hence `C²`), and its second
  derivative is exactly the affine Hessian on the velocity plus the first
  variation on the acceleration;
  at `t=0` it is `u²/(2κ) * (Rtot - 8*Λ*Vol)`. This does not cover a
  spatially varying conformal factor, a general metric-space Fréchet Hessian,
  or the nine-block Jacobi operator.
  `P0EFTJanusMappingTorusConformalFrameFreeMaxwellHessian4D` independently
  globalizes, for every `SmoothGeneralLorentzMetric`, the Maxwell pairing of
  two arbitrary smooth abelian potentials, hence its diagonal Lagrangian
  density and action. The overlap proof uses `F₁=JᵀF₂J` together with
  `g₁=Jᵀg₂J`; the resulting global fields are smooth and integrable. In four
  dimensions a positive conformal factor sends the pairing and Lagrangian
  density to `scale⁻²` times their reference values while the relative volume
  ratio is `scale²`, so the frame-free action is exactly the reference action.
  Along `scale(t)=baseScale*exp(t*u)` at fixed potential, it is `C∞` and
  constant, with zero symmetric conformal Hessian.
  `P0EFTJanusMappingTorusFrameFreeMaxwellGaugeOrbitHessian4D` now proves
  global exact-gauge invariance in either pairing slot against an arbitrary
  second potential and for the action. The action along its exact gauge
  orbits is `C∞` and constant, so their pulled-back symmetric Hessian is zero.
  Differentiating
  first in an exact-gauge direction and then in an arbitrary potential
  direction certifies the zero exact-gauge--potential kernel; differentiating
  first in a logarithmic-conformal metric direction and then in an arbitrary
  potential direction likewise gives a zero mixed block.
  `P0EFTJanusMappingTorusFrameFreeMaxwellPotentialHessian4D` now polarizes the
  same global pairing into an integrable symmetric `LinearMap.BilinForm` on
  arbitrary smooth potential directions at fixed metric. The action has an
  exact quadratic affine-line expansion, its second line derivative and
  two-parameter mixed derivative equal that Hessian, and exact gauge
  directions lie in both kernels. The arbitrary-metric--potential block,
  general metric/field-space Fréchet dependence, Candidate-A
  interaction/chart/core/Jacobi/Fredholm identification remain open. At fixed metric,
  the affine scalar line now has an
  exact pointwise/integrated
  quadratic expansion and action `HasDerivAt` under the explicit integrability
  contract for its three coefficients. Its first variation is PT-covariant
  pointwise and after integration, with exact iff integrability transport.
  For an arbitrary smooth D8 self-diffeomorphism, the same density and measured
  action are covariant under simultaneous metric, scalar, tangent-family and
  inverse-pushforward measure transport, including iff integrability and the
  direct two-sector exchange corollary. Tangent/Hom-bundle coordinates now
  construct the smooth tensor pullback for every such diffeomorphism; the true
  derivative transports its musical equivalence and Lorentz signature, so the
  metric pullback certificate is unconditional. On a supplied smooth orbit with such certificates at
  every parameter, finite invariance makes the action orbit constant with zero
  derivative; under the explicit non-vacuous first-variation contract this is
  exactly the scalar diffeomorphism Noether pairing, hence it vanishes.
  The jointly analytic D8 time action now also produces its genuine smooth
  tangent ghost, proved equal to the velocity of the complete flow. Restricting
  parameters to this real Lie-algebra line together with the existing
  `U(1)^2` pair gives a combined metric--matter--gauge `R`, its
  `B = E ∘ R`, the exact vanishing criterion and the infinitesimal Noether
  identity for the true time subgroup. This is not an arbitrary-ghost result:
  for arbitrary metric pairs, smooth symmetric global realization of the two
  metric derivatives remains an explicit `TimeTranslationMetricPairContract`.
  For the equal canonical intrinsic pair, finite time-translation isometry
  makes both metric generators zero and discharges that contract
  unconditionally. The specialized Noether identity still assumes the stated
  first variation and action invariance; no LL block is included.
  For the scalar-field variation, the genuine metric gradient is now
  `sharp(dφ)` and symmetry reduces the kinetic coefficient to
  `dψ(sharp(dφ))`. Under the explicit divergence/boundary-flux interface and
  its three integrability clauses, the first variation is exactly the weak
  covariant Euler pairing plus flux; zero flux makes stationarity equivalent
  to the weak equation, a pointwise Euler solution implies it, and the action
  derivative vanishes. This is specialized to the intrinsic D8 metric.
  Separately, a covariant scalar second jet in a four-dimensional normal frame
  now satisfies the exact algebraic identity
  `∇_μ T^{μν} = (□φ - V'(φ)) sharp(dφ)^ν`, hence zero divergence at that jet
  under its Euler residual. Both the intrinsic-fiber convention
  `V' = -m²φ` and the matrix-stress convention `V' = m²φ + source` are matched
  to their existing stress tensors. The calculation is now transported to
  arbitrary local coordinates under a pointwise metric-compatible,
  torsion-free connection-jet interface. Its covariant Hessian is symmetric;
  an explicit realization of `∇T = ∂T + ΓT + ΓT` cancels the Christoffel
  corrections and yields the same Euler identity and conservation. That
  interface is now discharged pointwise from every symmetric nondegenerate
  metric and metric-symmetric first jet by the local Levi-Civita formula,
  including the exact derivative `∂g⁻¹ = -g⁻¹(∂g)g⁻¹`, torsion freedom and both
  covariant- and inverse-metric compatibility equations. On every supplied
  smooth holonomic quotient patch, a genuine `SmoothGeneralLorentzMetric` now
  produces a smooth nondegenerate local metric matrix, its smooth inverse and
  coordinate derivative, and smooth Christoffel coefficients. A genuine
  smooth quotient scalar pulls back to a `C∞` coordinate representative. Its
  gradient and raw Hessian are `C∞`, form an actual coordinate scalar jet and
  obey Schwarz symmetry. The covariant Hessian/jet, Euler residual, raised
  gradient and canonically realized local stress divergence are all `C∞`.
  Their exact identity is
  `div T = EulerResidual · raisedGradient`, hence conservation at every patch
  coordinate under Euler. For two supplied overlap representatives, equality
  of the metric first jet and scalar second jet now forces exact equality of
  Christoffel coefficients, covariant scalar jet, Euler residual, raised
  gradient and stress divergence. The true quotient transitions are now proved
  analytic, and rebased metric/scalar jet agreements obey exact
  reflexive/symmetric/transitive laws and force equality of every local output.
  Under the now-realized covering holonomic atlas these data glue globally,
  with `div_g T = EulerResidual · raisedGradient` and hence `div_g T = 0` under
  the local Euler equations. For the pointwise conservation conclusion, raw
  jet-array agreement is no longer needed: the bridge reduces to existence of
  one holonomic chart through each point. Componentwise total-ball
  diffeomorphisms now provide such a chart at every point and form an actual
  field-independent covering atlas. Consequently scalar Euler equations imply
  chartwise and quotient-pointwise vanishing of the local stress divergence.
  This does not introduce a separate abstract global covariant-derivative field.
  The canonical latitude collar now supplies its own exact intrinsic D8
  divergence/boundary interface. Pairing `sharp(dφ)` with the explicit collar
  normal is the genuine manifold directional derivative, and the oriented
  endpoint flux is exactly the proved interval-IPP boundary functional,
  fiberwise and after base integration. Euler fields with endpoint-Dirichlet
  test variations therefore have zero collar first variation. An exact
  specialization predicate and adapter connect this result to the global
  interface. The former four-dimensional Green--Stokes contract is now
  discharged on the canonical cut bulk: the global boundary functional is the
  concrete oriented tangent-normal flux. Dirichlet, PT-fixed and PT-projected
  sectors close it; the general formula retains the possibly nonzero oriented
  period explicitly.
  On the canonical latitude collar, the antisymmetric scalar
  Green--Wronskian current is now explicit. Its derivative is exactly the
  antisymmetric pairing of the equal-mass Euler residuals; it is pointwise and
  measured constant for two Euler solutions, its endpoint jump is the
  antisymmetrized IPP boundary functional, and homogeneous Dirichlet Euler
  solutions make it vanish. This Wronskian is now realized as a genuine
  quotient-tangent current along the canonical collar: its intrinsic normal
  is unit spacelike, its metric normal flux is exactly the Green current, the
  flux is locally conserved for equal-mass Euler pairs, and its throat value
  is the concrete pairing of the two normal `mvfderiv`s. The same
  one-dimensional equation also has the
  energy `(φ')² + m²φ²`: its derivative is exactly twice `φ'` times the Euler
  residual, so Euler solutions conserve it fiberwise and after base
  integration, with zero endpoint jump; it is nonnegative when `m² ≥ 0`.
  The intrinsic unit-normal covector identifies this energy exactly with twice
  the normal-normal component of the general scalar stress on the
  normal-projected collar jet; this component has zero derivative and is
  locally constant under the collar Euler equation. This is only a local
  collar stress-energy identity. The finite box, stratified and null-action
  boundary residuals now assemble into a canonical zero ledger. Under the two
  canonical divergence-free spanning frame, the continuous IPP is now proved
  directly and its zero boundary flux realizes that ledger. The global
  boundary package derives the required strong regularity from the smooth
  canonical frame, so LL weak/strong and stationary/strong equivalences carry
  no extra regularity assumption. Extending the collar
  current to a covariant four-dimensional Noether current remains open.
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
  The scalar analytic architecture must be read in two layers. Its aggregate
  import head validates the abstract closed-graph, Lagrangian-boundary,
  resolvent, Poisson/DtN, spectral and variational interfaces; its marker
  theorem does not instantiate their physical hypotheses. On the concrete
  canonical scalar side, coarea/value trace, smooth density and zero-Cauchy
  cutoffs, cut-bulk Green--Stokes with Dirichlet/PT closures, positive static
  coercivity/Fredholm theory, full graph-`H¹` Rellich compactness and the
  intrinsic coercive elliptic operator/action are unconditional. The general
  off-shell Lorentzian realization, its operator-specific coercive shift and
  its physical Poisson uniqueness remain conditional.
  PT/exchange additionally acts on the complete current independent-field
  package and all its componentwise smooth throat boundary data, with exact
  trace equivariance and preservation of the full Dirichlet condition.
  The same result now holds after replacing the diagonal metric pair by two
  arbitrary smooth general Lorentz metrics: the unified packet has an exact
  involutive PT/exchange, and every retained non-metric boundary sector has
  equivariant trace and stable Dirichlet data. Each general metric now also
  restricts to a genuine smooth symmetric throat tensor, and the complete
  boundary packet carries both metric traces. Their nondegeneracy is exactly
  equivalent to absence of a tangential radical. Restriction now commutes
  pointwise with intrinsic PT tensor pullback, including the exact two-sector
  exchange law. The throat PT derivative is a linear equivalence, so this
  pointwise pullback preserves and reflects nondegeneracy; consequently the
  no-tangential-radical condition is invariant under PT and PT/exchange. A
  smooth intrinsic PT-pullback construction for an arbitrary throat tensor and
  classification of general metric restrictions remain open. Without
  postulating that missing pullback, smooth metric
  boundary references now carry a pointwise PT/exchange matching relation
  that is functional, preserves nondegeneracy and is realized by the actual
  ambient metric traces. Matched references transport the complete metric and
  non-metric Dirichlet equality exactly.
  For the retained intrinsic metric the stronger fixed-point result is now
  unconditional: the public time-reversal naturality of the cover immersion
  derivative proves cover isometry, projection naturality and equality of the
  PT-pulled quotient descent by uniqueness. The full metric with its musical,
  the equal two-sector pair and its smooth nondegenerate throat trace are PT
  fixed.
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
  covariance are unconditional. The model is now coupled to the actual smooth
  strictly-positive diagonal metric cone by its eight logarithms, with metric
  ghosts, antifields, corrected square-zero BRST, nonzero integrated action,
  pointwise/integrated CME and exact PT covariance. A separate first-level
  general-tensor BV layer now contains two smooth symmetric metric variations
  and their antifields, a nontrivial odd square-zero doublet, the background-
  raised trace pairing and a graded-skew pointwise Darboux antibracket, attached
  to the general-Lorentz independent packet. Its analytic PT pullback with
  sector exchange is an involution commuting with BRST; the raised pairing and
  odd bracket are exactly PT/exchange covariant pointwise. This bulk pairing now
  defines the general-tensor ultralocal master Hamiltonian
  `1/2 ⟨h⁺,h⁺⟩`: exact affine expansion and actual `HasDerivAt`, declared
  antifield gradient, generation of `(h⁺,0)`, intrinsic action-`4` nonzero
  witness, PT/exchange covariance and pointwise CME. Local tangent/cotangent
  trivializations, smooth finite-dimensional inversion of the musical matrix
  and trace invariance now prove every smooth bulk pairing density continuous.
  Hence all pairing `L¹` obligations are discharged: action/bracket
  integrability, the affine expansion and integrated `HasDerivAt`/gradient are
  unconditional, while measure-preserving PT covariance and the represented
  integrated CME remain exact. Certified bulk functional observables now carry
  actual gradients and a functional odd bracket. The rank-one nonlocal master
  `1/2 (∫⟨K,h⁺⟩)²` has its exact affine derivative, functional CME, generated
  square-zero BRST and an intrinsic nonzero witness. Derivative-dependent
  kernels, completed spaces and arbitrary functionals remain open. Both variations and
  antifields now have a genuine smooth trace through the actual throat
  inclusion. The boundary doublet squares to zero, restriction commutes with
  BRST, and the traces obey exact PT/exchange matching; the metric-extended
  boundary packet therefore transports its complete Dirichlet condition.
  Packet-level pointwise odd-bracket covariance is retained under the same
  exchange. For the retained PT-fixed nondegenerate intrinsic throat metric,
  equal tangent/cotangent rank now supplies a genuine pointwise musical inverse.
  It raises the traced variations and antifields, defines their symmetric
  intrinsic pairing and graded-skew odd bracket, and gives an exact expansion
  in the bulk-gradient traces. The pairing and bracket are PT/sector-exchange
  covariant. The pairing is genuinely bilinear, and the ultralocal pointwise
  action `S∂ = 1/2 ⟨h⁺,h⁺⟩` has an exact quadratic expansion on every affine
  smooth throat-antifield line. Its actual `HasDerivAt` is the pairing with the
  declared `antifieldGradient`; the intrinsic metric in both sectors is an
  explicit witness with action `3 ≠ 0`. The action generates the boundary
  doublet `(h⁺,0)`, is PT/exchange covariant and satisfies its pointwise CME.
  Local tangent/cotangent trivializations now identify the inverse pairing with
  continuous finite-dimensional matrix inversion and trace. Thus every smooth
  throat-tensor pairing density is globally continuous, the continuity contract
  and all required `L¹` obligations are discharged, and the canonical throat
  action and represented odd bracket are integrable without extra hypotheses.
  Their quadratic line expansion and true `HasDerivAt` equal to the integrated
  `antifieldGradient` pairing are unconditional; PT/exchange covariance and the
  represented integrated CME remain exact. On the same throat space, certified
  functional observables and their odd bracket now yield the analogous
  rank-one nonlocal master, with exact derivative, functional CME, generated
  square-zero BRST and a nonzero intrinsic throat witness. Derivative-dependent
  kernels, completed spaces, arbitrary functionals, inverse/classification for
  arbitrary general throat restrictions and Lorentzian preservation of affine
  variations remain open.
  Independently, real translation of the
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
  nontrivial. Integration of an arbitrary ghost remains open. An intrinsic
  positive fixed-patch energy replacement is also uniformly equivalent to the
  implemented localized graph density and gives unconditional uniform graph
  ellipticity. A fixed-atlas holonomic `ℓ²` jet is now exactly linearly
  equivalent to the finite graph jet, with both density dominations proved.
  Equality with the historical variable-`chartAt` density remains open.
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
  diagonalizable locus. These results are now packaged as the unique global
  lift of the complete local IFT atlas on exactly that locus: it is continuous,
  squares to the target and agrees with every presented local branch. This
  does not extend the lift to Jordan strata, nonpositive spectra or the full
  physical admissible domain. The similarity-invariant index-two unipotent locus
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
  This regular selector now supplies a genuine pointwise IFT atlas: every
  positive split raw matrix lies in an explicit open target chart whose local
  root is continuous, squares exactly throughout the chart and has the inverse
  Sylvester derivative at its centre. Pairwise overlaps on which both roots
  remain in the crossed IFT uniqueness sources are open, and the two branches
  agree there exactly. This does not prove continuity of the classical centre
  selector, a global no-branch-jump choice, or gluing beyond those uniqueness
  neighbourhoods.
  One positive-to-zero Jordan frontier witness is now exact:
  `J₂(t) ⊕ 1 ⊕ 1` has the Hermite root with nilpotent coefficient
  `1/(2√t)` for `t>0`; its square is exact while that coefficient and the
  Frobenius norm diverge as `t→0⁺`. The target has a finite limit, but the
  selected root has no finite matrix limit or continuous extension, and the
  Sylvester mode `E₀₁` collapses with eigenvalue `2√t→0`. This closes only
  that canonical witness. The obstruction is now transported through every
  fixed real similarity, and the simultaneous two-parameter collision
  `J₂(t) ⊕ J₂(s)` has two linearly independent Sylvester modes collapsing at
  the `0/0` corner while both nilpotent root coefficients diverge. One genuinely
  moving polynomial shear `P(t)=I+tE₂₀` is now exact too: its inverse,
  transported square and mode, nonconstant target, divergent root coefficient
  and absence of finite continuation are all proved. The singular diagonal
  scaling `P(t)=diag(t,1,1,1)` instead regularizes the canonical divergence to
  a finite nonzero nilpotent root limit; its inverse blows up and the Sylvester
  mode degenerates. Two explicit Jordan-type-change paths are also exact:
  `I+tE₀₁ → I` has a smooth affine root and constant Sylvester eigenvalue `2`,
  while `t(I+E₀₁) → 0` has both root and Sylvester eigenvalue tending to zero.
  These diagonal, canonical, fixed-similarity, moving-shear, double-collision,
  singular-frame and type-change witnesses are now packaged in one
  proof-carrying retained frontier certificate.
  At one diagonal `0/0` boundary point, the equal-rate and
  quadratic-numerator paths now reach the same boundary while the selected
  root coordinate tends respectively to `1` and `0`. This rules out a
  continuous single-valued extension agreeing with the positive interior
  branch. It is exactly a two-path obstruction, not a classification of
  arbitrary matrix paths or Jordan strata.
  The whole positive monomial family `(t^m,t^n)`, `m,n>0`, is now classified:
  the selected root tends to `1` for equal exponents, to `0` when the numerator
  vanishes faster, and to `+∞` when the denominator vanishes faster. This does
  not cover arbitrary nonlinear, matrix-valued or Jordan-degenerate paths.
  Arbitrary singular frames, a general Jordan-type classification/branch atlas
  and arbitrary matrix paths remain open.
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
  general symmetric D9 perturbations. Independently, six local symmetric
  metric coefficients now project surjectively onto the full D9 metric slot at
  fixed non-metric data; they are pointwise local data, not a tangent to the
  global Program-P action. Given a supplied smooth symmetric global tensor, a
  supplied holonomic chart and coordinate/throat compatibility, the six chart
  coefficients are now `ContDiff` and fill that D9 metric slot exactly. The
  total atlas now selects such a compatible chart automatically at every true
  throat point, removing that caller-supplied certificate. The bridge still
  does not prove that the tensor is a global Program-P action tangent. Literal
  finite D10 product modes use the same
  period, exact PT pairing and the existing heat regulator. A genuine
  smooth section of the D8 normal line now fills the D9 normal slot in every
  valid local bundle chart; one-loop transition is `-1` and equals the square
  of either `Z4` multiplier. The intrinsic latitude normal lift and its local
  tangent-trivialization coordinates are `C∞`; their explicit comparison with
  the older cover-product presentation is now integrated through
  `canonicalLatitudeNormal_presentations_compare`, while a single untwisted
  global scalar coordinate is excluded by the twisted normal topology. The
  genuine smooth tangent diffeomorphism ghost now fills its D9
  component in the same local package. A canonical real rank-four coordinate
  equivalence now fills its matter slot in the D11 squared-spinor coordinate
  specialization, closing that particular residual record at coefficient
  level. Separately, Program P now constructs the ambient twisted `PinC(4)`
  principal/spinor bundles, the D9 smooth spinor bundle and section spaces, and
  the complete primitive SpinC geometric signed tower. Every signed label has
  a genuine smooth first-order eigensection; Fourier--monopole completeness
  promotes the orthonormal synthesis to a unitary onto the independent
  geometric `L²` completion. The orientation-correct zero-mode relabeling makes
  this unitary intertwine the geometric `2D + m²` Hessian model with its exact
  self-adjoint Fredholm coefficient multiplier on the finite spectral core.
  Candidate-A matter now uses this primitive bundle and has the same graph
  action/Hessian on the finite core. What remains is the global gauge-fixed
  tangent-to-chart map, its extension beyond that core, common
  diffeomorphism invariance and action/Hessian/domain agreement for the other
  blocks. For every supplied differentiable
  nonlinear diffeomorphism generator, linearized Noether now gives the exact
  identity `H(v,G)+E(DG·v)=0`; at a critical configuration this makes `G` a
  left and right Hessian-kernel direction, also after pullback to the genuine
  smooth global tangent through any supplied dense chart bridge. The span of
  all such differentiable generators is now itself a two-sided kernel, and
  the Hessian descends exactly through both its quotient and the quotient by
  its sum with the physical `U(1)²` directions.
  The global LL action now has an exact simultaneous measure/flux cubic
  expansion and integrated derivative for every finite measure. Its algebraic
  Euler system is equivalent to the zero-flux branch. PT pullback is an exact
  involution and preserves its density, action, variation, Euler coefficients
  and stationarity for PT-invariant measures. The auxiliary LL metric has
  identically zero response in this selected algebraic action. Separately, for
  the differential PT-symmetric LL functional, the canonical throat
  volume is now unconditionally positive on nonempty opens and therefore has
  full support. A pointwise frame-divergence Euler field, weak/strong
  equivalence and stationary/strong equivalence are proved conditionally on
  the analytic realization. The finite boundary ledgers are now exactly zero;
  the four canonical measure-preserving generators prove the genuine raw and
  PT-averaged global IPP and realize the empty ledger unconditionally. General
  stratified Stokes and the complete covariant LL parent remain open. The
  exact formal-adjoint defect interface remains available for other frames;
  for the retained canonical frame the proved raw IPP makes its correction
  exactly zero.
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
- **P-C:** finite quadratic and polynomial Helmholtz reconstruction is formalized, including the exact three-sector PT-plus-reciprocity criterion. For the finite quadratic Euler family, self-adjointness of the actual Jacobian is equivalent to the coefficient Helmholtz swaps; these data construct a normalized cubic polynomial primitive with the prescribed actual Fréchet derivative, and derivative equality alone recovers its formal coefficients. A Poincaré--Helmholtz theorem reconstructs an action from a symmetric differentiable Euler one-form on an open convex configuration domain; on the whole space, under a global actual-gradient hypothesis, additive linear gauge invariance is equivalent to Euler horizontality. More generally, for a supplied complete differentiable one-parameter flow, full-orbit invariance is equivalent to annihilation of its field-dependent generator by the actual Euler derivative; horizontal Helmholtz data give an invariant normalized radial primitive. The exact Candidate-A action now instantiates this chain on every regular common `C²` variational chart: actual Euler derivative, symmetric Jacobian, normalized radial reconstruction, paired physical `U(1)²` Noether orbit and global functional null-classification. On a supplied genuine overlap, the Euler covector now obeys its exact derivative transition law; identity, composition and chart-independence of criticality are compiled. Constructing these overlaps for a normed atlas of every raw global tangent, the componentwise local PDE/diffeomorphism system and the full local jet variational bicomplex remain stronger open targets.
- The exact global Euler one-form is now proved equal, pointwise and in every
  direction, to the sum of the Fréchet derivatives of all nine assembled action
  blocks. Extracting their local tensor PDE representatives remains open.
- Given a linear identification with the actual D10-free physical tangent,
  Euler vanishing is now exactly equivalent to its non-SpinC bulk and primitive
  SpinC-matter component equations; both are evaluated as the sum of the nine
  exact action-block derivatives on pure sector variations. Constructing that
  identification from a normed raw-field atlas remains open.
- The same physical two-sector split is now connected to the local variational
  atlas: its descended `IsEulerCritical` predicate is equivalent to the bulk
  and SpinC equations in any represented chart carrying the algebraic tangent
  identification. At each admissible local point, both components are also
  identified with the exact nine-block Fréchet derivative sum.
- A first atlas inhabitant is now concrete rather than supplied: the injective
  finite SpinC-matter graph chart defines a singleton atlas on its physical
  image, and descended criticality is exactly its closed graph Euler equation.
- The null-normalization chart gives a second concrete atlas. Distinct
  representatives of its singleton physical carrier are joined by explicit
  affine transitions; its exact action is constant and its Euler covector
  vanishes in every normalization representation.
- The combined finite-matter/null-normalization chart now has a concrete atlas
  on the matter image with affine boundary fibers. Its descended criticality is
  independent of the normalization representative and equivalent exactly to
  the finite matter graph Euler equation.
- Every admissible local chart injective on its domain now canonically yields
  an atlas on its physical image. This promotes the corrected D10-free
  minimal-physical chart to an atlas and covers its base configuration once
  injectivity of the supplied field parametrization is proved; that geometric
  injectivity remains open rather than being hidden in the analytic chart data.
  At that base, descended criticality is exactly the local minimal-physical
  Euler equation.
- This remaining injectivity now has a constructive interface: a decoder from
  represented global fields back to admissible chart coordinates, with an
  exact recovery law, automatically proves injectivity and builds the same
  atlas. Constructing that decoder for the raw metric/gauge/LL fields remains
  the geometric task.
- The corrected minimal tangent itself now has a canonical product
  decomposition into a bulk kernel with the obsolete coefficient
  ghost/auxiliary directions removed and primitive SpinC matter. Consequently
  the minimal-chart Euler equation, and the retractive-atlas criticality at its
  base, are exactly the vanishing of these two sector covectors; no equivalence
  with the obsolete larger physical tangent is assumed.
- The corrected bulk kernel is now explicitly linearly equivalent to its seven
  free field families: full metric perturbation, paired Abelian gauge field,
  normal displacement, diffeomorphism ghost and the three LL fields. Its Euler
  covector vanishes exactly when all seven restrictions vanish. Together with
  primitive SpinC matter this gives an exact eight-sector formulation of local
  Euler vanishing and retractive-atlas criticality at the base.
- The seven-coordinate bulk packet and primitive SpinC variations now have
  explicit linear transports into the minimal chart. At every admissible
  point, both Euler evaluations equal the exact sum of the derivatives of all
  nine assembled action blocks. Every linear pure-component restriction of
  the seven bulk coordinates inherits this formula.
- These identities now form an exact weak field system: the nine-block
  derivative sum vanishes against every seven-field bulk test packet and every
  primitive SpinC test variation if and only if the local minimal Euler
  covector vanishes. At the covered base this is also equivalent to
  retractive-atlas criticality.
- The weak-to-strong frontier is now explicit: supplied bulk and SpinC PDE
  residuals must represent the two weak covectors and be separated by their
  test spaces. Under exactly these nondegeneracy data, vanishing of both
  residuals is equivalent to the nine-block weak system, local minimal Euler
  vanishing and retractive-atlas criticality. Concrete tensorial residuals and
  their separation proofs remain open; legacy scalar/LL operators are not
  silently identified with the current minimal sectors.
- The same frontier is also split into eight named residual obligations:
  metric, paired Abelian gauge, normal displacement, diffeomorphism ghost,
  auxiliary LL metric, LL measure, LL field and primitive SpinC matter. Their
  simultaneous strong equations are equivalent to the exact weak/local/atlas
  systems, while the concrete differential representatives remain explicit
  missing inhabitants.
- The seven pure bulk injections are now explicit, and each named bulk
  covector is proved to be the corresponding restriction. Consequently every
  supplied component residual pairing, including SpinC, equals the exact sum
  of all nine action-block derivatives along its transported pure variation.
- The residual interface has an unconditional canonical baseline: each of the
  eight covectors represents itself in its algebraic dual, separated by all
  tests. This concrete package is equivalent to the weak/local/atlas systems,
  but is explicitly not a tensorial differential representative; it isolates
  that analytic identification as the remaining strong-PDE task.
- The concrete finite SpinC atlas now goes further: its closed graph Hessian is
  a separating residual in the continuous dual, its evaluation is exactly the
  true Euler and nine-block derivative sum, and descended criticality is its
  vanishing. This is an actual finite-mode closure, not yet the full smooth
  SpinC differential operator.
- On that same finite SpinC core, the residual is now genuinely explicit in
  spectral coordinates: `(2D + m²)c`. Its Hilbert pairing is the exact graph
  Euler functional, separation is coefficientwise, and both chart Euler
  vanishing and descended criticality are equivalent to the diagonal mode
  equation. Extending this to the full smooth/distributional sector remains
  open.
- Its kernel is completely classified: a finite coefficient family is
  critical exactly when its support lies on the mass shell `(2D + m²)=0`.
  Off resonance the zero core is the unique critical point; any resonant mode
  gives an explicit nonzero critical core.
- The finite-support restriction is now removed for the closed graph action:
  the second graph component is the full maximal diagonal residual, its
  pairing with graph tests separates the ambient Hilbert field, and exact
  stationarity is equivalent to its vanishing. Off resonance the zero graph
  state is unique. Identification with the full coupled minimal chart and the
  other seven differential residuals remains open.
- Its full maximal kernel is also classified: a graph state is stationary
  exactly when its first component is supported on `(2D + m²)=0`, and every
  resonant mode yields an explicit nonzero stationary graph state.
- The complete three-slot LL graph now has an equally concrete strong
  equation: its existing bounded Riesz operator is a separating Hilbert
  residual for the genuine quadratic graph action, whose stationarity is
  exactly Riesz-residual vanishing. Coupled-chart identification and a
  pointwise three-operator decomposition remain open.
- The paired Abelian off-shell BRST graph is closed in the same strong sense:
  its bounded Riesz operator represents the exact graph Euler covector,
  separates tests, and vanishes exactly at stationary graph states. Its
  coupled minimal-chart identification remains open.
- The action-weighted diagonal diffeomorphism BRST graph now also has a
  separating strong Riesz residual. It vanishes exactly when the Frechet
  covector certified by the graph action's `HasFDerivAt` theorem vanishes;
  coupled minimal-chart identification is still open.
- These graph equations are now assembled into one faithful strong residual
  for the diagonal diffeomorphism BRST, paired Abelian BRST, SpinC and full LL
  same-action sum. Its Hilbert pairing separates the aggregate Euler covector.
  The seven physical action blocks are deliberately excluded, exactly as in
  the source faithful Riesz operator.
- The existing common-domain extension now upgrades that residual to the full
  augmented quadratic Candidate-A action, including all seven physical
  blocks. Its exact Frechet Euler covector vanishes iff the strong Riesz
  residual vanishes, and on the dense smooth core its pairing is the genuine
  local gauge-fixed Hessian. This remains conditional on supplied inhabitants
  of the same-action bridge and bounded seven-block extension. The latter is
  now constructed canonically from one aggregate norm estimate for the six
  non-Robin blocks, since the H10 Robin extension is already continuous.
  The six forms in that estimate are now fixed to the genuine Candidate-A
  chart Hessians; exact H10 Robin agreement and one graph-norm bound for the
  smooth core-to-chart map derive the estimate automatically. The Robin
  Hessian agreement itself is now derived from action-level H10 projection
  data, smooth-core projection agreement and transversality. Constructing
  that projection data remains necessary. The core-to-chart bound is no longer
  supplied separately: any bounded linear realization of the common Hilbert
  space in the chart that agrees on the smooth core yields it from its operator
  norm. The completed H10 boundary projection is likewise no longer supplied:
  it is the composite of the local projection with that realization. The
  remaining inputs are the continuous chart realization, local Robin action
  identification/base normalization, transversality, the chart/same-action
  bridge, and the nonlinear global chart Euler identification.
- Density of the typed smooth core now closes the weak--strong linearized
  equation: vanishing of the full local gauge-fixed Hessian against every
  smooth test is equivalent both to the augmented Riesz residual being zero
  and to the Frechet covector of the augmented quadratic action being zero.
  This does not identify the quadratic model with the nonlinear global Euler
  map away from the selected base chart.
- The exact nonlinear local action is now pulled back along any bounded affine
  realization of the common augmented Hilbert space. At every admissible
  state, its true Frechet derivative is the pulled Euler covector; the Riesz
  residual represents that covector and vanishes exactly at its critical
  points. The pulled action is also proved equal to the covariant action.
  On a genuine chart overlap, compatible bounded realizations now give the
  same action value, Euler covector, Riesz residual and stationarity equation.
  These data are now packaged as a residual atlas: one reference chart defines
  a global nonlinear action and residual on its Hilbert carrier, proved equal
  to every chart representative. Every bounded single-chart realization gives
  a compiled singleton inhabitant on its admissible preimage. A canonical
  multi-chart inhabitant covering the actual physical field space is still
  required for the terminal operator.
- The nonlinear Hilbert Euler map is now connected back to the certified local
  Hessian: its actual Frechet derivative is precisely the chart Hessian pulled
  through the bounded realization in both slots. The derivative of the strong
  nonlinear residual is its symmetric Riesz representative. This closes the
  nonlinear/linearized calculus bridge without assuming the missing bounded
  physical realization.
- On the dense smooth core, this nonlinear linearization is now identified
  with the genuine local covariant Hessian. The older augmented strong model
  is proved to equal it plus the explicit gauge-fixing Hessian, both in weak
  Hessian form and through the strong Riesz pairing. Equality without the
  correction is equivalent exactly to vanishing of that gauge-fixing form;
  no gauge dynamics is silently removed.
- For a complete local chart model, the existing dense-core graph-norm bound
  now constructs the bounded Hilbert-to-chart realization by the canonical
  `extendOfNorm` operation. Its smooth-core agreement and operator-norm bound
  are proved; density also makes it the unique continuous realization with
  those core values. It supplies the nonlinear singleton residual atlas and the
  covariant linearization theorem without a separately postulated realization.
  Completeness and the actual graph-norm estimate remain the honest inputs.
  On the concrete minimal physical chart, the previously isolated continuous
  linear equivalence from the common graph Hilbert space now supplies the
  bounded realization and its core estimate automatically. It directly gives
  the nonlinear singleton residual atlas and its covariant smooth-core
  linearization. The remaining analytic input on this route is construction
  of that Hilbert equivalence itself; multi-chart physical coverage is still
  open.
  The older minimal-Hilbert H11 adapter and its constructive H14 consumer were
  also repaired, compiled in isolation and integrated into the main facade;
  they now use this same typed common-Hilbert chart contract instead of
  incompatible duplicate norm instances.
  A supplied covering variational atlas now descends local Euler vanishing to a
  well-defined predicate on its physical carrier, equivalent to the equation in
  every chart representation. The concrete construction of that atlas from all
  raw global tangents remains open.
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
  For a general Lorentz musical metric, the intrinsic contravariant scalar
  stress is now defined fiberwise and proved pointwise covariant under every
  smooth D8 diffeomorphism, with simultaneous transport of `d phi` and both
  cotangent test arguments. Pairing it with two dependent cotangent tests and
  integrating against an arbitrary Borel measure preserves integrability iff
  and is invariant under simultaneous diffeomorphism and sector exchange.
  One unconditional certificate now packages this pointwise covariance,
  measured covariance, two-sector exchange and integrated stress-variation
  exchange. A separate normal-frame second-jet calculation proves the local
  identity `div T = (□φ - V'(φ)) sharp(dφ)` and Euler conservation for both
  retained potential conventions. A metric-compatible torsion-free coordinate
  connection-jet interface transports it to arbitrary coordinates and realizes
  the full Christoffel-corrected derivative. The interface is now realized
  algebraically by the local Levi-Civita coefficients and exact differentiated
  inverse for any symmetric nondegenerate metric first jet. On every supplied
  smooth holonomic quotient patch, the genuine Lorentz metric now realizes
  these data as smooth local metric, inverse, derivative and Christoffel
  coefficient fields. A genuine smooth quotient scalar pulls back to a `C∞`
  representative; its gradient, raw and covariant Hessians, Euler residual,
  raised gradient and canonically realized stress divergence are `C∞`. Schwarz
  supplies Hessian symmetry, and the exact identity
  `div T = EulerResidual · raisedGradient` gives local Euler conservation.
  Equality of the metric first and scalar second jets on supplied overlap
  representatives now gives equality of all these local outputs. The analytic
  quotient transitions and their rebased jet-agreement algebra are closed.
  Under a single explicit covering-atlas bridge, the local data glue and satisfy
  global `div_g T = EulerResidual · raisedGradient`, hence global conservation
  under Euler. Constructing that bridge from actual holonomic patches remains
  open.
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
  an explicit integrability contract. Under the exact intrinsic
  divergence/boundary-flux interface, this variation equals the weak covariant
  Euler pairing plus flux, with stationarity equivalence at zero flux and an
  intrinsic D8 specialization. The concrete throat flux
  `trace(ψ) · dφ(n)` equals `trace(ψ) · g(sharp(dφ), n)` and vanishes pointwise
  and integrally for homogeneous Dirichlet variations. On the canonical
  latitude collar, genuine interval-integral IPP identifies the inner term
  with `mvfderiv` on the canonical normal and proves the measured weak IPP
  without boundary for endpoint-Dirichlet variations. Its explicit
  Green--Wronskian current has exact Euler-residual derivative, pointwise and
  measured constancy for equal-mass solutions, the expected antisymmetric
  endpoint jump, and zero Dirichlet current. It is now a genuine tangent
  current along the quotient collar, carried by the intrinsic unit-spacelike
  canonical normal; its metric normal flux is exactly the Wronskian, is locally
  conserved on Euler pairs and at the throat is the concrete normal-`mvfderiv`
  pairing. Its scalar energy
  `(φ')² + m²φ²` has derivative `2φ'` times the Euler residual, is fiberwise
  and measured constant on Euler solutions, has zero endpoint jump, and is
  nonnegative for `m² ≥ 0`. It is exactly twice the general scalar stress
  component `T_nn` evaluated on the normal-projected collar jet, and `T_nn` is
  locally constant under the collar Euler equation. This remains only a local
  collar stress-energy result. Globally, the canonical cut bulk is now a
  `C∞` manifold with boundary, with smooth descended Green current, intrinsic
  Lorentz metric/volume, genuine normal divergence and the exact oriented
  measured Green--Stokes formula. Under the full Euler equations its only
  residual is the two-sheet oriented flux period. That period vanishes, and
  Stokes closes, in the proved Dirichlet, PT-fixed and PT-projected sectors; a
  universal zero-flux statement outside those sectors is false, as witnessed
  by the formalized massless Wronskian counterexample. The global boundary
  package identifies every non-null face with the true Gaussian throat,
  includes finite explicit null faces/joints and proves the EH, scalar and LL
  residual sum to zero on the PT-fixed or Dirichlet physical sector. Its
  canonical divergence-free frame discharges LL regularity, IPP and
  flux realization, hence weak/strong equivalence. Extension to a
  covariant four-dimensional Noether current and a global unit normal for every
  admitted general metric remain open; the intrinsic canonical latitude normal
  itself is already constructed;
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
  the compact-throat algebraic and differential LL actions are actual
  integrals, with canonical-frame weak/strong equations, IPP, Hessian/Jacobi
  and Fredholm realization. The global boundary completion ties non-null faces
  to the true Gaussian throat, admits finite explicit null faces/joints and
  closes EH, scalar and LL residuals on the PT/Dirichlet physical sector.
  Arbitrary general-metric/null ambient stratification and the gravitational
  bulk Euler equations remain open; the finite regular covariant action
  assembly itself is now constructed;
- **T/C** for every supplied finite null-generator family, one actual action
  now sums the integrated inaffinity density, the continuously extended
  expansion counterterm and the endpoint joints. Finite rescaling of the
  generator and inverse parameter measure gives the exact face transgression,
  cancelled by the oriented joints face by face and after finite summation.
  The value remains continuous at `Theta = 0`, while classical variation is
  restricted to `Theta != 0`. Ambient area/generator geometry and the sole
  `NullFaceIntervalIntegrability` contract remain supplied inputs;
- **T/N** additive translation of reduced scale variables is classified and
  fails for a concrete positive interaction; any relation to the covariant
  diagonal diffeomorphism still requires a separate bridge;
- **T/C** the reduced Candidate-A FLRW dust witness is promoted from one
  isolated rank calculation to an explicit affine family. The parameter locus
  where its exact `3 x 3` constraint minor is nonzero is open and nonempty,
  contains a neighbourhood of the witness, and carries three independent
  constraint covectors. This is only an open locus along the supplied reduced
  family; generic phase-space rank, covariant/ADM derivation and exclusion of
  the Boulware--Deser mode remain open;
- **O** general tensorial Lorentz square-root domain, metric Euler equations,
  ambient geometric realization of the finite GHY/null/joint models,
  Bianchi/constraint algebra, exact stability,
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
- the fixed-background D8 symmetry category with all smooth
  self-diffeomorphisms as arrows, plus the contravariant smooth-field functor
  and the actual contravariant general-Lorentz-metric pullback functor, both
  with exact identity/composition laws;
- the category of all effective D8 quotients with arbitrary nonzero period as
  objects and genuine smooth cross-background diffeomorphisms as arrows,
  together with its exact contravariant constant-fiber smooth-field functor,
  actual tangent bundles transported functorially by manifold derivatives and
  dual cotangent pullbacks satisfying identity/composition exactly; the same
  construction gives natural covariant rank-two tensor fibers and preserves
  their symmetric subspaces, promotes to genuine smooth symmetric-tensor
  sections, transports musical equivalences and Lorentz inertia, and yields a
  global contravariant functor of smooth general Lorentz metrics;
- any certified continuous ambient `Pin⁻(4)` Čech lift now canonically produces
  a genuine fiber-bundle core on the real 4D quotient, with free/transitive
  right action and exact equivariant chart changes; unconditional existence of
  that ambient lift remains separate;
- action-groupoid, orbit and stabilizer laws, with the regular isotropy stratum
  equal to every effective deck object, the singular stratum empty, and exact
  mutually inverse restriction/unique-extension maps for dependent sections;
- reconstruction of equivariant sections on one transitive orbit from isotropy-fixed values;
- a concrete valid-chart low-order residual/SpinC action-groupoid realization;
- the need for separate compatibility across isotropy strata.

The operator category is not an ordinary category of fixed linear
representations with plain fiber maps. The nonzero-period effective family is
not yet the decorated moduli category of all Janus geometries or a
smooth/derived stack, and the trivial deck isotropy does not classify
additional SpinC-fiber isotropy.

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
smooth quotient structure are not proved by those abstract lemmas alone.
`KJ-GLOBAL-01/02` are now closed on their stated physical scope. `K_Gram`,
`DK_Gram`, `R` and abelian `B_Noether` live on the actual quotient;
`K_SV` is the true Levi--Civita curvature on the total holonomic atlas and
`B_Bianchi` its covariant cyclic derivative, including curvature/connection
terms and satisfying `B_Bianchi ∘ K_SV = 0` at every physical point. The
actual `U(1)²` differential is faithfully embedded in canonical physical
`L²`; its kernel is exactly the global constants `H⁰ ≃ ℝ²`, its quotient is
linearly equivalent to the exact range, and the range closure is complete.
The paired gauge sector used by the common global field package has the same
result componentwise, with kernel linearly equivalent to
`GaugeLieAlgebra × GaugeLieAlgebra`.
The completed `ℤ⁴` Saint--Venant model remains an explicitly separate
principal-symbol certificate. No global curved Calabi exactness
`ker B = im K` is claimed; that stronger linearized elliptic/Fredholm question
belongs to `HESSIAN-GLOBAL-01`.

The global naturality block is closed: the effective-D8 category, descended
holonomic jets, genuine `Pin⁻`/`PinC` bundles and exact finite six-invariant
EFT coefficient classifier are assembled without new hypotheses. The regular
Candidate-A action is also assembled from two Einstein--Hilbert terms,
interaction, primitive SpinC Dirac-plus-mass matter, two Maxwell sectors, LL,
GHY, finite null faces/counterterms and joints. Its chartwise actual Euler,
nonlinear Helmholtz reconstruction, paired physical `U(1)²` Noether identity
and global functional variational cohomology are now closed. The actual
chartwise Hessian is symmetric. Its D7/D9 tangent algebra,
independent-field retraction, local field assembly and boundary pullback are
now packaged in an unconditional certificate. The genuine physical tangent
has no D10 coordinate. A legacy extended tangent adds it as a split factor
(surjective projection with injective zero-D10 section) for spectral regulator
and determinant work only. For every certified chartwise paired
`U(1)²` symmetry, differentiating the exact Noether identity now proves that
the genuine Hessian kills its gauge directions in both arguments without a
critical-point hypothesis; its algebraic quotient is exact, symmetric and
unique. A concrete D10-free physical domain is constructed for bulk
Dirichlet, sectorwise SpinC and LL; the extended analytic product additionally
contains D10.
The complete all-level SpinC **coefficient** tower now carries the actual
period, both normal roots and both signed first-order branches. Its square is
exactly the previous geometric `D²` spectrum. Its first-order weight is
proved proper, so every geometric Hessian-model shift `2D + m²` has only finitely many resonant
zero modes and defines a dense self-adjoint Fredholm maximal operator over
both `Complex` and its underlying `Real` Hilbert space. The complete squared
SpinC maximal domain is now unitarily reindexed as the missing zero tower plus
the positive D10 domain; this conjugates the unbounded operators exactly and
preserves graph energy. D10 remains bijective Fredholm. The LL Riesz identity
is now appended on the completed positive
energy space with the same canonical divergence-free frame as the unchanged
global LL action; its smooth pairing is exactly that action's mixed Hessian.
The native real `ℓ²` inner product is proved equal to the real part of the
complex pairing, so the enlarged operator is densely defined, self-adjoint
and Fredholm without an instance-coherence assumption. The D9
gauge–ghost symbol defines its maximal, generally unbounded `ℓ²` multiplier
with no upper symbol bound. A positive lower gap away from finitely many
characteristic modes proves density, self-adjointness and closedness; the
maximal-domain operator itself has closed range and finite kernel and
cokernel. The corrected D10-free spectral target assembles D9 and two sector
copies of signed `2D + couplings.matterMassSquared`; its LL enlargement adds
only `llField`. The older squared SpinC assembly remains only an
elliptic-control operator, and the historical D10-extended first-order target
is regulator-only. Density, self-adjointness, closed range and finite
kernel/cokernel are proved for this reduced target, not for the omitted
physical blocks. The exact linear-gauge interface
now combines `U(1)²` with a genuine smooth-diffeomorphism symmetry certificate
and automatically gives the total quotient and two-sided Hessian degeneracy.
For the genuine nonlinear-flow interface, the analogous flow-only and
combined quotients are now exact at critical configurations under explicit
generator-differentiability assumptions.
The BRST frontier also contains the exterior scalar graded derivation, its
two-ghost cancellation, the linearized diffeomorphism differential, the
corrected full linear/LL complex and the general-metric BV doublet.

The irreducible Hessian frontier is therefore narrower. The D10 mismatch is
resolved by a D10-free physical tangent/target, and Candidate-A matter now
uses the primitive SpinC smooth sections directly. Its graph action has exact
second Fréchet derivative `2D + m²`, is Fredholm, and agrees with the smooth
action on the finite spectral core. Typed D9 nonminimal gauge fermions add
distinct ghost/antighost/NL fields and the right FP symbols locally. The nine
corresponding smooth global species (two sector-indexed `U(1)^2` triples and
one tangent-vector triple) and their square-zero universal
nonminimal differential are now installed as real modules, with linear
physical/nonminimal projections, without changing the physical configuration.
The corrected gauge-fixed tangent holds the legacy coefficient ghost and
auxiliary directions fixed, preventing a duplicate nonminimal multiplicity;
the paired physical rule `sA = -dc` is now global and square-zero. Its
finite-measure `sΨ` uses the true `δ_g d` and is attached to the actual
  Candidate-A metrics, Maxwell potentials and typed nonminimal fields. The
  physical metric-plus-Abelian gauge subchart now consumes the completed de
  Donder and Lorenz features and embeds in the typed tangent with the
  nonminimal coordinates fixed. The full typed chart and the diffeomorphism
  rule `sg` remain separate. The global smooth Abelian Lorenz codifferential is
now linear and transition-independent for every supplied general metric; its
actual Faddeev--Popov composite is `δ_g d` and is the chartwise covariant wave.
The canonical specialization has exact `δ(d c)=+□c`. Componentwise, it is now
identified pointwise and in physical `L²` with the canonical mass-zero scalar
Euler operator. Its adjunction defect is exactly the established scalar
skew-density integral, and symmetry for each pair of smooth ghosts is
equivalent to that integral vanishing. Given the already isolated unrestricted
scalar Green--Stokes datum, the FP defect is now identified with the exact
oriented cut-bulk boundary current and formal symmetry follows on every
existing Green-isotropic smooth domain, with an explicit Dirichlet
specialization. This composition introduces no new hypothesis class. Once
that existing Green datum is supplied, the mass-zero scalar Green core is
exactly each FP component, its zero-Cauchy minimal core is dense by the
existing cutoff theorem, and its completed graph projection is injective. The
finite `Sector × Fin 2` product has a dense actual paired smooth core and a
single-valued ambient-range realization which agrees there with the true
paired FP map. The unconditional full 4D
`integral_eq_divergence`/Stokes theorem remains missing. The existing completed
boundary triple now gives dense component domains and actual-adjoint-domain
equality conditionally on its supplied Lagrangian analytic-closure package;
the existing graph/direct-coercive endpoint further reduces this to its PDE
data, graph estimate and shifted coercivity, with unconditional Rellich and
exact smooth-core FP identification. A constructor audit found only implication
packages from those two analytic inputs, not an inhabitant. Homogeneous
Dirichlet data close the Green boundary term but do not supply ellipticity or
coercivity for the full Lorentzian wave: the proved negative time coefficient
separates it from the existing positive intrinsic `H¹` elliptic regulator.
No total-Hessian domain identification or general-metric adjoint compatible
with the intrinsic physical `L²` measure is proved.
The actual intrinsic potentials inject into the corrected minimal tangent.
Their Lorenz feature has a dense injective graph completion, and that Hilbert
graph now carries a displayed `C∞` quadratic action (hence `C²`) whose exact
second Fréchet derivative is its same-action symmetric Riesz form. On the
common smooth core this derivative is the reduced on-shell BRST polarization,
and the core injects simultaneously into the graph chart and the corrected
minimal tangent. The complete
`llAuxMetric × llMeasure × llField` Hessian has an analogous dense injective
graph realization and exact bounded symmetric Riesz representative, including
the two cross blocks. It is now proved self-adjoint. Its kernel is explicit,
and the generic self-adjoint Fredholm reduction makes finite cokernel automatic
once closed range and finite kernel are proved; those two estimates remain.
On shell, stationarity itself supplies `llField = 0`; the quotient
Fredholm criterion and index-zero corollary now follow directly from the
stationarity equations, without a separate zero-flux hypothesis. The
fixed canonical GHY control has its genuine zero same-action Hessian, whereas
the mobile sourced GHY summand retains its physical Hessian,
and the finite null-face action has zero second derivative along exact
generator reparametrizations.
For de Donder, `tr_g h`, the induced Levi-Civita derivative and its contracted
divergence are constructed with the full overlap laws. The divergence glues
through the canonical atlas to a smooth global one-form, and its sum with
`-1/2 d(tr_g h)` closes the complete smooth de Donder operator. It is now
  bundled as a linear map, and its smooth inverse-metric contraction gives an
  integrable symmetric bilinear form with exact quadratic polarization. Its
  finite-frame tensor, one-form and raised one-form coordinates define a
  faithful refined Hilbert graph with dense injective smooth range. The
  resulting bounded symmetric Hessian equals the original Lorentzian pairing
  on that core, and its quadratic action is `C∞`. Two metric copies and the
  closed Lorenz graph now assemble into a common physical gauge `C²` subchart;
  its exact second Fréchet derivative is their direct sum, and the same core
  injects into the corrected typed tangent with nonminimal coordinates zero.
  This gauge chart, the primitive SpinC matter graph and the complete LL graph
  now also assemble into one physical bulk graph product. Its quadratic action
  is `C∞` (hence `C²`), is exactly the sum of the three graph actions, and has
  exact first derivative and constant block-diagonal second Fréchet derivative
  equal to the three existing same-action forms. It is not yet identified with
  the pullback of the complete nonlinear covariant action.
  Its gauge-smooth × finite-SpinC × smooth-LL core embeds injectively and
  densely for the product graph norm. At the physical Candidate-A metric and
  mass, one injective linear map records both the graph point and its exact
  slots in `GlobalPhysicalFieldTangent`. This is a core-level attachment, not
  a map from the whole graph completion to smooth fields. The Abelian
  nonminimal core separately has its canonical-volume off-shell feature
  completion/action and typed attachment. That feature completion alone does
  not prove differential closability; the intrinsic FP Green-core adapter now
  does so conditionally on the existing unrestricted scalar Green datum. The
  extended bulk now performs the required nonduplicating
  replacement of the shared potential/Lorenz factor, with dense injective
  core, exact sector-sum second Fréchet and injective typed core map. For each
  supplied metric the true
  diffeomorphism FP map
  `c ↦ B_g(L_c g)` is now global and linear. The typed chart has one diagonal
  diffeomorphism triplet, while the old gauge Hessian is the sum of two
  separate de Donder squares; the scalar no-go proves that this sum cannot be
  preserved by one projection. The kinetic-adjoint bridge now derives instead
  the unique action-weighted condition
  `F = F₊/(2κ₊) + F₋/(2κ₋)`, constructs its global FP operator as the same
  weighted sum of the mono-metric FP maps, and proves spatial-symbol
  ellipticity when the total kinetic weight is nonzero.
  The selected condition is now incorporated into one shared two-metric/
  one-triplet off-shell BRST graph with square-zero differential, dense
  injective core, exact weighted-`sΨ` Hessian/Riesz/action and typed raccord.
  Replacing the two old de Donder factors by this graph in the nonduplicated
  Abelian/matter/LL product yields an injective dense bulk core, an exact `C²`
  assembled Hessian and an injective total graph/typed-core map. Its nested
  `WithLp 2` realization is a complete real Hilbert space, continuously
  equivalent to the maximum-norm chart, with a bounded self-adjoint Riesz
  representative of that exact Hessian. Normal and boundary factors remain
  absent from that bulk chart. This dense graph/typed core is already faithful;
  the historical spectral D9 coordinate `ι × Fin 8` remains a reduced
  Fredholm model rather than the multiplicity of the complete action fields.
  The genuine normal displacement generates a deck-equivariant
  collar family descending from the throat to the bulk quotient. It starts at
  the canonical inclusion, has the prescribed local normal-coordinate
  velocity and zero scalar acceleration. Every member is injective, and at
  every physical throat point its parameter curve is `C∞`. The scalar lift is
  now `C∞` on the cover and the descended map
  `(point,parameter) ↦ normalGraph parameter point` is jointly `C∞`. After
  transport along `normalGraph_zero`, its `mfderiv` at zero is exactly the
  canonical global orthogonal lift of the corresponding differential-normal
  class. The induced normal action and its same-action Hessian remain open.
  A null-boundary chart with an independent `Theta` coordinate and nonzero
  uncancelled coefficient must in addition be stratified: the unchanged
  `Theta log |Theta|` factor is not `C¹` at `Theta = 0`. This does not exclude
  constrained subcharts with a proved cancellation, notably the already
  closed exact reparametrization curves. On each regular stratum
  `Theta ≠ 0`, its pointwise same-action Hessian is now proved exactly:
  `(u,v) ↦ Theta⁻¹ u v`, multiplied by the existing fixed
  screen/gravitational coefficient. The integrated null chart remains open.
  Independently rescaling every face normalization is now assembled on the
  finite Euclidean Hilbert space `EuclideanSpace ℝ NullFace`. The exact
  `GHY + null-face/counterterm/joint` action is constant there, so its actual
  first and second Fréchet derivatives vanish and its bounded zero Riesz
  representative is self-adjoint. General null geometry is still open.
  What remains is to extend this assembled bulk construction to the full
  global `C²` covariant chart including normal and boundary directions,
common diffeomorphism invariance, differential Green/domain and elliptic
Fredholm identifications, general metric/normal/mixed Maxwell/null-boundary
Hessians, LL coercivity off-shell, correct modal multiplicities and their same-action
Fredholm direct sum. The exact Parseval/unitary
identification between the independent geometric and spectral SpinC
completions is now closed. Finite multiplicity blocks are isometric and
distinct circle modes in one sector are orthogonal across all levels, so the
two opposite sectors are also orthogonal for arbitrary levels and modes.
The rotation Casimir and invariant round-sphere measure now prove exact
orthogonality between distinct sphere levels at fixed sector and mode. The
normalized blocks along all three axes now assemble into one canonical
Hilbert-sum linear isometry. Its range is proved equal to the closed span of
the explicit blocks. Fourier--monopole uniform approximation in the signed
Hopf frame proves that this range contains the dense smooth geometric core;
hence the synthesis is surjective and gives the global geometric unitary.
Reindexing only the undoubled zero tower by its orientation-correct PT
involution gives the unitary in the exact individual labels of the Hessian.
It maps every coordinate vector to a genuine smooth Dirac eigensection.
Consequently the true differential expression `2D + m²` intertwines on every
finite Fourier--monopole packet with the same maximal diagonal multiplier
already proved self-adjoint and Fredholm. Its maximal domain and unbounded
operator are explicitly pulled back to geometric `L²`, with exact unitary
conjugacy. This closes the geometric/coefficient identification of the
primitive SpinC Hessian model. The Candidate-A matter type/action now uses
that primitive bundle directly, and its finite spectral core has the same
graph action and Hessian; only the final global chart identification remains.
A single
null-curve construction gives, for every `p`, exactly `2p+1` complex
homogeneous polynomials, proves their linear independence, ambient
harmonicity and positive spherical energy `p(p+1)`; no further level-by-level
construction from `p ≥ 4` is needed. Its null powers are now realized
directly as genuine smooth sections of the quotient SpinC bundle. The
uniform Dirac recurrence proves their exact geometric `D²` equation and
generates both signed first-order branches. These branches are now tied
directly to every positive/negative coefficient label at every positive
level, with the exact first-order eigenvalue. The undoubled zero tower is
also realized at first order for either sign of the period through the
orientation-correct PT mode reindexing. Thus every complete signed
coefficient label has a genuine smooth geometric eigensection. At each
positive block the two branch spans are disjoint and their sum is exactly
the scalar/Clifford-gradient seed block. Each complex branch span now also
has a canonical finite-dimensional geometric `L²` orthonormal basis, exact
Parseval isometry, closed image in the independent completion and exact
first-order Dirac intertwining. Their algebraic sum has its own orthonormal
Parseval isometry, closed completed image and exact `D²` intertwining.
Radial Clifford parity separates the scalar and gradient components of every
raw signed relation. It proves linear independence of each signed family,
hence the exact geometric finrank `2p+1` per sign and `2(2p+1)` for the full
block. Rotation integration by parts, the exact tangential Hopf pairing and
the null-power Casimir identity additionally prove that the gradient pairing
is exactly `p(p+1)` times the scalar pairing. The two opposite first-order
signs are therefore orthogonal in every fixed level/sector/circle block.
Strict growth of the spherical energy separates the `D²` eigenspaces, so all
positive levels at fixed
sector/circle mode are jointly complex-linearly independent. Their
finite-support synthesis is injective and satisfies the exact diagonal law
`D² S = S Λ`. Thus smooth restriction, the all-level Lichnerowicz input,
within-level multiplicity and inter-level linear separation are closed. Both
normal-root sectors and all circle modes are also jointly separated at
every arbitrary fixed positive level: doubling cover time reindexes the two
sectors as the odd/even integer Fourier modes. The two separation axes and
the Hopf zero tower are now combined: one canonically indexed finite-support
synthesis simultaneously ranges over every nonnegative sphere level, both
sectors, every circle mode and every multiplicity; it is injective and
exactly intertwines geometric `D²` with the complete diagonal coefficient
operator. Every complete coefficient label therefore has real and
intrinsic-imaginary smooth geometric representatives. Their actual finite
smooth span now carries the coefficient-induced Hilbert norm. Its analysis
is injective and dense in coefficient `L²`; its completion is canonically
unitary to that `L²`, and the transported maximal `H²` squared Dirac is
exactly conjugate, coercive and bijective. Thus spectral Hilbert
orthogonality/completeness and the finite analysis-map identification are
closed. Independently, the canonical throat volume and the descended doubled
Hermitian pairing now define a smooth, integrable, positive-definite complex
`L²` product on the whole primitive SpinC smooth core. This gives its own
Hilbert completion with dense smooth embedding, without coefficient
definitions or additional physical axioms. Inside every fixed
level/sector/circle block, geometric Gram--Schmidt now preserves the raw
null-power span and exact `D²` eigenvalue while giving a genuine Euclidean
linear isometry and Parseval identity. Reduction to the canonical
round-sphere/time fundamental domain and exact Fourier cancellation now prove
orthogonality between distinct circle modes in either fixed normal-root
sector, uniformly across sphere levels and multiplicities. The explicit Hopf
half-spinor planes also give pointwise and integrated orthogonality between
opposite sectors for arbitrary levels and modes. Rotation integration by
parts and the exact Casimir eigenvalue additionally prove orthogonality
between distinct sphere levels, for raw blocks, their spans and normalized
syntheses. Their completed Hilbert sum is now isometrically embedded with
closed range exactly equal to their joint closed span. The opposite signed
blocks at each fixed spectral label are exactly orthogonal by the global
gradient/Casimir identity. Signed packets carrying distinct
sector/circle/level labels are now orthogonal as well, including the
zero-versus-positive separation. The zero tower and every complete two-sign
positive block therefore assemble into one canonical signed Hilbert-sum
isometry. Fourier completeness, polynomial monopole approximation and exact
signed Hopf-frame reconstruction prove that its range is dense in the whole
independently defined geometric completion. Because that range is already
closed, the synthesis is surjective and yields an unconditional linear
isometric equivalence from global signed coefficients onto geometric `L²`.
The
`p = 1,2,3` packets remain concrete compatibility checks
of this generic construction. One must
also prove invariance of all nine action blocks under the same
smooth diffeomorphisms and identify the actual
bulk/metric–Maxwell–matter–ghost–boundary Hessian, excluding the now-closed
`llField` factor but including the action-degenerate LL measure slot and all
remaining nonspectral sectors, with the
constructed global elliptic Fredholm operator.
The earlier abstract all-smooth realization theorem now transports the
maximal domain and squared operator through this geometric unitary.
Arbitrary couplings cannot imply the last statement: the repository now
proves that a zero Hessian has no such Fredholm realization on an
infinite-dimensional completion. Nondegenerate elliptic coupling hypotheses
must be derived or stated explicitly. In the Lorentzian full-field setting,
this also requires an explicit analytic choice of elliptic gauge/continuation,
boundary realization and common domain; it cannot be hidden as a new physical
axiom. The intrinsic/spectral Dirac,
nonlinear-BRST layers, circle Quillen geometry and PT/inflow anomaly
cancellation remain explicitly scoped frontiers. The common nuclear reference
regulator is closed; agreement with the physical Hessian remains a Hessian
obligation. Scheme independence is separately blocked by a proved
finite-part/normalization no-go, not by a missing algebraic manipulation.
The fixed-throat metric tensors are now bundled as a real module, and their
canonical integrated intrinsic pairing defines a linear morphism from smooth
geometric antifields to the algebraic BRST dual. Its injectivity is now
equivalent to separation by the pairing; the concrete finite-frame smooth
positive dualizer proves this separation without diagonal definiteness. Its
coadjoint equivariance is equivalent to integrated skew-adjointness for any
supplied throat representation, which remains open. The unconditional realization and both exact
criteria are now fields of the nonlinear BRST certificate and of
`GlobalBRSTFrontier`. The global frontier now also embeds the complete
nonlinear certificate, the bulk geometric metric dual, the canonical
algebraic Maxwell coadjoint closure, and the conditional two-metric
coadjoint closure for every supplied metric Lie action. The separate
`canonicalTensorialCoadjointAntifieldBRSTCertificate4D` now instantiates that
algebraic closure with the concrete Maxwell and metric Cartan
representations. The bulk geometric bridge is instead parameterized by one supplied
representation and its integrated skew identity.
The existing finite smooth bulk tangent frame now assembles a genuine smooth
metric-dependent covariant dualizer. Its pointwise pairing is
`Σᵢⱼ h(vᵢ,vⱼ)²`; canonical full support promotes this to integrated
separation, so the bulk geometric antifield realization is injective.
Bulk coadjoint equivariance still requires integrated skew-adjointness.
For genuine throat tensors, bilinear separation and integrated
skew-adjointness now construct the faithful geometric coadjoint bridge
directly through a `GlobalBRSTFrontier` gate. An explicit nonzero symmetric
Lorentzian tensor with nilpotent raised endomorphism has zero quadratic trace,
so diagonal definiteness is formally ruled out as a generic route; it remains
only a stronger conditional lemma. The same explicit Lorentz model now proves
that the bilinear trace pairing nevertheless separates every symmetric
covariant tensor. This algebraic audit is embedded in `GlobalBRSTFrontier`.
A smooth positive dualizer closes the entire globalization step:
continuity, compactness and the canonical full-support measure imply
integrated separation and injectivity of the geometric antifield realization.
Together with a supplied integrated skew identity it yields the faithful
coadjoint bridge. Its geometric construction from the smooth inverse metric
is complete; integrated skew-adjointness remains for the genuine throat. The already constructed finite smooth
generating frame now supplies an explicit nonnegative energy
`Σᵢⱼ h(vᵢ,vⱼ)²`; this energy vanishes pointwise iff the tensor pair is zero.
The covariant finite rank-one sum is now defined abstractly for every
symmetric musical equivalence, and its trace pairing is proved exactly equal
to this energy. Bundlewise two-vector contraction proves every coefficient
`h(vᵢ,vⱼ)` smooth; consequently the one- and two-sector frame energies are
genuine smooth scalar fields. The following covector/outer-product assembly
promotes the pointwise formula to the required smooth throat tensor section.
Each metric contraction with a frame vector is now a genuine smooth covector
section. Their fiberwise outer and symmetric products are genuine smooth
tensors, and smooth scalar multiplication is available. The finite weighted
sum is assembled as a genuine smooth symmetric tensor and specialized
componentwise to the intrinsic two-sector throat metric pair. A new intrinsic
rank-one contraction lemma bypasses the local `TangentSpace` wrapper mismatch
and proves the exact pointwise trace-pairing identity for the assembled
dualizer. The positive-dualizer input of the global BRST gate is therefore
unconditional; integrated skew-adjointness is its remaining geometric input.
The tensor and Maxwell pullback generators are now additive on differentiable
orbits and homogeneous in their field slots, hence bundle as genuine
field-linear maps under an explicit all-smooth-field orbit-differentiability
contract. The canonical intrinsic metric
is also registered in `GlobalBRSTFrontier` as fixed infinitesimally by the
genuine complete time-translation subgroup. Smooth two-vector contraction,
already available in the effective-D8 functor, now proves the metric Cartan
reduction: as for Maxwell, any globally smooth bilinear action satisfying
Cartan evaluation automatically satisfies the ghost bracket law. The metric
Cartan residual is now tensorial in both test fields, packaged by
`TensorialAt.mkHom₂` as a symmetric covariant fiber tensor and specialized to
smooth Janus tensors. Its evaluation on any two smooth ghosts is a genuine
smooth scalar field. The finite local assembly now yields the global smooth
bilinear metric action, its `SymmetricTensorCartanActionData`, the smooth-ghost
Lie representation and the exact bracket theorem.
The generic Maxwell residual
`X(A(Y))-A([X,Y])` is now tensorial in `Y`, packaged by
`TensorialAt.mkHom` as a true cotangent-fiber map, and specialized
componentwise to intrinsic smooth D8 gauge potentials. Its uniform
Hom-bundle regularity is now proved; the resulting global action is smooth,
bilinear, packaged as `GaugePotentialCartanActionData`, and upgraded to the
canonical smooth-ghost Lie representation with its bracket theorem. This
also closes the field and algebraic coadjoint-antifield BRST obstructions and
the canonical evaluation-pairing identity, but not a geometric or integrated
Maxwell antifield dual.
Together, these concrete Maxwell and metric actions form the canonical
tensorial action/representation packet and close its algebraic Maxwell and
two-metric coadjoint BRST certificate. Geometric or integrated duals remain
separate.
The bulk time-translation ghost and all three canonical bulk rotation ghosts
now restrict exactly to their throat ghosts through the derivative of the
fixed-throat inclusion. No throat-metric skew statement is inferred from this
alone. The rotation pullback orbit is concrete and its intrinsic raised
pairing, including the two-sector pairing, is pointwise natural under the
actual throat pullback. Its canonical-measure integral is also invariant under
every finite rotation, so the resulting integrated scalar curve has derivative
zero at angle zero by constancy. A public generic chain rule also differentiates
every fixed-fiber `SmoothThroatField` composed with the rotation, giving its
`mvfderiv` along the throat rotation ghost. It does not differentiate the
`mfderiv` factors in tensor pullback. Tensor-pullback angle differentiability,
the corresponding pairing chain rule and the independent generator/action
identification remain before any tensor skew or coadjoint conclusion; the
throat tensor orbit for time is not yet bundled.
Each throat rotation is now also a genuine smooth diffeomorphism with a
smooth pullback on symmetric throat two-tensors and exact identity at angle
zero. The corresponding finite ambient rotation preserves the Minkowski form,
and the induced cover rotation is an exact isometry of the intrinsic cover
Lorentz tensor. Pointwise quotient/throat pairing naturality and finite
integrated invariance are now closed, as is the zero derivative of the
resulting integrated scalar curve. The generic fixed-fiber field chain rule is
also public, but does not derive tensor pullback. Tensor-pullback angle
differentiability, the pairing chain rule and the orbit-generator/action bridge
remain before tensor skew or coadjoint transport follows.
On the bulk metric pair, the genuine time-flow tensor/background orbits,
intrinsic-background fixity, canonical-measure integral invariance and the
zero scalar derivative of the invariant pairing orbit are explicit.
Simultaneous pullback naturality is proved through the pulled-back musical
maps, conjugation and trace invariance. A separate pointwise contract now asks
that the actual pullback generator equal the supplied action; inhabiting it
and justifying differentiation through the integrated pairing remain before
skew follows.
Candidate A also has a nonlinear complete-flow interface: termwise invariance
of its nine blocks implies exact assembled-action invariance and Euler
horizontality for the field-dependent generator. Concrete fixed-measure
nine-block invariance is still the missing inhabitant. Transported covariance
now converts generically to that fixed-measure contract under exact measure
preservation. For the five measure-dependent Candidate-A blocks, their exact
integral covariance follows under seven supplied density-field pullback
identities; the interaction identity is further reduced to metric/root/basis
naturality. Only the fixed canonical GHY control vanishes identically; the
mobile sourced Robin block is retained. The four
SpinC-matter/LL/Robin/finite-BV ambient covariances and a concrete global-field/chart
flow remain. One explicit conformal zero-field configuration orbit now has
exact zero/add laws, but it is not lifted to action data or a chart. The
abstract flow is still not
identified with geometric pullback. The earlier affine interface embeds into
it through the proved constant-translation flow.
The curvature-based Maxwell pairing is
gauge-degenerate and is not substituted for a potential-antifield dual.
Parent-action selection is likewise non-unique in the current admissible
family, and all available geometric, spectral, heat and charge laws retain a
common rescaling orbit. Thus neither microscopic selection nor absolute scale
follows from the current assumptions.

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

The repository does **not** yet contain the full differentiable Janus
structured-jet groupoid, the geometric higher-order jet-isomorphism theorem,
the raw-field normed atlas and componentwise local Euler/diffeomorphism
system, a selected microscopic action, a unique vacuum or an absolute no-fit
scale.

### Global smooth scalar wave update

`P0EFTJanusMappingTorusGlobalSmoothScalarWave4D` packages the existing
canonical intrinsic wave as a global smooth scalar field, proves real
linearity, and gives finite-measure integrability.
`P0EFTJanusMappingTorusGlobalSmoothScalarProduct4D` adds the missing global
smooth pointwise product and its local gradient Leibniz law. The covariant
product jet and its exact wave-contraction rule are also closed algebraically.
It is now identified with the actual second derivative of the global product;
the induced global smooth gradient pairing has the expected local
inverse-metric representative and gives the pointwise global wave product
rule. The spatial-conformal Einstein--Hilbert Hessian and the raw
conformal curvature bridge through scalar curvature are closed. On the
restricted product of logarithmic spatial-conformal metric directions and
arbitrary Abelian potential directions, the Einstein--Maxwell Hessian is now a
genuine symmetric bilinear form. Its cross block is identified with the
already proved same-action conformal--potential Maxwell Hessian and therefore
vanishes. This still does not supply an arbitrary metric-section chart.
`P0EFTJanusMappingTorusSpatialConformalMetricJet4D` reuses the existing
positive conformal Lorentz metric and proves its local coefficient, matrix,
and first-derivative product laws. Its inverse and Christoffel laws are closed;
the companion curvature jet closes the differentiated connection, Riemann, Ricci and scalar contraction.
### Spatial conformal Einstein--Hilbert Hessian

`P0EFTJanusMappingTorusSpatialConformalEinsteinHilbertHessian4D` closes the
reduced four-dimensional conformal-density Hessian along
`g(t) = exp(2 t u) g₀`: the density curve is differentiated twice under the
canonical compact integral, the polarized Hessian is symmetric, and its
diagonal equals the integrated second derivative at zero. The conformal
inverse metric is also explicit.
`P0EFTJanusMappingTorusSpatialConformalPalatiniLinear4D` and
`P0EFTJanusMappingTorusSpatialConformalCurvatureClosure4D` now contract the
raw Ricci correction into its linear Palatini and quadratic pieces and prove
the standard four-dimensional conformal scalar-curvature law unconditionally.
`P0EFTJanusMappingTorusSpatialConformalExponentialCurvature4D` specializes it
locally and globally to
`R(g_t) = exp(-2tu) (R(g₀) - 6t □u - 6t² ⟨du,du⟩)`.
Finally,
`P0EFTJanusMappingTorusSpatialConformalEinsteinHilbertClosure4D` proves that
the genuine metric-volume frame-free Einstein--Hilbert action along `g_t`
equals the differentiated conformal action curve, so its second variation at
zero is exactly the certified symmetric Hessian.

`P0EFTJanusMappingTorusSpatialConformalEinsteinMaxwellCoreHessian4D` packages
that Einstein--Hilbert block with the existing fixed-metric Maxwell potential
Hessian. The resulting product-core form is bilinear and symmetric, and its
metric--potential cross value is exactly
`conformalPotentialFrameFreeMaxwellMixedHessian`, whose same-action
two-parameter theorem proves it is zero. No arbitrary Lorentz-metric Hessian
or total field-space chart is claimed.
