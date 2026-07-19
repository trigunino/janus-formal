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
Mathlib trace-class API. The full Fredholm/Quillen family and the
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
additional global choices, not a canonical functor of the real line. The
ambient Clifford gate now constructs an actual Spin element for every pair of
unit reflections, proves that its projection is their exact product, and
extends this construction to every finite list of pairs. Full surjectivity is
now unconditional: Mathlib's finite-dimensional reflection-generation theorem
supplies Cartan--Dieudonné and determinant parity, yielding both
`Spin(4) → SO(4)` surjectivity and a lifting function. The ambient determinant
descent is now proved empty: the mapping torus is nonorientable, so no honest
continuous oriented Spin or SpinC Čech realization exists. Purely algebraic
Spin Čech data remain conditional. The full twisted `Pin⁻(4)` projection,
central order-four reflection generator and normal character are now
unconditional; the ambient extension is reduced exactly to one continuous
normalized normal-compatible Čech choice, whose existence remains open. The
reference generator is now identified with the explicit `O(4)` flip and its
orientation character is proved on all four `ZMod 4` phases. A corrected
overlap-only normal interface now has the canonical ambient Čech winding built
from the genuine covering local sections, with normalization, cocycle and local
constancy. On an honest open chart refinement, the throat local section is
natural under the fixed-throat inclusion, the induced coordinate lies in the
real ambient transition source, and the ambient winding equals the throat
`localTransitionWinding`. This closes the winding and local-section naturality
only. The smooth orthonormal refinement is now closed independently by the
Whitney/Gram--Schmidt construction. The Jacobian-parity comparison, exact
`O(4)` reduction law and ambient `Pin⁻` lift remain open. A new exact chart
gauge no-go shows why the winding cannot determine the raw Jacobian sign by
itself: reversing one chart leaves the winding fixed and flips the determinant
and its `ZMod 2` parity. Independently, the central orthonormal-frame gauge
`-id` preserves the Euclidean form while changing every reduced transition.
Compatible chart orientations and a local frame gauge are both required. At
the pointwise level the latter is now solved exactly and uniquely by
`actual⁻¹ ∘ expected`. Its exact conjugation-twisted Čech law and converse are
proved algebraically; only a smooth, normal-compatible realization remains.
For genuine chart-frame gauges, the induced vertex-gauge formula is now exact,
preserves the strict cocycle automatically, and has unique local propagation
from a fixed target gauge. Global smooth propagation and normal compatibility
remain the geometric obstruction.
On every common-root (star) subatlas, an explicit propagated vertex gauge now
realizes all target transitions. The unclosed part is global path independence
across the atlas, together with smoothness and the prescribed normal values.
The global path-independence obstruction is now exact: a loop closes precisely
when the root gauge intertwines the actual and target holonomies. This criterion
still has to be discharged for the genuine mapping-torus atlas.
For its cyclic fundamental holonomy, one generator equality is now proved to
propagate to every integer winding and to close every propagated loop. The
remaining atlas statement is the geometric identification of the actual
orthogonal generator with the chosen reference generator up to root gauge.
That last equality is now proved for every orthogonal frame aligning the true
normal axis with the reference axis, including all integer windings. The
remaining geometric construction is a smooth aligned frame on the genuine
atlas with the required throat restriction.
Pointwise existence is now unconditional: the ambient orthogonal group is
proved transitive on every quadratic level set, hence every unit normal admits
an aligning frame and the complete all-winding gauge. Only smooth choice and
atlas/throat compatibility remain.
The choice itself is no longer a smoothness obstruction: quaternionic left
multiplication gives a canonical orthogonal frame for every unit normal, sends
the reference axis to that normal, and is jointly polynomial (`C∞`) in normal
and tangent. It remains to feed it the genuine normalized atlas normal and
prove the required overlap/throat identities.
The preceding construction now accepts any smooth nonvanishing normal field:
Euclidean normalization is proved unit and `C∞`, and its quaternionic frame
application is jointly `C∞`. Supplying the genuine atlas-coordinate normal
with its deck/overlap laws is the remaining input.
The unavoidable one-sided sign change is handled exactly: normalization is
odd and the quaternionic frame changes by the central `-id` gauge under
`n ↦ -n`. Thus no forbidden global normal trivialization is assumed.
This is proved for every integer winding with the actual
`normalSignRepresentation`; the normalized quaternionic frames therefore carry
the same signed cocycle as the constructed normal line.
Although the frames themselves differ by `-id`, their conjugated aligned
reflection is proved identical. Hence the reflection datum descends across the
nontrivial normal sign cocycle without choosing a forbidden global normal.
The normalized aligned reflection is now packaged directly from any nonzero
local normal and proved invariant under the full integer normal-sign cocycle.
The corresponding Clifford construction is also explicit: every unit normal
defines a genuine `Pin⁻(4)` generator, normal reversal multiplies it by the
nontrivial central sign, and after normalization both the lift cocycle and its
projected all-winding descent are proved. The genuine atlas normal field and
its equality with the actual reduced transitions remain open.
The generated integer family `w ↦ g(n)^w` now obeys the strict additive
cocycle law, and its projection is exactly the corresponding integer power of
the local orthogonal reflection.
The Clifford projection is also proved equal, not merely analogous, to the
independently constructed quaternionic aligned reflection; the equality holds
for every integer power.
This construction is now instantiated on the actual canonical latitude normal
of the throat cover, whose product-coordinate representative is proved
nonzero. Its cyclic lift and projected aligned reflection are therefore
unconditional on every genuine cover chart.
The complete two-winding gauge law is exact: the overlap winding controls the
local normal sign, the lifted winding controls the cyclic phase, and an odd
overlap contributes precisely the matching power of the central Pin sign.
On the genuine throat cover, every integer change of anchor preserves the raw
product normal, its generator, and every cyclic lift. Thus the unavoidable
minus sign is correctly assigned to the quotient-chart transition itself.
Evaluating this normal on the genuine local covering sections now produces an
actual throat-atlas algebraic `Pin⁻(4)` transition lift. It is normalized,
satisfies the strict triple-overlap Cech cocycle from the real local winding,
and projects to the corresponding power of the aligned reflection. Continuity
and equality with the full ambient reduced transition remain open. Reverse
overlaps are exact inverses, and the genuine one-loop lift squares to the
nontrivial central sign.

## 5. Program P

The explicit nonabelian `so(3)` ghost triple and the corrected Koszul
differential are now closed for the entire currently implemented field/BV
package: linear matter/gauge/auxiliary sectors, positive diagonal metrics,
bulk and throat antifields, master actions, PT covariance, and boundary trace.
Derivative kernels, completed spaces, and arbitrary functionals remain a
strictly stronger open refinement.

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
  A nonempty scoped common-domain package now forces one configuration to feed
  the induced diagonal metrics/root, `LLH1`, the smooth boundary trace and typed
  D7/D9/D10 accessors. It does not yet identify the action tangent, Hessian,
  D10 diagonalization, regulator or Fredholm/boundary domains; these residuals
  remain one explicit contract. That contract now carries concrete extension,
  linearity, isometry, modal-density, derivative, spectral-pairing and domain
  equalities rather than unconstrained `Prop` readiness flags.
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
  specialization predicate and adapter connect this result to a supplied
  global interface. Under one explicit four-dimensional Green--Stokes
  contract, the global boundary functional is now exactly the concrete tangent
  normal flux and homogeneous Dirichlet data close the weak-Euler and
  stationarity corollaries. The Green--Stokes contract itself remains open.
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
  directly and its zero boundary flux realizes that ledger; LL weak/strong and
  stationary/strong equivalences follow for this frame. Extending the collar
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
  of either `Z4` multiplier. No canonical global scalar normal coordinate is
  claimed. The genuine smooth tangent diffeomorphism ghost now fills its D9
  component in the same local package. A canonical real rank-four coordinate
  equivalence now fills its matter slot in the D11 squared-spinor coordinate
  specialization, closing that residual record at coefficient level. It does
  not identify a geometric SpinC bundle. Global SpinC realization, a global
  action tangent producing the full symmetric metric slot, and
  action/Hessian/domain agreement remain explicit contracts.
  The global LL action now has an exact simultaneous measure/flux cubic
  expansion and integrated derivative for every finite measure. Its algebraic
  Euler system is equivalent to the zero-flux branch. PT pullback is an exact
  involution and preserves its density, action, variation, Euler coefficients
  and stationarity for PT-invariant measures. The auxiliary LL metric
  has identically zero response in this selected action, so a genuine
  differential LL PDE still requires a richer action.
  For the differential PT-symmetric LL functional, the canonical throat
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
  collar stress-energy result. The finite stratified boundary ledger is exactly
  zero and yields the LL weak/strong equivalence under the explicit continuous
  IPP plus flux-realization contract. A global manifold Stokes theorem without
  that contract, extension to a covariant four-dimensional Noether current and
  a global canonical metric normal remain open;
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
