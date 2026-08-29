# P covariant second-variation audit

Status: sectoral bulk, Abelian and mono-metric diffeomorphism off-shell
completions constructed; the Abelian extended bulk has an equivalent genuine
`L²` Hilbert chart with self-adjoint same-action Riesz representative; the LL
stationary Fredholm reduction and the exact off-shell self-adjoint reduction
are closed, and the normal-collar derivative is the canonical orthogonal lift;
no total-chart `1001` input.

## Global closure obstruction

The authoritative obligation ledger is
[`HESSIAN-GLOBAL-01` closure map](hessian_global_01_closure_map.md). Historical
residual lists in this audit do not override that ledger.

`HESSIAN-GLOBAL-01` is not closed by the existing sectoral operators.
The field-content choice is now explicit rather than hidden:

- H05/P1 is closed by
  `regular_general_metric_c2_einstein_hilbert_gate`: the unrestricted
  general-metric Einstein--Hilbert family is `C²` on its admissible open chart
  and agrees exactly with the intrinsic action at the physical point. The
  remaining authoritative packages are P2--P4.

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
  The same off-shell state now has an injective graph-feature map: the old
  potential/Lorenz coordinates are reused once, while independent `B`, `c̄`,
  raw `c` and the true `δ_g d c` feature are added. Its smooth range is
  injective, and its closure is the declared Hilbert feature completion. A
  bounded symmetric Hessian and its Riesz representative agree, for the
  canonical Lorentz volume used by that completion, with the integrated `sΨ`
  polarization;
  the quadratic graph action is `C∞` with that constant second Fréchet
  derivative. At the physical Candidate-A metric, the graph core maps
  injectively to the two typed Abelian triples in
  `GlobalGaugeFixedPhysicalFieldTangent`; the diffeomorphism triple is zero.
  The existing global Cartan metric action also supplies the genuine
  infinitesimal generator `c ↦ L_c g`. Composing it with the completed de
  Donder operator constructs, for every supplied metric and without an
  assumption, the differential diffeomorphism FP map
  `c ↦ B_g(L_c g)`.
  The complete smooth de Donder one-form is now available and is bundled as
  a real-linear operator on genuine smooth symmetric perturbations. Raising
  two outputs with the supplied metric gives a smooth inverse-metric pairing;
  its integral against the existing finite general-metric volume is a
  symmetric bilinear form and exactly polarizes the associated quadratic
  functional. The already constructed finite tangent frame and canonical
  scalar `L²` injection give a faithful refined de Donder Hilbert graph:
  raw tensor coordinates are injective, its smooth core is dense, and the
  true and raised de Donder feature projections are bounded. Their symmetrized
  cross pairing extends the Lorentzian form exactly, without identifying it
  with the positive graph inner product. The resulting graph action is `C∞`;
  its constant second Fréchet derivative is this bounded symmetric Hessian and
  restricts to the original integrated pairing.
- the intrinsic paired Maxwell potentials now enter the corrected minimal
  physical tangent through a linear injective map obtained from the actual
  Candidate-A regular frames. This fixes the coefficient/intrinsic mismatch
  without asserting a nonexistent smooth inverse coframe.
- the supplied-metric Lorenz feature now has an injective dense smooth graph
  completion. Its bounded nonnegative Riesz representative is symmetric, has
  kernel exactly equal to the Lorenz kernel, and agrees on the smooth core
  with the reduced on-shell polarization of the unchanged global BRST
  gauge-fixing action.
- the two refined metric graphs and the Lorenz graph now form one physical
  metric-plus-Abelian gauge Hilbert subchart. Its quadratic action is `C∞`,
  with exact direct-sum second Fréchet derivative on the common smooth core.
  Metric and intrinsic potential directions enter the corrected typed
  gauge-fixed tangent linearly and injectively, while all typed nonminimal
  coordinates remain zero. This is deliberately not the total chart.
- that gauge subchart, the primitive SpinC matter graph and the complete LL
  graph now form one physical bulk graph product. Pullback adapters reuse the
  existing bounded forms without changing their calculus structures. The
  resulting quadratic action is `C∞`, is exactly the sum of the three graph
  actions, has the exact first derivative, and its constant second Fréchet
  derivative is the block-diagonal sum of their existing same-action forms.
  It is not yet identified with a pullback of the complete nonlinear
  covariant action. Its common gauge-smooth × finite-SpinC ×
  smooth-LL core embeds linearly, injectively and densely for the true product
  graph norm; in particular the matter density is graph-norm density. At the
  Candidate-A metric and physical matter mass, one injective linear map records
  both this graph point and its exact slots in `GlobalPhysicalFieldTangent`.
  No map from the whole graph completion to smooth tangent fields is asserted.
  A second, nonduplicating product replaces the Lorenz factor by the Abelian
  off-shell graph rather than adjoining another potential. Its quadratic
  action is `C²`, its second Fréchet derivative is the exact block Hessian,
  and its common smooth core maps injectively to the combined typed tangent.
  This remains a sector-action sum, not a proved pullback of the full nonlinear
  covariant action.
  The action-selected diagonal diffeomorphism graph now replaces the two
  independent de Donder blocks in that product. Its shared two-metric/one-
  triplet core is square-zero, dense and injective; the weighted `sΨ` gives its
  bounded symmetric Hessian and Riesz representative. The resulting
  diagonal-diffeomorphism × Abelian × matter × LL product has an exact `C²`
  action, constant assembled Hessian and injective graph/typed-core raccord.
  No new axiom, second diffeomorphism triplet or Lorenz copy is introduced.
  These four diagonal graph factors now also carry nested `WithLp 2` product
  norms. This complete real Hilbert chart is continuously linearly equivalent
  to the diagonal finite maximum-norm product; its smooth core stays
  dense/injective and maps jointly to the typed tangent. Its `C²` quadratic
  action is exactly the transported action and still equals diagonal `sΨ` plus
  the Abelian, matter and LL actions on that core. The symmetric block Hessian
  therefore has a bounded self-adjoint Riesz representative on this genuine
  Hilbert product. This does not prove standalone self-adjointness of either
  scalar Faddeev--Popov component.

This removes the old D10 and matter-bundle mismatches and closes the physical
metric-plus-Abelian gauge subchart without adding an axiom. It does not close
the total Hessian. The D10-free spectral target still covers
only D9 gauge `3` plus the historical five ghost coordinates and SpinC matter;
it omits the two metric tensors, normal displacement, the newly typed
antighost/Nakanishi--Lautrup fields, LL auxiliary metric/measure and boundary
blocks. The old LL Fredholm enlargement covers only the `llField` slice, but
the same-action form no longer does: the complete
`llAuxMetric × llMeasure × llField` smooth core now embeds injectively and
densely into one Hilbert graph completion. Its bounded symmetric Riesz
representative agrees exactly with the unchanged full three-slot LL Hessian,
including both cross blocks, and its kernel is characterized by the actual
feature equations. The same graph now carries a genuine `C∞` quadratic action
whose constant second Fréchet derivative is that exact same-action form.
This construction deliberately assumes neither
nonvanishing weights nor coercivity. Every pure `llMeasure` direction remains
in the auxiliary/measure subblock kernel. Off shell, closed range for the
complete operator still needs an estimate. The complete Riesz operator is now
proved self-adjoint. The generic bounded self-adjoint reduction proves that
closed range plus finite-dimensional kernel automatically gives a
finite-dimensional cokernel, and its LL specialization records the full
Fredholm criterion. Thus the only independent off-shell LL estimates left are
closed range and finite-dimensional radical. On the stationary branch,
stationarity forces `llField = 0`; the Fredholm criterion and index-zero
corollary now take stationarity directly and derive this zero-flux fact
internally. The Riesz operator then factors through the field projection, its
quotient by the exact kernel is continuously linearly equivalent to the
existing `LLH1Space`, the descended Riesz operator is the identity, and the
quotient realization is Fredholm of index zero.

The normal displacement is not a missing field type: the D10-free physical
tangent already contains the genuine sign-clutched smooth normal-line
section, now exposed directly by
`GlobalPhysicalFieldTangent.normalDisplacement`. Its local normal coordinate
now produces an unconditional deck-equivariant `arctan` collar family. The
family descends from the effective throat to the bulk quotient, equals the
canonical throat inclusion at parameter zero, has the prescribed pointwise
normal-coordinate velocity and zero scalar acceleration there. Every fixed
parameter gives an injective physical throat graph, and every fixed throat
point gives a `C∞` parameter curve. The descended map is now jointly `C∞` in
the throat point and collar parameter. After the explicit tangent transport
along `normalGraph_zero`, its `mfderiv` at zero is exactly the existing
canonical global orthogonal lift of the differential-normal class selected by
the same local displacement coordinate. What remains is the induced
metric/boundary action family and its same-action normal Hessian; assigning an
independent normal operator would still not be a second variation.

The canonical non-null GHY block is no longer missing: the existing exact
Candidate-A theorem makes this action summand identically zero for every
global datum. Its pullback to every regular chart is smooth with zero first
and second Fréchet derivatives, hence its same-action Hessian is genuinely
the zero symmetric form. For the finite null-face/counterterm/joint block,
the one-face transgression now assembles independent normalization parameters
in `EuclideanSpace ℝ NullFace`. The exact GHY plus null boundary action is
constant on this finite Hilbert chart, so its actual Fréchet Hessian and
bounded self-adjoint Riesz representative are zero. The former simultaneous
real curve is recovered by the constant-coordinate inclusion. General
null-face geometry and normal-displacement variations remain open.
Any chart with an independent `Theta` coordinate and a nonzero uncancelled
coefficient cannot carry one classical Hessian across `Theta = 0`: the
existing no-go proves that its `Theta log |Theta|` factor is not even `C¹`
there. A generic null-boundary Hessian must therefore live on a regular sign
stratum `Theta ≠ 0`. Constrained subcharts with a proved cancellation, such as
the exact reparametrization curve above, are not excluded. On the regular
strata, the pointwise density Hessian is now constructed from the unchanged
action: its scalar form is exactly `(u,v) ↦ Theta⁻¹ u v`, multiplied by the
already declared fixed screen/gravitational coefficient. Integration over a
geometric null hypersurface is not yet supplied.

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

`P0EFTJanusProgramPGlobalCandidateAStrongEinsteinMaxwellC2Closure4D` removes
the integration sub-obstruction. For every finite measure, integration is a
continuous linear map on the canonical strong scalar core. Consequently a
`C²` strong lift of the actual volume and scalar curvature makes the genuine
Einstein--Hilbert action line `C²`; the analogous volume/pairing lifts do the
same for the genuine varying-metric Maxwell line, globally or on an open
domain. Separate domination and parameter--spacetime continuity hypotheses
are no longer needed after such lifts are available. The gate does not
construct those lifts. The complete C² jet/root core is now available, but the
actual general-metric map into it for volume, scalar curvature and Maxwell
pairing remains necessary.

`P0EFTJanusProgramPGlobalActionSpectatorSectors4D` and the unbounded
zero-quotient-Hessian no-go still forbid reusing the historical D10-extended
operator as the action Hessian. The unbounded promotion gate itself now uses
the corrected D10-free LL target, but honestly leaves its dense global
same-action core as residual data.
`P0EFTJanusProgramPGlobalCandidateADiagonalCovariantHessianResidualBridge4D`
now composes that corrected typed core with the minimal physical inclusion and
the legacy tangent at exactly zero D10. Given the existing
`ProgramPGlobalVariationalChartCoreBridge4D`, it pulls back the actual
covariant second Fréchet derivative and proves the exact decomposition

`gauge-fixed covariant Hessian = completed graph Hessian + physical residual`.

`P0EFTJanusProgramPGlobalCandidateALocalPhysicalHessianSplit4D` shows that
this former residual must not vanish: it is the physical seven-block Hessian
plus the matter--LL same-action mismatch. The corrected comparison augments
the graph by the retained physical Hessian, and equality is equivalent only
to vanishing of the matter--LL mismatch. This prevents an accidental removal
of Einstein--Maxwell and boundary dynamics.
`P0EFTJanusProgramPGlobalCandidateAMinimalPhysicalLocalHessianBridge4D`
states the same exact comparison directly on the nonduplicated D10-free
physical tangent. The historical D10-extended bridge remains only a proved
zero-D10 factorization for compatibility.
`P0EFTJanusProgramPGlobalCandidateAMatterFiniteGraphVariationalChart4D`
now supplies the first genuine nonconstant subchart of that comparison. It
keeps every non-matter datum fixed, puts the inherited closed-graph norm on the
finite SpinC range, proves all nine exact covariant-action blocks `C²`, and
identifies the actual `globalCandidateAHessian` with the pullback of the
primitive `2D+m²` graph form. Thus the matter subtraction is now validated on
the real covariant action, not only on the model graph action. This is not an
inhabitant of the total diagonal chart bridge and does not annul the remaining
general-metric/boundary residual.
`P0EFTJanusProgramPGlobalCandidateABoundaryReparametrizationVariationalChart4D`
also inserts the existing independent null-generator rescalings into the real
covariant action data. All nine exact blocks are `C²`, the action pullback is
constant, and the actual `globalCandidateAHessian` is zero. This covers only
normalization reparametrizations, not normal displacement or general boundary
geometry.
The same gate now extends any existing covariant chart functorially. The
extended Hessian is exactly the first-projection pullback of the original one,
so every normalization and mixed normalization block vanishes. Applied to the
matter chart, it retains precisely the primitive `2D+m²` graph form.
The former whole-space chart mismatch is now closed by
`P0EFTJanusProgramPGlobalLocalVariationalChart4D`. Its physical configuration/
action datum exists only for points of an open admissible set `U` in a normed
model, with `0 ∈ U`. The nine hypotheses are `ContDiffWithinAt` on `U`;
openness yields ordinary ambient `ContDiffAt`, the actual ambient Euler
derivative, and a symmetric Hessian on the full model tangent space. The
fallback used to totalize the scalar action outside `U` carries no physical
datum. The conversion `U = univ` proves exact compatibility with every former
global chart, including equality of action pullback, Euler form and Hessian.
`P0EFTJanusProgramPGlobalCandidateADiagonalLocalCovariantHessianResidualBridge4D`
now pulls that local Hessian back through a dense injective smooth-core map at
any admissible base point. It reuses the existing diagonal BRST, matter and LL
forms and proves the exact gauge-fixed covariant = graph + physical-residual
decomposition. For `U = univ`, both the covariant core Hessian and residual are
exactly the former ones; the corrected physical split applies to both APIs.
The pointwise root input is now genuinely `C²` on an open perturbation domain:
`P0EFTJanusPositiveRawSplitCharpolyContDiffLocalRootBranch4D` works around
every positive-real-split raw target, contains zero in translated coordinates,
and proves the exact square identity throughout. It is neither diagonal nor a
Minkowski specialization. The same gate now proves a generic continuation
upgrade: a continuous root lift satisfying the square identity and pointwise
Sylvester bijectivity is automatically `C²` whenever its target is `C²`.
The continuous-field intermediate layer is now concrete:
`P0EFTJanusContinuousMatrixFieldContDiffLocalRootBranch4D` proves that on any
compact base, pointwise Sylvester regularity induces a bounded equivalence on
the uniform Banach space of continuous matrix fields and hence an open
zero-centered `C²` root chart with the exact fieldwise square identity.
`P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0Space4D` now supplies the
scalar strong-regularity Banach model as the closed equalizer of the existing
continuous maps `C⁰ → L²` and `H¹ → L²`. Its two projections agree in physical
`L²`, and the smooth core has an exact compatible lift. This uses neither a
Sobolev embedding nor a new axiom.
`P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0CoreClosure4D` avoids assuming
simultaneous smooth density in the whole equalizer: it takes the closed smooth
core inside it, proves completeness and injectivity, and makes smooth density
true by construction.
`P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0SmoothLeibniz4D` reuses the
existing smooth scalar product and proves the exact intrinsic first-jet rule
`(fg, f·dg + g·df)` together with bilinearity into that dense core.
`P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0ProductExtension4D` proves
the uniform strong estimate from the existing `L∞·L² → L²` Hölder map and
extends multiplication canonically to a continuous bilinear map on the full
complete core, with exact smooth agreement and no new hypothesis.
`P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0MatrixProduct4D` assembles
this operation on `4 × 4` coefficient matrices. The product is continuous
bilinear, agrees with smooth matrix multiplication, projects to the exact
pointwise continuous product, and its square is `C∞` with the exact Sylvester
Fréchet derivative.
`P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0LocalRootBranch4D` then
reuses the existing pointwise inverse family. For every general smooth matrix
root with pointwise bijective Sylvester operator, its inverse coefficients are
smooth, assemble into a bounded equivalence on the strong core, and yield an
open `0 ∈ U` `C²` root chart with the exact square identity. No diagonal
specialization or extra analytic axiom is used.
  The former fixed-size limitation is also removed.
  `P0EFTJanusMappingTorusCanonicalPhysicalStrongH1C0FiniteMatrixProduct4D`
  constructs the associative strong product for arbitrary finite matrices, with
  exact smooth/continuous agreement and the expected smooth square/Sylvester
  derivative. The companion `...FiniteMatrixLinearEquivLift4D` lifts every
  smooth pointwise-bijective finite operator family to a bounded equivalence on
  the strong completion. `P0EFTJanusProgramPGlobalCandidateAFiniteFrameRootBridge4D` uses
the existing finite smooth tangent generators to encode the intrinsic
Candidate-A root. Redundancy is retained honestly: the encoded identity is a
smooth idempotent `P`, not the ambient identity. The two
`P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCorner*` gates construct
the closed complete corner `P M_N P`, prove that the root lies in it, and
internalize its bounded product, smooth square and Sylvester derivative.
`P0EFTJanusProgramPGlobalCandidateAStrongFiniteFrameCornerLocalRoot4D` then
supplies a reusable Banach IFT certificate and, assuming bijectivity of the
strong corner Sylvester operator at the center, an open zero-centered domain,
a branch `C²` throughout that domain and the exact square identity there.
  No global frame or new physical axiom is assumed. The three
  `...StrongFiniteFrameSylvester*` gates now close the missing transport:
  intrinsic pointwise Sylvester bijectivity gives a smooth bijective ambient
  extension (identity off the corner), exact dense-core agreement, commutation
  with the corner projector, strong-corner bijectivity and finally the full
  open-domain `C²` root branch.
  The regular-stratum gate now also defines the explicit subtype
  `GlobalCandidateASylvesterRegularGeometry` and the corresponding local-chart
  predicate; every admissible point of such a chart inherits that full branch.
`P0EFTJanusProgramPGlobalStrongH1C0AnalysisDomain4D` applies the equalizer to
the pre-existing finite `GlobalBulkSobolevSlot`, so all bulk metric, gauge and
ghost coefficients form a complete product with exact smooth-tangent lift.
  The general intrinsic encoding, strong corner algebra, regularity transport
  and local chart interface are therefore concrete on the intrinsic
  Sylvester-regular stratum. `GlobalCandidateAGeometry` itself does not exclude
  singular roots. The explicit stratum restriction is now formalized, and
  `P0EFTJanusProgramPGlobalCandidateAPositiveSelectedRootSylvester4D` proves
  that the stored root is intrinsically regular whenever it is exactly the
  existing positive spectral selector; no Sylvester hypothesis is inserted in
  that certificate. The local-root joint-regularity gate now proves that every
  strong `C²` target family pulls the branch back to an open parameter domain
  with jointly continuous parameter--spacetime coefficients and the exact
  square identity.
  The genuine order-two field layer is now available as well. The canonical
  scalar C² jet core is complete, has the exact second-order Leibniz product
  and maps continuously to the strong `C⁰ ∩ H¹` core. Finite C² matrices have
  associative multiplication, a smooth square and the exact Sylvester
  derivative; the canonical local root branch is C² on an open domain, and
  every coefficient's value, first derivatives and ordered second derivatives
  are jointly continuous in parameter and spacetime. The intrinsic redundant
  finite-frame projector defines a complete C² corner containing the selected
  root. Intrinsic Sylvester regularity restricts to a bounded equivalence on
  that corner and activates its open-domain C² root branch, with no new axiom.
  Thus higher-order local-root regularity is closed. The actual general-metric
  map into this C² core and the jointly C² nine-block action data remain
  downstream.
  Closing the ticket therefore has a strict dependency order: construct the
  actual general-metric C² target and its curvature/pairing lifts; realize the arbitrary-general-metric
  Einstein--Maxwell and general normal/boundary same-action blocks while
  closing only the matter--LL mismatch; only then promote common domains,
  prove off-shell LL closed range and finite radical, and construct the total
  same-action Fredholm sum.

The multiplicity audit also separates two facts. The diagonal graph core and
its `WithLp 2` realization already have a dense injective smooth core and a
faithful typed raccord. The historical spectral target still uses
`ι × Fin 8` for D9 and is therefore a valid reduced Fredholm model, not the
faithful total field content. No theorem currently identifies it with the
complete typed action Hessian.

Finally, the existing zero-Hessian and zero-quotient-Hessian no-go theorems
show that chartwise `C²` regularity cannot imply an infinite-dimensional
Fredholm realization for unrestricted couplings. Terminal closure therefore
requires an explicitly constructed nondegenerate elliptic analytic stratum
(gauge/continuation, boundary realization and common domain), not a new
physical axiom hidden in a chart field. Until that choice is made and proved
compatible with the unchanged action, `HESSIAN-GLOBAL-01` remains a frontier.

The former obstruction to the total diffeomorphism assembly is now resolved.
Candidate A has two canonical mono-metric FP maps, but the typed field space
has one diagonal diffeomorphism `c/c̄/B` triplet, whereas the existing physical
gauge Hessian is the sum of two independent de Donder squares. Eliminating one
`B` after coupling it to any sum, difference or weighted projection of the two
conditions produces a square with a cross term and does not recover that
existing sum. The scalar weighted-projection no-go now proves this obstruction
already in one real component. The kinetic-adjoint bridge now resolves the
selection without duplicating the triplet: the Einstein--Hilbert coefficients
`1/(2κ₊)` and `1/(2κ₋)` weight the direct-sum DeWitt pairing, whose proved
four-dimensional adjoint is exactly
`F₊/(2κ₊) + F₋/(2κ₋)`. The global smooth condition and its FP composite are
constructed, the weights are unique, and the spatial FP symbol has trivial
kernel when their sum is nonzero. Thus the old two-square Hessian must be
replaced, not silently reused.
That replacement is now implemented directly on the shared two-metric core:
`s hₛ = L_c gₛ`, `s c = 0`, `s cbar = B`, `s B = 0` is square-zero; its graph
core is injective and dense, its bounded symmetric Hessian/Riesz representative
agrees with the weighted diagonal `sΨ`, and its quadratic action is `C²`.
The same core is inserted into the total bulk graph and maps injectively to the
existing typed tangent, so no external projection choice or duplicate triplet
is imposed.
The construction uses ordinary real field spaces and does not formalize a
Grassmann-graded odd derivation.

The Abelian smooth differential operator is now constructed. The local raised
potential and its Levi-Civita divergence obey the true transition law, hence
descend for every supplied `SmoothGeneralLorentzMetric` to a global linear
Lorenz codifferential
`δ_g : SmoothAbelianGaugePotential → SmoothScalarField`. Its actual
Faddeev--Popov composite is `δ_g d` and agrees chartwise with the covariant
scalar wave. The earlier canonical operator is exactly the intrinsic-metric
specialization and satisfies `δ(d c)=+□c`. For that intrinsic metric, every
real ghost component is now identified pointwise and in physical `L²` with
the canonical mass-zero scalar Euler operator. Its FP adjunction defect is
exactly the established scalar Euler skew-density integral, and smooth-core
symmetry for each ghost pair is equivalent to the vanishing of that integral.
The FP Green--Stokes adapter now reuses the pre-existing unrestricted scalar
Green datum to identify this defect with the exact oriented cut-bulk current;
all existing Green-isotropic domains therefore give componentwise formal
symmetry, including the explicit Dirichlet specialization. No new axiom or
Green interface is introduced. From that same datum, the existing mass-zero
physical Green core is definitionally the FP component. Existing cutoff
density therefore gives its minimal-core closability certificate. Taking the
finite `Sector × Fin 2` product yields a completed paired graph whose actual
smooth ghost core is dense, whose field projection is injective, and whose
single-valued ambient-range operator agrees on that core with the existing
paired FP map. This closes intrinsic projected closability conditionally on
the scalar Green datum. A further adapter reuses the existing completed
boundary-triple inputs and analytic-closure package: for every supplied
Lagrangian boundary condition, each of the four real FP components has dense
realization domain and equality of its actual-adjoint and realization domains.
The paired finite inclusion is dense/injective and agrees with the true FP map
on its admitted smooth core. No inhabitant of the analytic package is built,
but the existing direct physical package now feeds this certificate directly;
its remaining fields are adjoint regularity, one coercive shift, physical
Rellich compactness and semiboundedness. More sharply, the pre-existing
graph/direct-coercive Program P endpoint needs only its canonical-normal PDE
data, a graph estimate, a Lagrangian condition and shifted-form coercivity:
Rellich is already unconditional, a bounded real resolvent proves actual
adjoint-domain equality, and the admitted smooth realization is exactly the
intrinsic FP component. Its local-divergence data also reconstruct the global
Green--Stokes datum with definitionally the same scalar Green core, so no
separate Green hypothesis remains on this route. No inhabitant of those
remaining data is constructed. A repository-wide constructor audit confirms
that the energy/Gårding and positive-shift modules only convert an exact PDE
estimate or positive decomposition supplied in input. They do not derive one
from the Lorentzian wave. Dirichlet removes the boundary current, but the
already-proved strictly negative Lorentzian time coefficient prevents treating
the full dynamic Hessian as the positive `H¹` energy; the unconditional
intrinsic elliptic operator is explicitly a regulator, not that Hessian.
Thus this remains conditional and does not identify the total gauge-fixed
Hessian domain. The unconditional full 4D
`integral_eq_divergence`/Stokes theorem remains open; for a general supplied metric, the current physical
`L²` measure is still intrinsic and no matching adjoint/volume bridge is
proved. Independently, the
Lorenz graph completion gives the honest bounded adjoint of its continuous
feature projection and the same-action Riesz operator described above. It now
also carries an explicit smooth quadratic action whose first derivative is the
Lorenz form and whose constant second Fréchet derivative is that Riesz
pairing. On the dense smooth core it is exactly the reduced on-shell BRST
polarization, while the same core injects jointly into this Hilbert chart and
the corrected minimal tangent. This does not identify the bounded adjoint with
a differential codifferential. For the metric block there
is now a chart-independent smooth trace `tr_g h`, its differential and the
`-1/2 d(tr_g h)` part of de Donder on
`SmoothSymmetricCovariantTwoTensor`. The induced Levi-Civita derivative is
smooth, symmetric, satisfies `∇g = 0`, and obeys the full rank-three overlap
law. Its genuine contraction now gives a transition-independent local
covector, which is glued through the canonical atlas into the smooth global
one-form `div_g h`. Adding the existing trace differential closes the complete
smooth de Donder operator with its expected formula in every holonomic chart.
Its inverse-metric quadratic pairing is now smooth, integrable and bundled as
a symmetric bilinear form. A faithful Hilbert graph core and bounded de Donder
  and raised-feature projections are also available. Their bounded
  symmetrized cross form extends the direct Lorentzian pairing exactly and is
  the constant second Fréchet derivative of a `C∞` graph action. Two such
  metric graphs are assembled with the Lorenz graph in the physical gauge
  subchart described above. This does not prove a differential adjoint or
  Green identity; those still require genuine multiplier, Stokes/domain and
  total-chart layers.

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

`P0EFTJanusMappingTorusSpatialConformalEinsteinMaxwellCoreHessian4D` now
combines the genuine spatial-conformal Einstein--Hilbert block with that
potential block into a symmetric bilinear form on the restricted product
core. Its conformal-metric--potential cross value is explicitly identified
with the existing same-action mixed Maxwell Hessian above and is zero.

This does not construct arbitrary-metric--potential mixing, a field-space
Fréchet Hessian, the Candidate-A interaction or nine-block
chart/core/Jacobi/Fredholm identification.

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
bridge through scalar curvature are closed. The restricted
spatial-conformal Einstein--Maxwell product-core Hessian and its exact zero
conformal--potential cross block are closed as well. The available interfaces
still do not construct an arbitrary metric-section chart.

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
