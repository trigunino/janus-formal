# Janus Quantum World-Volume Alpha Program

## Purpose

Generate the absolute LL-brane charge scale without importing `H0`, an observed
radius, a fitted `alpha`, or an arbitrary world-volume mass parameter.

The classical bridge program has already reduced the exact-solution length
`A = alpha^2` to

```text
16 q_LL^2 A^4 = 1,
8 pi |chi| A = 1.
```

Therefore a microscopic derivation of `q_LL` or `|chi|` fixes `A`.

## Concrete candidate theory

On the `2+1` dimensional LL world-volume, introduce:

- a neutral real scalar `phi`;
- a compact `U(1)` connection `A_aux`;
- its intrinsic field strength `F_aux`;
- an integer Chern--Simons level `k`;
- the existing non-Riemannian LL measure sector.

A classically scale-invariant candidate density is

```text
L_WV = 1/2 (d phi)^2
       - lambda6 phi^6 / 6
       - F_aux^2 / (4 phi^2)
       + Chern--Simons_k[A_aux]
       + L_LL-measure.
```

In three spacetime dimensions:

```text
[phi] = 1/2,
[A_aux] = 1,
[(d phi)^2] = 3,
[phi^6] = 3,
[A dA] = 3,
[F_aux^2 / phi^2] = 3.
```

Thus no classical dimensionful coefficient is required.  By contrast, an
ordinary undressed Maxwell term needs a coefficient of mass dimension `-1` and
would simply hide the missing scale.

A one-component real scalar cannot carry a nontrivial continuous orthogonal
`U(1)` charge: its one-dimensional skew generator vanishes. The minimal
manifest therefore uses a neutral real scalar. A charged scalar branch would
require a complex scalar and constitutes a different candidate theory.

This choice is formalized in `P0EFTJanusRealScalarU1Representation.lean` and
recorded in `data/worldvolume_quantum_candidate_manifest.json`. The executable
`scripts/audit_janus_worldvolume_microscopic_manifest.py` checks representation
consistency, compactness, opposite PT-paired Chern--Simons levels and the
interaction basis, together with the perturbative choices below.

The conditional computational prescription is now fixed in that manifest:
background Lorenz gauge with `xi=1`, gauge-invariant higher-derivative plus
Pauli--Villars regularization, momentum subtraction at `mu`, and coverage
through two loops. These are calculation conventions, not uniquely selected
physics.

Around `phi=v+eta`, `v!=0`, the dressed Maxwell factor has the exact expansion

```text
1/(v+eta)^2 = 1/v^2 - 2 eta/v^3 + 3 eta^2/v^4 + remainder.
```

`P0EFTJanusBackgroundVertexExpansion.lean` proves the identity including its
exact remainder and the vertex lock `c1^2=(4/3)c0*c2`.
`scripts/derive_janus_worldvolume_background_vertices.py` independently checks
the coefficients and that all three vertex densities retain mass dimension
three. Full LL-measure and ghost vertices are still missing.

For the one-loop gauge contribution to the six-scalar vertex, truncation at
`eta^2` is not complete: the exact inverse-square dressing contains direct
`eta^n F^2` vertices through `n=6`. The manifest now requires expansion order
six. `P0EFTJanusGaugeLoopSexticCoverage.lean` classifies the four ring diagrams
built only from linear/quadratic vertices and proves that a connected gauge
ring has one loop. The companion executable verifies
`c_n=(-1)^n(n+1)/v^(n+2)` through `n=6`, including `c_6=7/v^8`.

`P0EFTJanusMCSPropagatorPowerCounting.lean` derives the transverse inverse of

```text
K = a p^2 P_T + kappa E,   E^2 = -p^2 P_T,
```

with denominator `a^2 p^2 + kappa^2` and topological mass squared
`kappa^2/a^2`. The symbolic audit independently inverts the physical
two-dimensional transverse block. Gauge rings built from `eta^n F^2` vertices
have superficial degree three. This identifies regulator-dependent power
divergences; it does not yet extract the logarithmic residue needed for a beta
function.

For the compact Abelian connection, linear Lorenz gauge gives the local
Faddeev--Popov symbol `|xi|^2`. The gate
`P0EFTJanusAbelianGhostDecoupling.lean` proves its nonzero-momentum kernel is
trivial. Because the scalar is neutral and the gauge group Abelian, this local
FP operator has no scalar--ghost interaction vertex. Global zero modes and the
primed determinant remain separate obligations.

The reduced published LL equations determine `F^2`, `M_measure` and `a0`, but
not the gauge generators of the local measure fields. The explicit no-go gate
`P0EFTJanusLLGhostOperatorFrontier.lean` constructs distinct ghost completions
with identical reduced LL constraints. Deriving LL ghosts therefore requires
the local measure fields, complete gauge/reducibility structure and a gauge
fermion; those data are not recoverable from the reduced equations alone.

Lean file:

```text
JanusFormal/Branches/WorldvolumeQuantumAlpha/Gates/
  P0EFTJanusScaleInvariantWorldvolumeAction.lean
```

The local bosonic Hamiltonian is now proved nonnegative when
`lambda6 >= 0`, the scalar and magnetic kinetic invariants are nonnegative,
and `phi != 0`.  The exclusion of `phi = 0` is explicit: the dressed Maxwell
coefficient is singular there, so closure still requires a quantum-domain or
field-redefinition prescription and the LL constraint Hamiltonian.

For strictly positive magnetic invariant, the same gate now proves a stronger
result: as `phi^2` approaches zero, `B/(4 phi^2)` exceeds every fixed positive
energy bound. Thus nonzero flux dynamically excludes the singular origin at
the classical level. In the zero-flux sector, however, `F^2/phi^2` approaches
zero along `F=0` and one along `F=phi`; it has no path-independent value at
`(phi,F)=(0,0)`. `P0EFTJanusPhiZeroFluxZeroFrontier.lean` proves this ambiguity.
The candidate therefore uses the punctured domain `phi != 0`; including the
origin requires an explicit boundary condition or UV completion.

Lean file: `P0EFTJanusClassicalBosonicStability.lean`.

## Signature and classical equations

`P0EFTJanusWorldvolumeSignatureAndEOM.lean` separates the real parity-even
Euclidean density from the imaginary Wick-rotated Chern--Simons term. It proves
positivity of the parity-even Euclidean density under the stated sign
conditions. For a homogeneous scalar it reduces the local equation to

```text
2 lambda6 phi^8 = magneticInvariant.
```

Consequently, with `lambda6 > 0`, the zero-flux sector has no nonzero
homogeneous stationary point. This is a conditional local equation, not yet the
full LL-constrained field equation.

`P0EFTJanusLLMeasureScalarCompatibility.lean` combines this scalar equation
with the published minimal LL measure and auxiliary-metric constraints. It
eliminates the continuous auxiliary invariant and reduces the saddle to
`4 lambda6 phi^8 = 1`. This remains conditional on that LL sector; its complete
first-class constraint algebra and reduced quantum Hilbert space are open.

The reduced LL saddle also does not determine `beta_LL`. Identical reduced
constraints admit quantum completions with different gauge-fixed Hessians and
different sextic beta contributions. This non-uniqueness is proved in
`P0EFTJanusLLGhostOperatorFrontier.lean`. A numerical LL residue requires the
local measure fields, full gauge/reducibility tower, gauge fermion, FP/BV
operator, vertices and zero-mode prescription; it cannot be recovered from
`F^2`, `M` and `a0` alone.

Programme P now supplies a reusable classical LL bridge: the global compact-
throat action and variation, an energy-Hilbert self-adjoint Fredholm operator
with trivial kernel and index zero, and a square-zero smooth ultralocal BV
model. `P0EFTJanusProgramPQuantumLLBridge.lean` imports these facts into A.
They do not yet identify the physical Sobolev fluctuation operator, compact
resolvent, primed determinant, gauge fermion or derivative-dependent BV
completion; consequently `beta_LL` and `gamma_LL` remain undetermined.

The manifest audit now reflects this distinction: the repository candidate is
ready for the non-LL conditional calculation, but not for the total RG
calculation. Its total `perturbative_rg_ready` flag remains false until the LL
physical completion, gauge fermion, determinant prescription and cross-scheme
matching are fixed.

`P0EFTJanusQuadraticBosonicNoGhost.lean` isolates the reduced scalar and
transverse-gauge residues. Positive residues and nonnegative scalar mass imply
a nonnegative quadratic energy whose kernel contains only the zero physical
modes. This is a bosonic criterion conditional on the LL/Dirac reduction; it is
not yet BRST unitarity or reflection positivity of the full quantum theory.

## Counterterms and finite scheme covariance

`P0EFTJanusFiniteSchemeCovariance.lean` records the minimal marginal basis
consisting of scalar kinetic, sextic, dressed Maxwell and gauge Chern--Simons
operators. It proves their mass dimension is three. At one-log order it also
proves invariance of both

```text
lambda6 + b log(sigma/mu)
mu exp(t)
```

under the matching finite coupling/logarithm shift. Completeness of the BRST
counterterm basis and the actual beta functions remain open calculations.

The four-operator list above is only the marginal basis. In the chosen
cutoff/Pauli--Villars-type prescription, the MCS determinant has asymptotic
terms

```text
Lambda m_CS^2/(4 pi^2) - m_CS^3/(12 pi),
m_CS proportional to |kappa| phi^2.
```

Therefore the power divergence has scalar shape `Lambda*kappa^2*phi^4` and a
quartic subtraction is required. More generally the even vacuum, quadratic,
quartic and sextic operators form the relevant-or-marginal scalar basis.
`P0EFTJanusMCSOneLoopSchemeAudit.lean` checks their dimensions. The finite
`|kappa|^3 phi^6` term is not a beta function and remains movable by a finite
sextic renormalization condition; no logarithmic divergence is claimed at this
order.

The isolated one-loop MCS contribution is therefore closed in MS: its
logarithmic sextic residue, and hence its sextic beta contribution, vanish.
This does not remove mixed higher-loop diagrams or LL-measure contributions.

For the dressed-Maxwell background vertices, every vertex carries exactly two
gauge half-edges. In a connected vacuum/background graph this gives

```text
L = I_scalar + 1.
```

Hence the one-loop sector has no internal scalar line and is precisely the
gauge-ring determinant already audited. Every genuinely mixed gauge-scalar
graph starts at two loops. `P0EFTJanusMixedGaugeScalarLoopOrder.lean` proves
this threshold; it does not assign the remaining two-loop residue.

The same UV count gives `D = I_scalar + 3` for these mixed graphs. Their
leading divergence is therefore a power divergence, not a primitive logarithm.
Any logarithmic sextic residue must be extracted from a subleading
mass/momentum term after the relevant local power counterterms are subtracted;
power counting alone neither sets that residue to zero nor fixes its sign.

There is also a genuine EFT obstruction. Because the Taylor expansion of
`phi^-2` has vertices with arbitrarily many scalar legs, `I_scalar` and hence
`D = I_scalar + 3` are unbounded. The Lean gate constructs such a family for
every proposed degree bound. Therefore the four marginal operators and the
relevant scalar potential operators are not a proof of all-order finite
counterterm closure. The candidate must be interpreted as an EFT with a
truncation order, unless a BRST/LL identity or a microscopic completion proves
cancellations of this tower.

At the manifest truncation `eta^6`, the local background-potential sector does
close on seven Taylor operators

```text
1, eta, eta^2, ..., eta^6.
```

`P0EFTJanusTruncatedPotentialCounterterms.lean` proves their cardinality,
their maximum scalar order, and that each coefficient has dimension
`3 - n/2`, so all seven are relevant or marginal. These coefficients are
independent EFT subtraction data around `phi = v`; the result does not claim
closure of operators with derivatives.

The candidate manifest now makes this projection machine-checkable:
`effective_action_projection = constant_scalar_background_potential` and
`maximum_external_derivative_order = 0`. The RG-ready verdict is refused if
that projection is absent. A kinetic or full derivative expansion therefore
requires a separate manifest extension and counterterm basis.

The manifest now separates the scheme used to extract universal logarithmic
residues (`d=3-2 epsilon`, MS) from the gauge-invariant higher-derivative/PV
plus MOM prescription used for finite physical matching. One-log covariance
and leading-beta invariance are marked `derived` by their Lean gates. The
numerical finite matching constant remains `not_yet_computed`; the audit keeps
the full match open rather than treating MS and MOM as identical conditions.

The minimal mixed graph has one internal scalar line, two loops and
superficial degree four. Its two linear `eta F^2` vertices and two Maxwell UV
propagators leave a background prefactor `v^-2`. Including the scalar
fluctuation mass, the degree-four logarithmic mass basis has three terms:

```text
v^-2 m_CS^4                 -> kappa^4 v^6,
v^-2 m_CS^2 m_eta^2         -> kappa^2 lambda6 v^6,
v^-2 (m_eta^2)^2            -> lambda6^2 v^6.
```

`P0EFTJanusMixedTwoLoopLogTarget.lean` proves that these are exactly the
nonnegative mass-power solutions of degree four and verifies all three sextic
background scalings. Thus the unknown mixed beta has candidate form
`C40 kappa^4 + C21 kappa^2 lambda6 + C02 lambda6^2`. This basis is the target
for the explicit tensor reduction below.

The transverse numerator has now been reduced explicitly. For Euclidean MCS
propagators and the two linear `eta A A` vertices it is

```text
N = p^2 q^2 + (p.q)^2 - 2 m_CS^2 (p.q).
```

Writing `(p+q)^2=s` and reducing modulo the three sunset denominators leaves
exactly `(m_eta^2)^2/4`: the candidate `kappa^4` and
`kappa^2 lambda6` pole residues cancel. With `m_eta^2=5 lambda6 v^4`, the two
gauge Wick contractions, the cumulant factor, and the sunset pole
`1/(64 pi^2 epsilon)`, the conditional mixed contribution is

```text
beta_lambda6^(mixed) = 75/(32 pi^2) lambda6^2.
```

Together with the pure-scalar result this gives the conditional non-LL result

```text
beta_lambda6^(non-LL) = 475/(32 pi^2) lambda6^2 + higher orders.
```

This coefficient is inserted into Callan--Symanzik without suppressing the LL
sector:

```text
b = 475 lambda6^2/(32 pi^2) + beta_LL
    - 3 gamma_sigma lambda6.
```

The Lean theorem proves positivity only when this complete beta term dominates
the anomalous-dimension term.

The executable audit records every intermediate residue and labels the result
conditional on the candidate Euclidean MCS Feynman rules. The universal sunset
pole and tensor-reduction strategy are cross-checked against
`arXiv:hep-th/9703121`; that paper studies charged scalar electrodynamics, so
its final beta function is not imported into this neutral-scalar candidate.

The executable RG audit now accepts the decomposition

```text
beta_total = beta_scalar + beta_mixed + beta_LL
```

and reports its residual independently of the Callan--Symanzik residual. This
prevents a supplied total beta from silently hiding an omitted mixed or LL
sector when all three components are claimed.

The executable `scripts/audit_janus_worldvolume_rg_data.py` consumes candidate
`beta_lambda6`, `gamma_sigma` and `lambda6`, checks Callan--Symanzik, the
stationary logarithm and finite-scheme covariance, and refuses closure when the
microscopic RG inputs are absent. It audits supplied coefficients; it does not
compute them.

The renormalization gate now also lists the microscopic data required before a
beta coefficient is meaningful: gauge normalization, representations, charges,
LL vertices, gauge fixing and ghosts, regulator, subtraction conditions and
loop order. These data are intentionally marked open rather than replaced by a
free numerical beta coefficient.

For the pure sextic contribution, connected six-point graph counting gives
three internal lines and two loops when two sextic vertices are used. A single
sextic vertex is only the tree interaction. `P0EFTJanusSexticLoopOrder.lean`
therefore proves that the `lambda6^2` contribution cannot be obtained from a
one-loop calculation. The manifest now requests two-loop coverage; gauge,
mixed and LL diagrams still require separate enumeration.

The pure-sextic two-loop graph has `L=2`, `I=3`, hence superficial degree
`3L-2I=0`: it is logarithmic. In dimensional continuation
`d=3-2 epsilon`, the sextic coupling has engineering dimension `4 epsilon`.
For

```text
lambda_B = mu^(4 epsilon)
  (lambda6 + A lambda6^2/epsilon + ...),
```

the conditional MS relation is `beta_lambda6 = 4 A lambda6^2 + ...`.
`P0EFTJanusSexticTwoLoopLog.lean` proves the counting and algebra, while the
audit keeps `A` unset. Computing it still requires a nonzero-momentum/IR
prescription, combinatorial normalization and subdivergence subtraction.

The massless two-loop master integral has now been reduced by two successive
one-loop convolutions to

```text
I_d(p) = (p^2)^(d-3)/(4 pi)^d
  Gamma(d/2-1)^3 Gamma(3-d) / Gamma(3d/2-3).
```

At `d=3-2 epsilon`, its pole residue is `1/(64 pi^2)`. The executable verifies
this limit symbolically. `P0EFTJanusSexticMasterIntegralPole.lean` then reduces
the quadratic beta coefficient to `W/(16 pi^2)`. For the repository
normalization `lambda6*phi^6/6`, explicit labeled-leg, expansion-factor and
internal-pairing counting gives `W=200`. Therefore the pure-scalar result is

```text
beta_lambda6^(scalar) = 25/(2 pi^2) lambda6^2 + higher orders.
```

The same counting gives `5/3` in the standard `g*phi^6/6!` normalization,
providing an independent normalization cross-check. Gauge and LL contributions
to the total beta function remain open.

This agrees with the two-loop normalization reviewed in
`arXiv:2502.07880`, which also confirms that odd loop orders have no UV poles
in dimensional regularization near three dimensions. The repository audit
checks the standard coefficient `5/(48 pi^2)` before converting to the
`lambda6/6` convention used here.

Substitution into the Callan--Symanzik coefficient gives the exact conditional
stability test

```text
3 gamma_sigma lambda6 < 25 lambda6^2/(2 pi^2)
  => b = beta_lambda6 - 3 gamma_sigma lambda6 > 0.
```

The corresponding Lean theorem does not set `gamma_sigma` to zero and does not
drop the still-open gauge or LL beta contributions.

For one sextic vertex, one `sigma = phi^2` insertion and two external legs,
half-edge and Euler counting force three internal lines and two loops. A finer
valence audit shows, however, that every such connected topology contains at
least one self-loop. These scaleless tadpoles vanish in the selected massless
dimensional-regularization prescription. Thus the pure-scalar contribution has
no order-`lambda6` MS term and may first occur as
`gamma_sigma = c_sigma lambda6^2 + ...`. Its Callan--Symanzik contribution is
then one order beyond the computed leading beta function. The gate proves that
for positive `c_sigma` the leading-log stability condition holds throughout
the weak-coupling interval

```text
0 < lambda6 < 25/(6 pi^2 c_sigma).
```

The coefficient `c_sigma` still requires the four-loop, two-sextic composite
insertion graphs; it is not inferred from the effective potential or set to
zero. Gauge and LL vertices can alter this ordering and remain separate.

For the non-LL gauge bubble, the one-loop MS question is now closed. In
`d=3-2 epsilon`, one-loop integrals with integer propagator powers contain
Gamma functions whose epsilon-zero arguments are half-integers, so their pole
residues vanish. The executable audit checks powers one through six and the
Lean gate converts the zero wavefunction pole into a zero one-loop anomalous
dimension contribution. This is an MS pole statement, not a claim that the
finite momentum-dependent two-point function vanishes.

The non-LL two-loop composite insertion is obtained by adding `J phi^2/2` and
differentiating the mixed sunset pole
`-(m_eta^2)^2/(256 pi^2 v^2 epsilon)`. Since
`m_eta^2 = J + 5 lambda6 v^4`, cancellation by the source counterterm gives

```text
delta J/J = 5 lambda6/(64 pi^2 epsilon),
gamma_sigma^(non-LL) = 5 lambda6/(16 pi^2).
```

Combining this with the conditional non-LL beta function yields

```text
b_non-LL = [475/32 - 3*(5/16)] lambda6^2/pi^2
         = 445 lambda6^2/(32 pi^2) > 0.
```

This closes the non-LL leading-log sign in the stated source convention. The
LL insertion and additive identity mixing tied to its zero modes remain open.
The integrated Callan--Symanzik gate isolates that remainder exactly:

```text
b = 445 lambda6^2/(32 pi^2) + beta_LL - 3 gamma_LL lambda6.
```

It proves positivity only under the explicit bound
`3 gamma_LL lambda6 < 445 lambda6^2/(32 pi^2) + beta_LL`.

`P0EFTJanusLeadingRGSchemeEnvelope.lean` separates two further issues. First,
for an analytic finite redefinition

```text
lambda6' = lambda6 + a lambda6^2,
```

the chain rule leaves the quadratic beta coefficient unchanged; scheme changes
start at cubic order. Thus `25/(2 pi^2)` is a leading-coefficient statement,
not a choice of finite sextic subtraction. Second, unresolved gauge and LL
contributions are retained as a lower bound `Delta_beta_min`. A sufficient
condition for a positive total logarithmic coefficient is

```text
3 gamma_max lambda6
  < 25 lambda6^2/(2 pi^2) + Delta_beta_min.
```

This envelope makes the remaining uncertainty explicit and cannot certify the
vacuum until bounds on the gauge/LL sector are supplied.

## Condensate-to-alpha map

Let the renormalized vacuum select

```text
v = <phi> > 0
```

and let the normalized LL charge be

```text
q_LL = c_q v^2,
```

where `c_q` is dimensionless and must be computed from the compact gauge-field
normalization.

Primitive flux then gives

```text
4 c_q v^2 A^2 = 1.
```

For `c_q = 1`:

```text
2 v A = 1,
A = 1/(2v).
```

Lean file:

```text
P0EFTJanusCondensateToAlphaMap.lean
```

## Dimensional transmutation

A Planck-anchored asymptotically free or nonperturbative sector may generate

```text
ell_dyn = ell_UV exp(X),
B X = 8 pi^2,
q_LL ell_dyn^2 = 1.
```

The primitive LL law then gives

```text
2 A = ell_dyn = ell_UV exp(X).
```

For `ell_UV = ell_P` and a diagnostic `A = 10^26 m`:

```text
X ~= 140,
B = beta0 g_UV^2 ~= 0.56.
```

Representative couplings are moderate:

```text
beta0 = 7  -> g_UV ~= 0.28,
beta0 = 11 -> g_UV ~= 0.23.
```

However the hierarchy is exponentially sensitive:

```text
d log A / d log g = -2 X ~= -280.
```

Therefore a fit of `g_UV` would be useless.  The microscopic theory must derive
`beta0`, fix `g_UV` through an integer level or bulk boundary law, and prove that
the vacuum is stable and unique.

Lean file:

```text
P0EFTJanusWorldvolumeRGTransmutation.lean
```

Executable audit:

```text
scripts/audit_janus_worldvolume_quantum_completion.py
```

## Parity anomaly

For unit-charge fermions in `2+1` dimensions, use the doubled-level convention

```text
2 k_eff = 2 k_bare + N_f.
```

An exactly vanishing integral effective level requires even `N_f`.  An odd
multiplicity obstructs a single-fold parity-symmetric zero-level theory.  A
Janus pair can instead carry opposite levels, so the total paired theory is PT
symmetric while each fold is anomalous.

Lean file:

```text
P0EFTJanusWorldvolumeParityAnomaly.lean
```

This discrete anomaly condition can select sectors and matter content.  It does
not by itself generate a length.

## Flat-direction no-go

An exactly flat positive vacuum family cannot select a unique scale.  The Lean
branch proves that if every positive condensate is a vacuum, `ExistsUnique`
fails.  Consequently a Bardeen--Moshe--Bander-like flat direction is not a
prediction until quantum corrections, a boundary condition or a stable gap
equation lifts the modulus.

Lean file:

```text
P0EFTJanusWorldvolumeVacuumSelection.lean
```

## Literature anchors and caveat

Relevant mechanisms exist in three-dimensional field theory:

- Maxwell--Chern--Simons scalar QED dimensional transmutation:
  `arXiv:hep-th/9509109`;
- large-N Chern--Simons scalar spontaneous scale breaking:
  `arXiv:1402.4196`;
- related fermionic large-N phase:
  `arXiv:1404.7477`.

But stability is a major caveat.  The proposed light dilaton phase was found
unstable in `arXiv:1605.00750`, and a recent next-to-leading large-N revisit of
the three-dimensional `phi^6` model reports the disappearance of the naive BMB
fixed line (`arXiv:2502.07880`).  Those papers motivate a mechanism; they do not
establish the Janus world-volume theory.

## Acceptance criteria

### Programme A frontier synthesis

The new Lean gate `P0EFTJanusProgramAFrontier` packages the current route:
the (2+1)D marginality check, a stable and scheme-independent nonzero vacuum,
paired anomaly cancellation, and derived UV transport are explicit hypotheses.
Under those hypotheses it proves, without fitting, `q_LL = c_q v^2` and
`2 c_q^{1/2} v A = 1`. It is a conditional closure gate, not evidence that
the four physical inputs have already been derived.

The quantum route closes only after all of the following are derived:

1. compact `U(1)` bundle and global flux operator;
2. anomaly-free paired matter content;
3. renormalized effective action;
4. bounded-below Hamiltonian or reflection-positive Euclidean theory;
5. unique stable nonzero condensate;
6. computed `beta0` or exact gap equation;
7. microscopic law fixing the UV coupling;
8. bulk-gravity UV anchor;
9. convention-independent charge normalization `c_q`;
10. controlled Lorentzian continuation;
11. no target cosmological scale inserted anywhere.

## Verdict

This is the only currently explicit mechanism in the branch capable of
producing a cosmological hierarchy without an integer of order `10^122`.
It is also highly sensitive and requires a genuinely new quantum theory.
The mathematical map from its derived RG data to `A` is closed; the quantum
dynamics selecting those data is the remaining research theorem.
