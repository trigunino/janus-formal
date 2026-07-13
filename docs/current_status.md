# Janus Formal — Current Status

This is the canonical status document for readers who did not follow the research conversation. Detailed derivations remain in the program-specific documents; this file states what is integrated, what is validated and what remains open.

## 1. Repository integration status

Three stacked pull requests were merged on 12 July 2026:

```text
PR 1  main <- research/rp4-twisted-four-form-alpha
PR 2  research/rp4-twisted-four-form-alpha <- research/fundamental-geometry-d
PR 3  research/fundamental-geometry-d <- research/fundamental-geometry-dirac-spectral
```

Because they were initially merged from the bottom of the stack upward, the later Program D/P/P.E and D2 changes did not immediately propagate to `main`. Draft PR 5 then consolidated the complete stack and was merged into `main` on 12 July 2026 at merge commit

```text
d4b893b06983c5b65f481c24e2e71f2ba6ddd1ba.
```

`main` therefore contains the consolidated scientific history, canonical documentation, focused entry points and CI cleanup. No scientific files were discarded. Historical and exploratory branches remain available, while current claims are routed through this file.

Draft PR 6 advances Programs P-D/P-E beyond that consolidated baseline. It corrects the categorical jet statement, globalizes invariant pairings as modules over scalar invariants, adds formal action-groupoid and orbitwise-descent cores, proves the first concrete low-order structured-jet quotient `(B,F)`, constructs the pointwise adapted tangent/normal orthogonal splitting, and proves the pointwise connection-corrected identification `B = II` together with residual `O(T) x O(N)` equivariance. Until PR 6 is merged, these additions belong to its feature branch rather than to `main`.

## 2. Validation truth

All four workflows attached to the consolidation head passed:

```text
Programs D and P integration matrix       success
Program D2 Dirac spectral geometry       success
Program PE jet universality              success
Janus deep alpha completion              success
```

On the active PR 6 branch, the focused P-E workflow passes with the action-groupoid, orbitwise descent, concrete quotient, adapted orthogonal splitting, second-fundamental-form jet and residual-equivariance gates, together with the exact low-order jet-normal-form Python audit.

### Green focused Lean heads

```text
JanusFormal.Branches.FundamentalGeometryD
JanusFormal.Branches.FundamentalGeometryDiracSpectral
JanusFormal.Branches.FundamentalGeometryD7SpectralTheory
JanusFormal.Branches.FundamentalGeometryD8TopologyRepresentation
JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly
JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple
JanusFormal.Branches.FundamentalGeometryPEInvariantPairings
JanusFormal.Branches.FundamentalGeometryPEJetUniversality
JanusFormal.Branches.FundamentalGeometryPFCompatibilityHelmholtz
```

D9 and D11 remain gate collections without supported standalone entry files; they are not advertised as buildable heads.

### Green executable audits

The focused Python audits and tests pass for:

- fundamental geometry;
- holonomy determinant;
- heat-kernel effective action;
- D7 Seeley–DeWitt coefficients;
- invariant pairings;
- spinor pairings;
- D2 spectral geometry;
- P-E jet universality;
- low-order immersion/abelian-connection jet normal forms;
- the separate deep-alpha audit suite.

### Meaning of “green”

A green Lean head means that its imported formal statements compile. It does **not** mean that every abstract proposition stored in a status structure has been realized by a concrete geometric or physical construction. The evidence labels below remain essential.

## 3. Stable scientific architecture

```text
D0/D8  global mapping-torus and one-sided-throat topology
D2/D7  twisted Dirac, eta, heat kernel and determinant constraints
D9     gauge-fixed elliptic-symbol and BRST/ghost gate collection
D10    determinant-line, Quillen and anomaly interfaces
D11    natural-operator and finite-jet gate collection

P0     moduli-geometry no-go
P-A    relative action specification / parent-bulk reduction
P-B    anomaly consistency and discrete selection
P-C    Helmholtz inverse variational problem
P-D    isotropy-stratified pairings and invariant-coefficient modules
P-E    finite jets, action groupoids, orbitwise descent and jet reduction
P-F    compatibility-map pullbacks, Helmholtz and Noether identities

A/B/C  quantum scale, nonlinear junction and charge compatibility
E      observational falsification after theoretical closure
```

The numbering records research history, not a claim that every numbered package has a standalone Lean head.

## 4. Topology and Z4 verdict

For the current candidate

```text
J(T,rho) = (S3 x R)/((x,u) ~ (rho(x),u+T)),  T != 0,
```

the translated action is treated as a free smooth mapping-torus action, not as a reflection orbifold with a local singular fixed stratum. The equatorial throat target is `S2 x S1` and is one-sided in the nonorientable quotient.

The expected fundamental group is `Z`, not `Z4`. The quarter phases arise conditionally as a lift of the normal-line sign holonomy:

```text
one loop on the real normal line:       -1
complex square-root multipliers:        +i or -i
two lifted loops:                       -1
four lifted loops:                      +1
```

Thus `Z4` is a holonomy/lift phenomenon. The existence and physical assignment of the global Pin/normal-root bundle remain open geometric constructions. A square-root line or a `Z4` lift must be included as additional global data; it is not a canonical functor of the underlying line alone.

## 5. Program P — precise current position

Program P asks how one physical Janus action can be selected or reconstructed without fitting the desired radius or vacuum.

### P0 — moduli-geometry no-go

**Formalized in finite models:** a metric does not select a potential; a symplectic form does not select a Hamiltonian; a Kähler-like package still requires a moment map or functional.

**Conclusion:** geometry on moduli organizes dynamics but does not choose the action.

### P-A — relative universal property

**Formalized:** a quadratic Hessian determines an action only up to an affine functional. Hessian + critical point + reference value determine one normalized quadratic action. A quadratic parent-bulk problem produces a Schur-complement boundary action.

**Conclusion:** canonicity is relative to a complete specification or parent theory. Selecting the parent action and its boundary terms remains open.

### P-B — anomaly selection

**Formalized in anomaly proxies:** PT pairing cancels the parity-odd contribution. Anomaly cancellation is logically independent of parity-even Helmholtz integrability and does not fix even couplings or finite even counterterms. Discrete multiplicity arithmetic can be selected only after regulator data are fixed.

**Conclusion:** P-B is a consistency filter and possible discrete selector, not a complete dynamics principle.

### P-C — Helmholtz reconstruction

**Formalized:** in finite quadratic models, Hessian realizability is equivalent to formal self-adjointness. PT and one normalization remove the affine ambiguity. Polynomial finite models reconstruct a cubic potential from a Helmholtz-compatible Euler source.

**Open in Janus:** derive the complete nonlinear Euler–Lagrange source, prove gauge/Noether compatibility, all nonlinear Helmholtz conditions, variational-bicomplex obstruction vanishing, and classify boundary/null Lagrangians.

**Conclusion:** P-C is the strongest inverse route, but a Hessian at one background is not a proof of the global nonlinear action.

### P-D — invariant pairings, coefficients and isotropy strata

**Formalized/audited in low-rank models:**

- `Z4` neutrality forbids same-quarter quadratic masses and allows the conjugate `(+i,-i)` cross pairing;
- vector self-pairing is unique up to scale at a fixed representation fiber;
- scalar–vector, scalar–traceless and vector–traceless scalar pairings vanish;
- finite signed permutations leave two traceless-tensor quadratic forms, while a generic continuous rotation reduces them to the Frobenius pairing up to scale;
- the fundamental `Spin(3)=SU(2)` spinor has one invariant complex bilinear epsilon pairing and one invariant Hermitian pairing up to scale;
- repeated irreducible sectors leave multiplicity-space matrices;
- graded fusion rules distinguish allowed bilinear/trilinear channels and show that bilinear multiplicity one does not imply quartic uniqueness;
- invariant background-dependent pairing families are closed under multiplication by invariant scalar coefficients;
- an explicit finite Lean model proves that one pointwise pairing shape need not be one constant global multiple;
- a second finite Lean model proves that invariant-fiber freedom can jump between a free orbit and a higher-isotropy fixed stratum.

**Correction:** the pointwise space

```text
Hom_(H_b)(E_i,b tensor E_j,b, R)
```

classifies the fiberwise shape at a structured jet `b`. Global natural pairings form a module over the algebra of invariant scalar functions on the structured-jet base. Pointwise dimension one therefore does not imply one global coupling constant. A generic-stratum dimension also need not extend across singular isotropy strata.

**Open in Janus:** construct the actual structured jet groupoid, classify its orbit types and stabilizers, compute the invariant scalar algebra and global equivariant pairing module, and prove smooth extension across strata; then impose order, weight, Helmholtz and parent-law restrictions.

**Conclusion:** P-D converts arbitrary couplings into pointwise invariant spaces, a global coefficient-module problem and a stratified extension problem. Surviving normalizations still require a parent or microscopic law.

### P-E — finite jets, groupoids, reduction and the operator category

The original unrestricted polynomial-universality and naive representation-category claims have been corrected.

**Defensible architecture:**

```text
regular + local
  -> locally finite-jet                    [Peetre–Slovák interface]

finite-jet presentation + naturality
  <-> smooth equivariant evaluator         [formal action model]

operator composition
  -> holonomic prolongation to a higher jet

structured jet action
  -> action groupoid + isotropy

transitive orbit + isotropy-fixed value
  <-> equivariant section on that orbit

source/gauge orbit reduction
  -> (B,F)

pointwise adapted orthogonal splitting
  -> di = (id,0)

connection-corrected second jet
  -> B = II

residual orthogonal frames
  -> O(T) x O(N)-equivariance

invariance under orbit directions
  <-> unique factorization through reduced data
```

For ordinary natural and gauge-natural bundles, the finite-order classification by equivariant jet maps is a classical external theorem. Categorically, the morphisms are maps from jet prolongations and compose through the holonomic jet tower; they are not ordinary maps in one fixed linear representation category.

**Formalized in the repository:**

- naturality/equivariance and evaluator uniqueness in an abstract action model;
- local-versus-global order corrections and a smooth nonpolynomial counterexample;
- holonomic factorization of composite jet evaluators;
- identity, composition, inverse, orbit and stabilizer laws for an abstract action groupoid;
- an equivalence between equivariant sections on a transitive orbit and isotropy-fixed values in one chosen fiber;
- concrete second-order source-coordinate action from the chain rule;
- concrete abelian connection gauge action and orbit classification by curvature;
- combined quotient whose orbit fibers are exactly the level sets of `(B,F)`;
- unique factorization of every invariant observable through `(B,F)`;
- pointwise orthogonal splitting of a linear isometric derivative and its standard-inclusion form;
- connection-corrected second derivative and normal-projection definition of `II`;
- source- and ambient-coordinate two-jet invariance of the connection-corrected tensor;
- torsion-free symmetry of `II`;
- exact flat-adapted equality `B = II`;
- residual `O(T) x O(N)` action laws, symmetry preservation and equivariance of `B = II`;
- exact rational-matrix audits of the low-order normalizations.

These are genuine theorems for the declared pointwise and Taylor-coefficient models. They do not yet construct smooth manifold Levi-Civita connections, a smooth adapted frame germ, the oriented/SpinC lift or the complete differentiable Janus structured-jet groupoid.

**Open in Janus:**

- construct source and ambient Levi-Civita connections in the formal manifold environment;
- construct a smooth local germ of adapted orthonormal frames;
- prove the derivative-of-frame contribution and full varying-frame transformation law;
- reduce the residual group to the required oriented subgroup and construct its SpinC lift;
- attach the determinant-line connection;
- construct the finite-dimensional admissible structured-jet base and full differentiable groupoid;
- prove the higher-order jet-isomorphism theorem with Gauss–Codazzi–Ricci–Bianchi and formal-integrability constraints;
- classify orbit types and prove smooth extension between them;
- prove effective descent for the declared natural tensor, spinor, twist and ghost bundles;
- classify smooth equivariant maps on the resulting reduced stratified space.

This still does not imply polynomial dependence, ellipticity, a single global order, finite invariant generation, global topology or field-content selection.

### P-F — compatibility pullback bridge

**Formalized as an abstract schema:** if a compatibility map has linearization `J` and its target carries a self-adjoint Hessian/pairing `H`, then the pulled-back quadratic form `J^T H J` is self-adjoint and satisfies the quadratic Helmholtz condition. If the compatibility map is gauge invariant, the same pullback satisfies the linearized Noether identity. For nonlinear maps away from a target critical point, an additional gradient-times-second-jet term appears.

**Correction:** Gauss–Codazzi–Ricci–Bianchi compatibility alone does not imply Helmholtz. A target pairing/action is indispensable.

**Open in Janus:** construct the actual compatibility jet complex, target pairing and global variational primitive.

## 6. Program P conclusion

The current supported chain is:

```text
actual decorated Janus field/category data
  -> regular local finite-jet presentation
  -> structured jet groupoid and holonomic equivariant category
  -> orbitwise descent and low-order quotient reduction
  -> pointwise B = II and residual orthogonal equivariance
  -> oriented/SpinC lift and smooth adapted frames
  -> residual tensor representations and isotropy strata
  -> invariant coefficient and pairing modules
  -> compatible Euler family
  -> Helmholtz + Noether
  -> anomaly consistency
  -> global action class modulo boundary/null terms
  -> microscopic normalization and finite counterterms
  -> renormalized effective action
  -> unique stable vacuum
  -> absolute scale
```

The repository has green focused formal and executable layers through the abstract/finitely modeled Helmholtz, pairing, action-groupoid, orbitwise-descent, concrete low-order quotient, pointwise second-fundamental-form and compatibility stages. It does **not** yet contain the smooth Janus structured-jet groupoid, a SpinC residual lift, a higher-order jet-isomorphism theorem, the concrete global Janus Euler family, a selected parent action, a scheme-independent effective potential, a unique vacuum or an absolute no-fit scale.

## 7. Immediate priorities

### Repository

1. keep this status document synchronized with merged PR and CI state;
2. retain focused CI rather than one opaque all-program job;
3. add D9/D11 standalone heads only after their gate collections are integrated and buildable;
4. keep historical documents, but route current status claims through this file.

### Scientific Program P

1. construct smooth local adapted orthonormal frame germs;
2. formalize source and ambient Levi-Civita connections and connect them to the pointwise jet coefficients;
3. prove the varying-frame two-jet transformation law;
4. construct the oriented residual group and the exact SpinC lift, including determinant-line data;
5. construct the finite-dimensional smooth structured-jet base and differentiable groupoid;
6. extend to one covariant derivative of `II` and derive the first Codazzi constraint;
7. prove the higher-order structured jet-isomorphism theorem and formal-integrability constraints;
8. classify orbit types, stabilizers, invariant scalar functions and global pairing modules, including cross-stratum extension;
9. construct the concrete compatibility map `K`, the nonlinear Euler family and prove Helmholtz/Noether conditions;
10. compute variational cohomology, anomalies, normalization and finite counterterms without observed-radius input.

## 8. Canonical navigation rule

- This file is the current truth.
- `PROGRAM.md` is the stable high-level map.
- `program_master_roadmap.md` is the detailed dependency tree.
- `program_pe_categorical_jet_equivalence.md` records the corrected categorical theorem.
- `program_pe_structured_jet_reduction.md` records the action-groupoid and quotient program.
- `program_pe_low_order_structured_background.md` records the first exact `(B,F)` quotient.
- `program_pe_second_fundamental_form_jet.md` records the pointwise `B = II` theorem and residual orthogonal equivariance.
- `program_pd_global_pairing_modules.md` records the pointwise-to-global coupling correction.
- program-specific documents contain derivations and theorem queues.
- `janus_branch_registry.md` lists supported heads and explicitly labels gate-only collections.
