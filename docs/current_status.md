# Janus Formal — Current Status

This is the canonical status document for readers who did not follow the research conversation. Detailed derivations remain in the program-specific documents; this file states what is integrated, what is validated and what remains open.

## 1. Repository integration status

The consolidated scientific stack was merged into `main` on 12 July 2026 through PR 5 at commit

```text
d4b893b06983c5b65f481c24e2e71f2ba6ddd1ba.
```

Draft PR 6 advances Programs P-D/P-E beyond that baseline. It contains:

- the corrected categorical jet statement;
- invariant pairing modules and isotropy-stratification locks;
- action-groupoid and orbitwise-descent cores;
- the first concrete low-order structured-jet quotient `(B,F)`;
- the pointwise adapted tangent/normal orthogonal splitting;
- the pointwise connection-corrected identity `B = II`;
- residual `O(T) x O(N)` equivariance;
- smooth tangent and normal projector fields;
- a smooth local adapted orthonormal frame constructed by projected normal seeds and Gram--Schmidt.

Until PR 6 is merged, these additions belong to branch

```text
agent/categorical-jets-and-pairing-modules
```

rather than to `main`.

## 2. Validation truth

The consolidated `main` workflows are green. On PR 6, the focused head

```text
JanusFormal.Branches.FundamentalGeometryPEJetUniversality
```

also builds successfully with S5.1 and S5.2 included.

The S5 code was validated at commit

```text
700609f4dfa8e40d188601513a174be6c6a88e28
```

by workflow **Program PE jet universality**, run `29234536119`:

```text
Lean build                    success
P-E executable audits        success
focused Python tests         success
```

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

D9 and D11 remain gate collections without supported standalone entry files.

A green Lean head means that its imported statements compile. It does **not** mean that every proposition stored in an abstract status structure has been realized by a concrete geometric or physical construction.

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
P-E    finite jets, action groupoids, reduction and adapted frames
P-F    compatibility-map pullbacks, Helmholtz and Noether identities

A/B/C  quantum scale, nonlinear junction and charge compatibility
E      observational falsification after theoretical closure
```

## 4. Topology and Z4 verdict

For the candidate

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

Thus `Z4` is a holonomy/lift phenomenon. A square-root line or `Z4` lift is extra global data; it is not a canonical functor of the underlying line bundle.

## 5. Program P — precise position

### P0 — moduli-geometry no-go

**Formalized:** a metric does not select a potential; a symplectic form does not select a Hamiltonian; a Kähler-like package still requires a moment map or functional.

### P-A — relative action selection

**Formalized:** a quadratic Hessian fixes an action only up to an affine functional. Hessian + critical point + reference value determine a normalized quadratic action. A quadratic parent-bulk problem yields a Schur-complement boundary action.

**Open:** select the actual Janus parent action and boundary data.

### P-B — anomaly filter

**Formalized in finite proxies:** PT pairing cancels the parity-odd contribution. Anomaly cancellation is independent of parity-even Helmholtz integrability and does not fix even couplings or finite even counterterms.

### P-C — Helmholtz reconstruction

**Formalized:** finite quadratic Hessian realizability is equivalent to formal self-adjointness; finite polynomial Helmholtz conditions reconstruct a cubic potential.

**Open:** derive the complete nonlinear Janus Euler source, Noether identities, nonlinear Helmholtz conditions, variational cohomology and boundary/null terms.

### P-D — invariant pairings and coefficient modules

**Formalized/audited:**

- `Z4` charge neutrality and PT selection rules;
- low-rank scalar/vector/tensor and spinor pairing dimensions;
- residual multiplicity-space matrices;
- closure under multiplication by invariant scalar coefficient functions;
- a counterexample showing that pointwise multiplicity one does not imply one constant global coupling;
- a counterexample showing invariant-fiber dimensions can jump between isotropy strata.

The correct global object is an equivariant pairing module over the invariant scalar algebra, not merely a pointwise Hom-space.

### P-E — finite jets, reduction and smooth adapted frames

The supported chain is now:

```text
regular + local
  -> locally finite-jet

finite-jet presentation + naturality
  <-> smooth equivariant evaluator

operator composition
  -> holonomic prolongation

structured action
  -> action groupoid + orbitwise descent

source/gauge quotient
  -> (B,F)

pointwise orthogonal splitting
  -> di = (id,0)

connection-corrected second jet
  -> B = II

smooth tangent frame
  -> smooth P_T and P_N

projected normal seeds + Gram--Schmidt
  -> smooth local adapted orthonormal frame

residual frames
  -> O(T) x O(N)-equivariance
```

#### P-E results proved in Lean

- finite-jet naturality/equivariance and evaluator uniqueness;
- holonomic factorization of composite operators;
- action-groupoid laws, orbits and stabilizers;
- orbitwise descent from isotropy-fixed values;
- concrete second-order source action from the chain rule;
- concrete abelian connection gauge action and classification by curvature;
- exact combined quotient by `(B,F)`;
- universal factorization of invariant observables through `(B,F)`;
- pointwise tangent/normal orthogonal splitting;
- connection-corrected definition and coordinate invariance of `II`;
- exact flat-adapted identity `B = II`;
- residual `O(T) x O(N)` equivariance;
- joint smoothness of explicit tangent and normal projectors;
- projector identities and smooth projected normal seeds;
- openness and local persistence of normal-seed independence;
- smoothness of finite Gram--Schmidt on the independent locus;
- construction of a smooth orthonormal normal frame;
- tangent-normal cross orthogonality;
- existence of an open neighborhood carrying a smooth adapted orthonormal basis.

#### Exact boundary

S5.1 and S5.2 are closed **in a finite-dimensional local coordinate model**. The repository has not yet packaged these functions as actual sections and endomorphisms of the source and pulled-back ambient tangent bundles over manifolds. Mathlib supplies smooth local frames from bundle trivializations, but not yet the planned general orthonormal-frame bundle API; the required coordinate Gram--Schmidt smoothness was therefore proved directly.

### P-F — compatibility pullback

**Formalized:** a self-adjoint target Hessian pulls back through a compatibility-map linearization to a self-adjoint quadratic Helmholtz operator; gauge invariance gives the linearized Noether identity.

**Open:** construct the actual Janus compatibility complex, target pairing and global variational primitive.

## 6. Program P conclusion

```text
actual decorated Janus field/category data
  -> regular local finite-jet presentation
  -> structured jet groupoid and holonomic equivariant category
  -> low-order quotient (II,F)
  -> smooth local adapted orthonormal frame
  -> varying-frame two-jet law
  -> oriented/SpinC lift and determinant-line data
  -> higher reduced jets and integrability identities
  -> invariant coefficient and pairing modules
  -> compatible Euler family
  -> Helmholtz + Noether + anomaly consistency
  -> action class and microscopic normalization
  -> stable vacuum and absolute scale
```

The repository does **not** yet contain the full smooth Janus structured-jet groupoid, a SpinC residual lift, the higher-order jet-isomorphism theorem, a concrete global Janus Euler family, a selected parent action, a unique vacuum or an absolute no-fit scale.

## 7. Remaining lemma queue

S5.1 and S5.2 are closed in the coordinate model. The next open lemmas are:

1. **S5.3 — varying-frame two-jet lemma.** Prove that derivatives of the smooth adapted frame generate exactly the source and ambient connection corrections in the already formalized pointwise covariant-second-derivative formula.
2. **Bundle-packaging lemma.** Instantiate the tangent frame from an immersion chart and package the tangent/normal projectors and adapted frame as morphisms and sections of actual manifold vector bundles.
3. **Overlap lemma.** Prove compatibility of the local constructions under changes of tangent and ambient bundle trivializations.
4. **Oriented residual reduction lemma.** Reduce `O(T) x O(N)` to the correct oriented subgroup or fiber product.
5. **SpinC lift lemma.** Construct the exact central extension/fiber product and its actions on tangent, normal, spinor and determinant-line sectors.
6. **Determinant-connection compatibility lemma.** Identify the reduced curvature `F` with the curvature of the SpinC determinant-line connection.
7. **First covariant-derivative reduction lemma.** Classify the next jet order by `nabla II`, `nabla F` and ambient curvature data.
8. **Gauss--Codazzi--Ricci--Bianchi lemma.** Characterize the realizable reduced jets by their algebraic and differential identities.
9. **Higher-order jet-isomorphism theorem.** Classify all finite structured jets by curvature data and covariant derivatives subject to integrability.
10. **Stratified equivariant extension lemma.** Characterize smooth extension across higher-isotropy strata.
11. **Finite-generation/module lemma.** Under a proved compact/reductive residual action and a fixed polynomial/weight class, prove finite generation of invariant and equivariant modules.
12. **Concrete Helmholtz lemma.** Insert the resulting finite operator basis into the nonlinear Helmholtz system.

## 8. Immediate priorities

1. prove S5.3, the varying-frame two-jet transformation law;
2. package S5.1/S5.2 in actual manifold vector bundles and local frames;
3. construct the oriented residual group and SpinC lift;
4. attach the determinant-line connection;
5. construct the finite-dimensional smooth structured-jet groupoid;
6. extend to `nabla II`, `nabla F` and Gauss--Codazzi--Ricci--Bianchi;
7. prove the higher-order structured jet-isomorphism theorem;
8. classify invariant modules and the concrete Helmholtz submodule.

## 9. Canonical navigation

- `PROGRAM.md` — stable high-level map;
- `docs/program_master_roadmap.md` — detailed dependency tree;
- `docs/program_pe_categorical_jet_equivalence.md` — corrected categorical theorem;
- `docs/program_pe_structured_jet_reduction.md` — action-groupoid and quotient program;
- `docs/program_pe_low_order_structured_background.md` — exact `(B,F)` quotient;
- `docs/program_pe_second_fundamental_form_jet.md` — pointwise `B = II` theorem;
- `docs/program_pe_smooth_adapted_frames.md` — S5.1/S5.2 projectors and adapted frames;
- `docs/program_pd_global_pairing_modules.md` — pointwise-to-global coupling correction;
- `docs/janus_branch_registry.md` — supported heads and gate-only collections.
