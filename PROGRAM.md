# Janus Research Program

This is the stable high-level map of the repository. The canonical current status, including CI and merge integration, is maintained in:

```text
docs/current_status.md
```

The detailed dependency graph is maintained in:

```text
docs/program_master_roadmap.md
```

## Scientific target

Derive the Janus geometry, field content, action, charge normalization and cosmological scale from explicit mathematical and physical laws, without importing an observed value of `H0`, `alpha`, a bridge radius or an equivalent hidden scale.

The positive length denoted `alpha^2` in the 2018 exact solution is called `A = alphaSquaredLength` in the current research branches.

## Evidence labels

| Code | Meaning |
| --- | --- |
| **T** | theorem or exact algebra checked in Lean |
| **X** | executable Python/symbolic audit |
| **C** | conditional theorem from explicit assumptions |
| **I** | analytic/geometric theorem represented by an interface |
| **N** | no-go result or correction |
| **O** | open theorem or construction |

A theorem about an abstract closure structure is not evidence that its physical inputs have been constructed.

## Canonical program map

| Program | Purpose | Current role | Canonical entry |
| --- | --- | --- | --- |
| **D0/D8** | mapping torus, throat, normal line, Pin/SpinC and `Z4` lift | global topology and bundle seed | `FundamentalGeometryD`, `FundamentalGeometryD8TopologyRepresentation` |
| **D2** | monopole-twisted Dirac spectrum, eta and geometric ratios | strongest focused spectral head | `FundamentalGeometryDiracSpectral` |
| **D7** | heat kernel, winding determinants and scale no-go results | local/nonlocal spectral layer | `FundamentalGeometryD7SpectralTheory` |
| **D9** | de Rham/Maxwell, metric, normal, Dirac and ghost symbols | gate collection; no stable standalone head yet | `FundamentalGeometryD9ImmersedSpinCEllipticComplex/Gates/` |
| **D10** | Quillen/determinant-line and anomaly interfaces | quantization/anomaly layer | `FundamentalGeometryD10QuillenAnomaly` |
| **D11** | natural bundles, symbols and jet interfaces | gate collection; no stable standalone head yet | `FundamentalGeometryD11NaturalImmersionOperators/Gates/` |
| **P0/P-A/P-B/P-C** | no-go, relative action selection, anomaly filter and Helmholtz reconstruction | variational core | `FundamentalGeometryPVariationalPrinciple` |
| **P-D** | pointwise invariant pairings, invariant scalar algebra and global coupling modules | representation-theory filter with corrected globalization | `FundamentalGeometryPEInvariantPairings` |
| **P-E** | locality, finite jets, equivariant evaluators and holonomic composition | corrected local natural-operator category | `FundamentalGeometryPEJetUniversality` |
| **P-F** | compatibility-map pullbacks, Helmholtz and Noether identities | bridge from geometry to a variational complex | `FundamentalGeometryPFCompatibilityHelmholtz` |
| **A** | quantum world-volume and dimensionful scale generation | absolute-scale candidate | `WorldvolumeQuantumAlpha` |
| **B** | nonlinear bimetric action and PT junction | parent/classical action candidate | `NonlinearBimetricJunctionAlpha` |
| **C** | equality of bulk, throat, LL and bridge charge units | normalization compatibility | `AlphaDeepCompletionMatrix` |
| **E** | SN/BAO/CMB/lensing/structure tests | falsification after theory closure | branch-specific runners |

## Corrected dependency graph

```text
D0/D8 global decorated geometry
  -> D2/D7 spectral constraints
  -> D9/D11 natural bundles, symbols and local operators
  -> P-E regular-local finite-jet presentation
  -> structured-jet groupoid, descent and holonomic morphism category
  -> P-D pointwise invariant spaces plus invariant coefficient modules
  -> P-F compatibility-map pullback and Noether bridge
  -> P-C nonlinear Helmholtz / variational cohomology
  -> P-B anomaly consistency
  -> P-A parent or microscopic action selection
  -> finite normalization and counterterms
  -> renormalized action and stable vacuum
  -> A/B/C absolute-scale closure
  -> E observational tests
```

This is a dependency graph, not a completion claim. Some arrows are formal schemas or analytic interfaces rather than constructed Janus objects.

## Topology and Z4 correction

For

```text
J(T,rho) = (S3 x R)/((x,u) ~ (rho(x),u+T)),  T != 0,
```

the translation makes the candidate action fixed-point free. The current model is treated as a smooth nonorientable mapping torus, not as an orbifold with a singular equatorial fixed locus.

The expected fundamental group is `Z`, not `Z4`. The quarter phase is a possible lift of the one-sided normal-line sign:

```text
normal holonomy:  -1
square-root lift: +i or -i
four lifted loops: identity
```

Thus `Z4` is a lift/holonomy structure. It does not by itself select rank five, a field representation or a physical action. A square-root line or `Z4` lift must be supplied and globally constructed; it is not an automatic functor of the underlying line bundle.

## Program P summary

```text
P0   moduli metric/symplectic/Kähler data do not select an action
P-A  action uniqueness is relative to Hessian, critical point, normalization
P-B  anomaly cancellation is an independent consistency/discrete filter
P-C  Helmholtz reconstructs an action class from a compatible Euler source
P-D  pointwise invariant Hom-spaces classify fiberwise pairing shapes;
     global pairings form modules over invariant scalar functions
P-E  regular local natural operators are locally smooth finite-jet evaluators;
     categorical composition uses holonomic prolongation
P-F  a self-adjoint target pairing pulls back to Helmholtz/Noether structure
```

The ordinary natural/gauge-natural categorical theorem is classical, but the Janus specialization remains conditional on a structured SpinC-immersion jet groupoid, effective descent and a jet-normal-form theorem. Pointwise multiplicity one does not imply one constant global coupling without controlling the invariant scalar coefficient algebra.

The shortest honest route is:

```text
actual Janus category and field space
  -> adapted structured-jet groupoid and finite-order descent
  -> holonomic equivariant operator category
  -> isotropy-stratified invariant spaces and coefficient modules
  -> concrete compatible Euler family
  -> nonlinear Helmholtz + Noether + variational cohomology
  -> anomaly consistency
  -> parent/microscopic normalization and finite counterterms
  -> selected renormalized action.
```

## Navigation

1. `README.md`
2. `PROGRAM.md`
3. `docs/current_status.md`
4. `docs/program_master_roadmap.md`
5. `docs/program_p_variational_principle.md`
6. `docs/program_pe_jet_universality_proof.md`
7. `docs/program_pe_categorical_jet_equivalence.md`
8. `docs/program_pe_invariant_pairings.md`
9. `docs/program_pd_global_pairing_modules.md`
10. `docs/janus_branch_registry.md`

## Repository rule

Every new proposal must record:

- program and stable ID;
- evidence level;
- dependencies;
- theorem, conditional result, executable audit or no-go;
- remaining geometric/analytic/physical atom;
- falsification or failure criterion;
- Lean/Python target.
