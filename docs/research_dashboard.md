# Janus Research Dashboard

This is the operational scorecard. The authoritative prose status is [`current_status.md`](current_status.md); the full dependency tree is [`program_master_roadmap.md`](program_master_roadmap.md).

## Evidence legend

| Code | Meaning |
| --- | --- |
| **T** | theorem/exact algebra checked in Lean |
| **X** | executable audit |
| **C** | conditional theorem |
| **I** | analytic/geometric interface |
| **N** | no-go/correction |
| **O** | open construction |

## Portfolio

| Program | Role | Strongest current result | Terminal blocker |
| --- | --- | --- | --- |
| **D0/D8** | global geometry and normal lift | analytic compact mapping-torus quotients, exact total differential-normal `Diffeomorph` and strata, real ambient tangent orientation cocycle, positive nondegenerate model quadratic form with transported transition isometries, normal principal `Pin⁻(1) ≃ Z4` bundle | instantiate global orthonormal compatibility, compare ambient and normal orientation cocycles, then construct ambient tangent Pin/SpinC principal bundles |
| **D2** | focused twisted Dirac spectrum | green monopole eigenvalue/multiplicity law, `l2`, self-adjointness, compact resolvent and circle-reduced determinant | extend the circle model to the common-domain global Janus operator family |
| **D7** | heat kernel/effective action | green convergent heat trace, order-four Euler--Maclaurin remainder control, unconditional spectral/universal `a0/a2/a4` small-time matching, convergent `Z4` determinant, normalized-circle heat generator with maximal domain exactly `Dom(D²)=Dom(D∘D)`, and positive-time summable rank-one nuclear expansion with the spectral trace | abstract functional calculus/general trace-class API, then connect the closed local spectrum to the full field/ghost regulator and global Fredholm family |
| **D9/D11** | elliptic and natural-operator gates | green D9 symbol/BRST and D11 naturality/jet heads; typed P projection for diagonal metric, tangential gauge, U(1) ghost and matter; true smooth tangent diffeomorphism ghost with a linearized scalar BRST complex and a proof that ordinary real ghosts cannot realize the nonlinear quadratic term; local smooth D8-normal-section bridge with exact `-1 = Z4²` transition | graded nonlinear diffeomorphism-BRST/SpinC completion, canonical global normal description and concrete Janus Fredholm family |
| **D10** | Quillen/anomalies | green transgression/inflow, P--D7--D10 physical-`Z4` spectral bridge, literal finite P-period product-mode truncation with exact PT/regulator cancellation, concrete finite-mode holomorphic Fredholm family, and normalized infinite-circle family with common maximal domain, compact resolvent, Fredholm index zero, a topological determinant line and an explicit clutching-compatible Hermitian metric/flat connection in the chosen Fourier model | prove action/Hessian/mode/domain agreement, lift the circle model to the smooth global Janus family and identify its analytic Quillen/Bismut--Freed geometry, families-index curvature, eta holonomy and partition section |
| **P0/P-A** | reject shortcuts and define relative selection | diagonal/positive-diagonalizable roots and one signature-certified, Sylvester-regular 4D Lorentz-Jordan stratum; global scalar weak Euler/Jacobi, static-positive index-zero Fredholm realization and holonomic-frame-to-uniform-ellipticity `H¹` bridge; linearized BRST; PT-covariant Robin and differential-LL H¹/Riesz/Fredholm | classify/glue all admissible root strata, instantiate the uniformly bounded true-frame/holonomic transition, descend the general tensor/action and physical-volume Sobolev trace, then nonlinear/BV and boundary stability |
| **P-B** | anomaly consistency | independent of Helmholtz; compact D7 heat blocks, convergent `Z4` determinant and modewise P--D7--D10 inflow bridge | common Fredholm family/regulator, full field/ghost content and global anomaly |
| **P-C** | inverse variational problem | green finite Helmholtz and polynomial reconstruction models | concrete nonlinear Janus Euler source and variational cohomology |
| **P-D** | invariant pairings | green low-rank pairing, spinor, fusion and `Z4` neutrality head | exact global symmetry category, multiplicity spaces and normalizations |
| **P-E** | finite jets/equivariance | green corrected jet-universality head | concrete Janus jet group/bundles and elliptic classification |
| **P-F** | compatibility pullback | green `J^T H J` Helmholtz/Noether schema | actual compatibility complex and target pairing |
| **A/B/C** | scale, junction and charge compatibility | deep-alpha workflow green; advanced conditional chains | selected action, stable vacuum and common unit |
| **E** | observations | diagnostics only | native predictions from a closed theory |

## CI scorecard

| Entry | Current label |
| --- | --- |
| `FundamentalGeometryD` | **green** |
| `FundamentalGeometryDiracSpectral` | **green** |
| `FundamentalGeometryD7SpectralTheory` | **green** |
| `FundamentalGeometryD8TopologyRepresentation` | **green** |
| `FundamentalGeometryD9ImmersedSpinCEllipticComplex` | **green** |
| `FundamentalGeometryD10QuillenAnomaly` | **green** |
| `FundamentalGeometryPVariationalPrinciple` | **green** |
| `FundamentalGeometryPEInvariantPairings` | **green** |
| `FundamentalGeometryPEJetUniversality` | **green** |
| `FundamentalGeometryPFCompatibilityHelmholtz` | **green** |
| deep-alpha completion workflow | **green** |
| `FundamentalGeometryD11NaturalImmersionOperators` | **green** |

## Program P scorecard

| Layer | Closed in abstract/finite models | Concrete Janus closure |
| --- | --- | --- |
| P0 moduli no-go | yes | applies generally |
| P-A relative uniqueness | yes; finite tangent generators and first-jet graph `H¹`, global diagonal and positive-diagonalizable roots, one non-diagonalizable 4D Lorentz-Jordan family with exact `(3,1)` congruence and Sylvester inverse, global Candidate-A plus induced-field variation, and a static scalar holonomic-frame ellipticity bridge | instantiate continuous uniformly bounded true-frame coefficients, intrinsic physical-volume Sobolev trace, general tensorial root/action and Jordan classification/gluing, parent action, physical boundary flux and curved global PDE |
| P-B anomaly logic | yes; positive-time compactness, physical `Z4` determinant and modewise P--D7--D10 inflow bridge, plus a holomorphic finite-mode determinant line and a normalized-circle canonical bounded-transform family that is self-adjoint, operator-norm continuous, Fredholm of index zero and has exact PT-opposite crossings, rank-one pointwise determinant fibers and a large-gauge endpoint transition | topology on the determinant family, global unbounded Janus Fredholm family/common domain, physical Hessian/regulator, Quillen/Bismut--Freed geometry and local/global anomaly not computed |
| P-C quadratic/polynomial Helmholtz | yes | nonlinear Euler source/cohomology open |
| P-D low-rank pairings/fusion | focused Lean head, global normal `Z4` root lines, abelian `U(1)^2` BRST and a true tangent-ghost linearization are green | global SpinC and nonlinear diffeomorphism/nonabelian/BV classification open |
| P-E jet theorem architecture | focused head green | Janus specialization open |
| P-F pullback schema | focused head green | actual `K`, `J`, `H` and primitive open |
| finite normalization/counterterms | no | microscopic law open |
| stable vacuum | no | full renormalized action open |
| absolute scale | no | scale-breaking and charge compatibility open |

## Highest-priority theorem queue

The exhaustive dependency-aware checklist is
[`program_p_exhaustive_todo.md`](program_p_exhaustive_todo.md).

1. Extend the proved real ambient tangent orientation cocycle through quadratic reduction to the ambient Pin/SpinC decoration; the rank-one normal principal lift is already constructed.
2. Specify the exact Janus field space and metric formulation without double counting.
3. Build the concrete compatibility map `K`, its linearization `J` and the target pairing `H`.
4. Construct the adapted SpinC/PT/Z4/BRST jet symmetry and natural bundles.
5. Classify invariant pairings and smooth equivariant evaluators globally.
6. Derive the full Euler source and prove nonlinear Helmholtz/Noether conditions.
7. Compute variational cohomology, boundary terms and anomalies in one regulator.
8. Derive action normalization and finite counterterms microscopically.
9. Compute the full effective action and prove one scheme-independent stable vacuum.
10. Close bulk/throat/LL/bimetric charge units and the absolute scale.

## Update rule

Every new result must update:

- its program ID and evidence label;
- the canonical status file when it changes the frontier;
- the branch registry when it changes build support;
- the relevant focused CI target.

Do not use percentage-complete claims as substitutes for named theorems and blockers.
