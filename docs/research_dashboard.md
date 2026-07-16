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
| **D0/D8** | global geometry and normal lift | the effective spacetime and throat quotients carry analytic manifold atlases, analytic PT diffeomorphisms, compactness, a closed analytic throat inclusion with injective differential and rank-one tangent quotient, plus a genuine analytic rank-one normal `VectorBundle` whose one-loop transition is `-id` and whose fibers are pointwise linearly equivalent to the differential normal quotients | prove `IsSmoothEmbedding`, assemble the pointwise normal equivalences smoothly, construct the non-null/null/joint strata and global Pin/root bundle |
| **D2** | focused twisted Dirac spectrum | green monopole eigenvalue/multiplicity law, `l2`, self-adjointness, compact resolvent and circle-reduced determinant | extend the circle model to the common-domain global Janus operator family |
| **D7** | heat kernel/effective action | green convergent heat trace, order-four Euler--Maclaurin remainder control, unconditional spectral/universal `a0/a2/a4` small-time matching, convergent `Z4` determinant, normalized-circle heat generator with maximal domain exactly `Dom(D²)=Dom(D∘D)`, and positive-time summable rank-one nuclear expansion with the spectral trace | abstract functional calculus/general trace-class API, then connect the closed local spectrum to the full field/ghost regulator and global Fredholm family |
| **D9/D11** | elliptic and natural-operator gates | green D9 symbol/BRST and D11 naturality/jet heads; typed P projection for diagonal metric, tangential gauge, U(1) ghost and matter, with proved non-surjectivity toward general D9 metric perturbations | normal/diffeomorphism-ghost/SpinC completion and concrete Janus Fredholm family |
| **D10** | Quillen/anomalies | green transgression/inflow, P--D7--D10 physical-`Z4` spectral bridge, literal finite P-period product-mode truncation with exact PT/regulator cancellation, concrete finite-mode holomorphic Fredholm family, and normalized infinite-circle family with common maximal domain, compact resolvent, Fredholm index zero, a topological determinant line and an explicit clutching-compatible Hermitian metric/flat connection in the chosen Fourier model | prove action/Hessian/mode/domain agreement, lift the circle model to the smooth global Janus family and identify its analytic Quillen/Bismut--Freed geometry, families-index curvature, eta holonomy and partition section |
| **P0/P-A** | reject shortcuts and define relative selection | causally compatible global diagonal Candidate-A domain with exact spectral frontier, controlled one-sided root limits and exact Minkowski-IFT/global-root overlap; global-field and complete induced-package variation on the same compact smooth D8 quotient; smooth/L²/PT/trace/Dirichlet spaces; unconditional finite `C∞` tangent generators, complete graph-`H¹` and norm-one throat-supported trace; fixed-frame global holonomic scalar action and variation; diagonal diffeomorphism action; actual LL throat action; explicit null domain `Theta ≠ 0` | intrinsic Sobolev identification and physical-volume trace, general tensorial Lorentz/gauge covariance, full curved Euler--flux action/PDE, same-action Hessian and constrained stability |
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
| P-A relative uniqueness | yes; PT-matched smooth D8 fields, weighted `Z^4` exactness, finite smooth tangent generators with complete first-jet graph `H¹` and throat-supported trace, causally compatible global diagonal root/domain/frontier with exact local/global overlap and one-sided limits, global Candidate-A plus induced-field variation, same-field/same-metric holonomic scalar action and fixed-metric variation, plus flat weak Euler pairing | intrinsic physical-volume Sobolev trace, general tensorial root/action, parent action, automatic domination, physical boundary flux and curved global PDE not derived |
| P-B anomaly logic | yes; positive-time compactness, physical `Z4` determinant and modewise P--D7--D10 inflow bridge, plus a holomorphic finite-mode determinant line and a normalized-circle canonical bounded-transform family that is self-adjoint, operator-norm continuous, Fredholm of index zero and has exact PT-opposite crossings, rank-one pointwise determinant fibers and a large-gauge endpoint transition | topology on the determinant family, global unbounded Janus Fredholm family/common domain, physical Hessian/regulator, Quillen/Bismut--Freed geometry and local/global anomaly not computed |
| P-C quadratic/polynomial Helmholtz | yes | nonlinear Euler source/cohomology open |
| P-D low-rank pairings/fusion | focused Lean head and Python audits green | global SpinC/PT/Z4/BRST classification open |
| P-E jet theorem architecture | focused head green | Janus specialization open |
| P-F pullback schema | focused head green | actual `K`, `J`, `H` and primitive open |
| finite normalization/counterterms | no | microscopic law open |
| stable vacuum | no | full renormalized action open |
| absolute scale | no | scale-breaking and charge compatibility open |

## Highest-priority theorem queue

The exhaustive dependency-aware checklist is
[`program_p_exhaustive_todo.md`](program_p_exhaustive_todo.md).

1. Construct the actual decorated mapping torus, throat embedding and normal-root/SpinC data.
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
