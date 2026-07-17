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
| **D0/D8** | global geometry and normal lift | analytic compact mapping-torus quotients, exact differential-normal `Diffeomorph` and strata, ambient tangent orientation/quadratic transition data, genuine Clifford Spin action, unconditional `Spin(4) → SO(4)` surjectivity/lifting function, and exact reduction of global lifting to one kernel-valued Čech class; normal principal `Pin⁻(1) ≃ Z4` bundle | prove global orientation, trivialize that Čech class and regularize the lifts, compare the normal lift, then extend to SpinC |
| **D2** | focused twisted Dirac spectrum | green monopole eigenvalue/multiplicity law, `l2`, self-adjointness, compact resolvent and circle-reduced determinant | extend the circle model to the common-domain global Janus operator family |
| **D7** | heat kernel/effective action | green convergent heat trace, order-four Euler--Maclaurin remainder control, unconditional spectral/universal `a0/a2/a4` small-time matching, convergent `Z4` determinant, normalized-circle heat generator with maximal domain exactly `Dom(D²)=Dom(D∘D)`, and positive-time summable rank-one nuclear expansion with the spectral trace | abstract functional calculus/general trace-class API, then connect the closed local spectrum to the full field/ghost regulator and global Fredholm family |
| **D9/D11** | elliptic and natural-operator gates | green D9 symbol/BRST and D11 naturality/jet heads; unconditional quotient/throat `so(3)` Koszul and LL completion; positive diagonal throat metrics with square-zero BRST; first finite field/antifield doublet and pairing | extend to general spacetime metrics, the full BV master equation, SpinC and a concrete Janus Fredholm family |
| **D10** | Quillen/anomalies | green transgression/inflow, P--D7--D10 physical-`Z4` spectral bridge, literal finite P-period product-mode truncation with exact PT/regulator cancellation, concrete finite-mode holomorphic Fredholm family, and normalized infinite-circle family with common maximal domain, compact resolvent, Fredholm index zero, a topological determinant line and an explicit clutching-compatible Hermitian metric/flat connection in the chosen Fourier model | prove action/Hessian/mode/domain agreement, lift the circle model to the smooth global Janus family and identify its analytic Quillen/Bismut--Freed geometry, families-index curvature, eta holonomy and partition section |
| **P0/P-A** | reject shortcuts and define relative selection | the global positive-diagonalizable root selector is continuous, locally IFT-stable and has the exact inverse-Sylvester derivative; a unified direct/raw spectral certificate selects exact roots across positive, real nonpositive and pure-nonreal regimes, with raw root existence unconditional on PSD and irreducible-quadratic loci and the three presentation/classification gaps reduced to exact non-PSD, outside-quadratic and Jordan residuals; canonical global intrinsic `(3,1)` metric with an unconditional finite nonzero quotient-volume/action; physical-volume graph `H¹` with exact FTC/Fubini, twisted latitude collar, throat pushforward, `L²` trace identity, exact finite-frame normal reconstruction, with coarea reduced through an exact quotient factorization to the pure `Measure.toSphere` inequality `S² × Ioc(0,1) → S³` after exact quotient/time-product reduction and frame control conditional only on tangent-lift continuity; a jointly analytic nontrivial complete D8 time action acts nontrivially on a full current independent-field configuration and has its exact set-theoretic orbit quotient; global scalar weak Euler/Jacobi and static-positive index-zero Fredholm/H¹ bridge | prove the single pure positive-latitude sphere-measure domination and tangent-lift continuity, identify intrinsic Sobolev sections, close the reduced raw residuals (or the three stronger Jordan bridges) and select the physical spectral domain, then nonlinear/BV and boundary stability |
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
| P-A relative uniqueness | yes; finite tangent generators and first-jet graph `H¹`, global continuous/IFT-stable positive-diagonalizable root with inverse-Sylvester derivative, one exhaustive selector for all supplied positive real Jordan partitions with Lorentz/strict witnesses, a canonical intrinsic global `(3,1)` metric, an unconditional finite nonzero quotient-volume/action, a jointly analytic complete D8 time flow acting nontrivially on a full current field configuration, global Candidate-A plus induced-field variation, and a static scalar ellipticity bridge | prove the physical-volume trace inequality, then raw-matrix Jordan presentation/nonpositive classification, parent action, physical boundary flux and curved global PDE |
| P-B anomaly logic | yes; positive-time compactness, physical `Z4` determinant and modewise P--D7--D10 inflow bridge, plus a holomorphic finite-mode determinant line and a normalized-circle canonical bounded-transform family that is self-adjoint, operator-norm continuous, Fredholm of index zero and has exact PT-opposite crossings, rank-one pointwise determinant fibers and a large-gauge endpoint transition | topology on the determinant family, global unbounded Janus Fredholm family/common domain, physical Hessian/regulator, Quillen/Bismut--Freed geometry and local/global anomaly not computed |
| P-C quadratic/polynomial Helmholtz | yes | nonlinear Euler source/cohomology open |
| P-D low-rank pairings/fusion | focused Lean head, global normal `Z4` root lines, abelian `U(1)^2` BRST, unconditional quotient/throat `so(3)` Koszul and LL closure, positive diagonal throat-metric BRST, and a first finite field/antifield doublet are green | general spacetime metric action, global SpinC and the full antifield/BV master complex |
| P-E jet theorem architecture | focused head green | Janus specialization open |
| P-F pullback schema | focused head green | actual `K`, `J`, `H` and primitive open |
| finite normalization/counterterms | no | microscopic law open |
| stable vacuum | no | full renormalized action open |
| absolute scale | no | scale-breaking and charge compatibility open |

## Highest-priority theorem queue

The exhaustive dependency-aware checklist is
[`program_p_exhaustive_todo.md`](program_p_exhaustive_todo.md).

1. Regularize the now-unconditional `SO(4)` Spin lifts into coherent atlas-wide Pin/SpinC transition data and trivialize their Čech defect; the rank-one normal principal lift is already constructed.
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
