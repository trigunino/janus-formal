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
| **D0/D8** | global geometry and normal lift | analytic compact mapping-torus quotients, exact differential-normal `Diffeomorph`, smooth bundle atlas and causal/joint stratification from any continuous intrinsic normal quadratic form; global product derivative equivalence with exact canonical latitude product/ambient image `(e₀, 0)`, intrinsic cover Lorentz square `1`, fixed-throat orthogonality and spacelike/non-null classification; ambient tangent orientation/quadratic transition data, genuine Clifford Spin action, unconditional `Spin(4) → SO(4)` surjectivity/lifting function, and exact reduction of global lifting to one kernel-valued Čech class; normal principal `Pin⁻(1) ≃ Z4` bundle | prove the local regular projection lemma and descend the cover normal calculation to the global quotient; prove global orientation, trivialize the Čech class and regularize the lifts, then extend to SpinC |
| **D2** | focused twisted Dirac spectrum | green monopole eigenvalue/multiplicity law, `l2`, self-adjointness, compact resolvent and circle-reduced determinant | extend the circle model to the common-domain global Janus operator family |
| **D7** | heat kernel/effective action | green convergent heat trace, order-four Euler--Maclaurin remainder control, unconditional spectral/universal `a0/a2/a4` small-time matching, convergent `Z4` determinant, normalized-circle heat generator with maximal domain exactly `Dom(D²)=Dom(D∘D)`, and positive-time summable rank-one nuclear expansion with the spectral trace | abstract functional calculus/general trace-class API, then connect the closed local spectrum to the full field/ghost regulator and global Fredholm family |
| **D9/D11** | elliptic and natural-operator gates | green D9 symbol/BRST and D11 naturality/jet heads; unconditional quotient/throat `so(3)` Koszul and LL completion; finite `32`-dimensional BV master model promoted to smooth throat and true-spacetime fields, then coupled to the actual smooth positive diagonal/log metric cone with ghosts, antifields, nonzero action, pointwise/integrated CME and unconditional PT covariance | extend to general non-diagonal spacetime tensor metrics, derivative-dependent and arbitrary nonlocal/completed functionals, SpinC and a concrete Janus Fredholm family |
| **D10** | Quillen/anomalies | green transgression/inflow, P--D7--D10 physical-`Z4` spectral bridge, literal finite P-period product-mode truncation with exact PT/regulator cancellation, concrete finite-mode holomorphic Fredholm family, and normalized infinite-circle family with common maximal domain, compact resolvent, Fredholm index zero, a topological determinant line and an explicit clutching-compatible Hermitian metric/flat connection in the chosen Fourier model | prove action/Hessian/mode/domain agreement, lift the circle model to the smooth global Janus family and identify its analytic Quillen/Bismut--Freed geometry, families-index curvature, eta holonomy and partition section |
| **P0/P-A** | reject shortcuts and define relative selection | exact Sylvester-regular roots now exist unconditionally for every raw `4×4` real matrix with split strictly-positive charpoly; a proof-carrying retained frontier certificate assembles the diagonal, fixed-similarity, double-`J₂`, explicit moving-shear, singular-diagonal and two explicit Jordan-type-change witnesses; the canonical intrinsic `(3,1)` metric has finite nonzero quotient action, unconditional smooth pullback by every D8 self-diffeomorphism, an integrated general-metric scalar action, finite covariance and Noether pairing, weak covariant Euler/flux decomposition, concrete Dirichlet flux cancellation, an unconditional pointwise/measured/two-sector/integrated scalar-stress covariance/exchange certificate, a unified general-Lorentz independent-field PT/exchange packet with all non-metric boundary traces, genuine IPP, a quotient-tangent canonical-collar Green current with unit-spacelike normal and exact locally conserved metric flux, and a conserved nonnegative-mass autonomous energy current; physical-volume graph `H¹`, coarea, canonical trace/operator/Dirichlet/Hilbert renorming, complete D8 time action, global scalar weak Euler/Jacobi and static index-zero Fredholm bridges are green | extend collar IPP to global manifold Stokes, identify the abstract boundary functional, prove four-dimensional covariant stress divergence and extend the collar current to a covariant four-dimensional Noether current; prove the single local normal-projection regularity lemma, identify intrinsic Sobolev sections, then arbitrary matrix-path/singular-frame/general Jordan-type classification and nonpositive/complex residuals, select the physical spectral domain, then general-metric throat restriction/boundary trace, antifields/full BV boundary stability and the curved global PDE |
| **P-B** | anomaly consistency | independent of Helmholtz; compact D7 heat blocks, convergent `Z4` determinant and modewise P--D7--D10 inflow bridge | common Fredholm family/regulator, full field/ghost content and global anomaly |
| **P-C** | inverse variational problem | green finite Helmholtz and polynomial reconstruction models | concrete nonlinear Janus Euler source and variational cohomology |
| **P-D** | invariant pairings | green low-rank pairing, spinor, fusion and `Z4` neutrality head; fixed-background D8 self-diffeomorphism category and general-Lorentz-metric pullback functor are exact | extend from the fixed background to the global moduli symmetry category, multiplicity spaces and normalizations |
| **P-E** | finite jets/equivariance | green corrected jet-universality head plus contravariant smooth-field and general-Lorentz-metric functors on the fixed D8 category | concrete global Janus jet group/bundles and elliptic classification |
| **P-F** | compatibility pullback | green `J^T H J` Helmholtz/Noether schema | actual compatibility complex and target pairing |
| **A/B/C** | scale, junction and charge compatibility | deep-alpha workflow green; advanced conditional chains | selected action, stable vacuum and common unit |
| **E** | observations | diagnostics only | native predictions from a closed theory |

The canonical physical trace now also defines a closed, complete, nonempty
homogeneous Dirichlet kernel with exact smooth zero-`L²`-trace agreement. Its
canonical nested finite-`ℓ²` renorming is a genuine Hilbert completion,
continuously linearly equivalent to the original graph norm and identical on
smooth jets. The renormed kernel now has a contractive orthogonal projection,
an orthogonal splitting and an exact equivalence with the graph-Dirichlet
kernel. This is not yet an intrinsic Sobolev identification.

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
| P-A relative uniqueness | yes; finite tangent generators and first-jet graph `H¹`, unconditional canonical trace/Dirichlet/Hilbert renorming, raw split-positive `4×4` Sylvester-regular root selection, unique global IFT-atlas lift on the full strictly-positive real-diagonalizable locus, fixed-similarity, double-Jordan, explicit moving-shear/singular-diagonal zero-frontier control and two explicit Jordan-type-change paths, canonical intrinsic global `(3,1)` metric, finite nonzero quotient action, unconditional arbitrary-diffeomorphism metric pullback, integrated scalar/Noether covariance, weak covariant Euler/flux, concrete Dirichlet cancellation, canonical-collar IPP, a quotient-tangent equal-mass Green current with unit-spacelike normal and exact locally conserved metric flux, conserved nonnegative-mass autonomous collar energy and an unconditional scalar-stress covariance/exchange certificate, complete D8 time flow, Candidate-A induced variation and static scalar ellipticity bridge | extend root atlases beyond the strictly-positive real-diagonalizable locus to Jordan/nonpositive and physical domains; globalize collar IPP to manifold Stokes, identify the abstract boundary functional, prove four-dimensional covariant stress divergence and extend the collar current to a covariant four-dimensional Noether current; prove normal-projection regularity, identify intrinsic Sobolev sections, then arbitrary singular-frame/general Jordan-type and nonpositive classification, parent action, general-metric/nonlocal BV and the curved global PDE |
| P-B anomaly logic | yes; positive-time compactness, physical `Z4` determinant and modewise P--D7--D10 inflow bridge, plus a holomorphic finite-mode determinant line and a normalized-circle canonical bounded-transform family that is self-adjoint, operator-norm continuous, Fredholm of index zero and has exact PT-opposite crossings, rank-one pointwise determinant fibers and a large-gauge endpoint transition | topology on the determinant family, global unbounded Janus Fredholm family/common domain, physical Hessian/regulator, Quillen/Bismut--Freed geometry and local/global anomaly not computed |
| P-C quadratic/polynomial Helmholtz | yes | nonlinear Euler source/cohomology open |
| P-D low-rank pairings/fusion | focused Lean head, global normal `Z4` root lines, abelian `U(1)^2` BRST, unconditional quotient/throat `so(3)` Koszul and LL closure, and a finite `32`-dimensional master BV model promoted to smooth throat/spacetime fields and coupled to the real positive diagonal/log metric cone with exact BRST, odd bracket, nonzero action, CME and PT covariance | general non-diagonal tensor-metric BV, derivative/nonlocal/completed functionals and global SpinC |
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
