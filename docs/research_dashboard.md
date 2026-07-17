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
| **D0/D8** | global geometry and normal lift | analytic compact mapping-torus quotients, differential-normal `Diffeomorph`, smooth bundle atlas and causal strata; the intrinsic Lorentz metric/musical, equal-sector pair and nondegenerate throat trace are PT fixed by public cover time-reversal naturality and descent uniqueness; the explicit local normal curve/tangent and scalar quadratic model have exact all-winding deck/parity laws, while its named cover normal is `HEq` to the raw derivative; ambient orientation/Spin data and the normal `Pin⁻(1) ≃ Z4` bundle are exact | bridge the raw cover derivative to the quotient derivative and glue the local normal lift continuously; classify arbitrary general-metric throat restrictions; trivialize the Spin Čech class and extend to SpinC |
| **D2** | focused twisted Dirac spectrum | green monopole eigenvalue/multiplicity law, `l2`, self-adjointness, compact resolvent and circle-reduced determinant | extend the circle model to the common-domain global Janus operator family |
| **D7** | heat kernel/effective action | green convergent heat trace, order-four Euler--Maclaurin remainder control, unconditional spectral/universal `a0/a2/a4` small-time matching, convergent `Z4` determinant, normalized-circle heat generator with maximal domain exactly `Dom(D²)=Dom(D∘D)`, and positive-time summable rank-one nuclear expansion with the spectral trace | abstract functional calculus/general trace-class API, then connect the closed local spectrum to the full field/ghost regulator and global Fredholm family |
| **D9/D11** | elliptic and natural-operator gates | green D9 symbol/BRST and D11 naturality/jet heads; unconditional quotient/throat `so(3)` Koszul and LL completion; finite `32`-dimensional BV master model promoted to smooth throat and true-spacetime fields, then coupled to the actual smooth positive diagonal/log metric cone with ghosts, antifields, nonzero action, pointwise/integrated CME and unconditional PT covariance; the separate first general-tensor BV level has an odd square-zero doublet and pointwise PT/exchange-covariant pairing and graded antibracket | prove Lorentz-domain preservation and a functional CME for general non-diagonal tensors, then BV boundary trace, derivative-dependent and arbitrary nonlocal/completed functionals, SpinC and a concrete Janus Fredholm family |
| **D10** | Quillen/anomalies | green transgression/inflow, P--D7--D10 physical-`Z4` spectral bridge, literal finite P-period product-mode truncation with exact PT/regulator cancellation, concrete finite-mode holomorphic Fredholm family, and normalized infinite-circle family with common maximal domain, compact resolvent, Fredholm index zero, a topological determinant line and an explicit clutching-compatible Hermitian metric/flat connection in the chosen Fourier model | prove action/Hessian/mode/domain agreement, lift the circle model to the smooth global Janus family and identify its analytic Quillen/Bismut--Freed geometry, families-index curvature, eta holonomy and partition section |
| **P0/P-A** | reject shortcuts and define relative selection | split-positive raw `4×4` root selection with Jordan/singular witnesses; the intrinsic `(3,1)` metric has nonzero action and is PT fixed together with its equal-sector pair and nondegenerate throat trace; scalar stress has arbitrary-coordinate jet conservation with its pointwise Levi-Civita interface discharged from the metric first jet; the general-Lorentz packet has PT-natural nondegenerate traces and functional Dirichlet matching; collar IPP/flux, all-winding local-normal curve/tangent/quadratic deck laws plus cover raw-derivative `HEq`, pointwise PT-covariant first-level tensor BV, physical trace/Hilbert and scalar Fredholm bridges are green | lift the pointwise Levi-Civita jet to smooth global connections/fields and prove global `div_g T = 0`; globalize collar Stokes/Noether; bridge the cover normal to the quotient derivative and glue globally; identify intrinsic Sobolev sections, classify Jordan/nonpositive/root and general throat-metric domains; prove functional tensor BV and the curved global PDE |
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
| P-A relative uniqueness | yes; graph `H¹`/trace/Hilbert, split-positive root IFT atlas and Jordan witnesses, PT-fixed intrinsic metric/action and nondegenerate throat trace, arbitrary-coordinate scalar-stress jet conservation with pointwise Levi-Civita realization, functional metric Dirichlet matching, all-winding local-normal curve/tangent/quadratic deck laws plus cover raw-derivative `HEq`, and scalar Fredholm bridges | extend roots beyond the positive locus; lift the local connection jet to smooth fields and prove global `div_g T = 0` plus collar Stokes/Noether; bridge/glue the normal projection globally, classify general throat metrics, identify intrinsic Sobolev sections, then functional tensor BV and the curved global PDE |
| P-B anomaly logic | yes; positive-time compactness, physical `Z4` determinant and modewise P--D7--D10 inflow bridge, plus a holomorphic finite-mode determinant line and a normalized-circle canonical bounded-transform family that is self-adjoint, operator-norm continuous, Fredholm of index zero and has exact PT-opposite crossings, rank-one pointwise determinant fibers and a large-gauge endpoint transition | topology on the determinant family, global unbounded Janus Fredholm family/common domain, physical Hessian/regulator, Quillen/Bismut--Freed geometry and local/global anomaly not computed |
| P-C quadratic/polynomial Helmholtz | yes | nonlinear Euler source/cohomology open |
| P-D low-rank pairings/fusion | focused Lean head, global normal `Z4` root lines, abelian `U(1)^2` BRST, unconditional quotient/throat `so(3)` Koszul and LL closure, a finite `32`-dimensional master BV model promoted to smooth throat/spacetime and positive diagonal/log metrics, plus a first-level general symmetric-tensor field/antifield doublet with pointwise PT/exchange-covariant pairing and odd bracket | Lorentz preservation, BV boundary trace and functional CME for general non-diagonal tensor-metric BV, derivative/nonlocal/completed functionals and global SpinC |
| P-E jet theorem architecture | focused head green | Janus specialization open |
| P-F pullback schema | focused head green | actual `K`, `J`, `H` and primitive open |
| finite normalization/counterterms | no | microscopic law open |
| stable vacuum | no | full renormalized action open |
| absolute scale | no | scale-breaking and charge compatibility open |

## Highest-priority theorem queue

The exhaustive dependency-aware checklist is
[`program_p_exhaustive_todo.md`](program_p_exhaustive_todo.md).
Mechanical count: **483 closed / 608 total; 125 open**.

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
