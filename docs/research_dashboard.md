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
| **D0/D8** | global geometry and normal lift | analytic manifold atlases on the concrete `S³×ℝ` and `S²×ℝ` covers; smooth deck actions and smooth throat-cover inclusion with locally groupoid-compatible section transitions; effective quotient and throat are actual `C⁰` manifolds with local-homeomorphism projection and `C⁰` throat embedding; continuous involutive PT; two connected components upstairs exchanged by reflection/deck whose quotient images coincide with the full path-connected one-sided complement; associated normal-line quotient; two-sheeted even-winding throat cover with free deck involution and topologically trivial normal pullback | install quotient `ChartedSpace`/`IsManifold` and promote projection/embedding to `C∞`, then stratified geometry, differential `VectorBundle` and global Pin/root bundle |
| **D2** | focused twisted Dirac spectrum | green monopole eigenvalue/multiplicity law, `l2`, self-adjointness, compact resolvent and circle-reduced determinant | extend the circle model to the common-domain global Janus operator family |
| **D7** | heat kernel/effective action | green convergent heat trace, order-four Euler--Maclaurin remainder control, unconditional spectral/universal `a0/a2/a4` small-time matching, convergent `Z4` determinant, and normalized-circle heat generator with maximal domain exactly `Dom(D²)=Dom(D∘D)` | abstract functional calculus/trace class, then connect the closed local spectrum to the full field/ghost regulator and global Fredholm family |
| **D9/D11** | elliptic and natural-operator gates | green D9 symbol/BRST and D11 naturality/jet heads | concrete Janus Fredholm family |
| **D10** | Quillen/anomalies | green transgression/inflow, P--D7--D10 physical-`Z4` spectral bridge, concrete finite-mode holomorphic Fredholm family, and normalized infinite-circle family with common maximal domain, entire dependence, compact resolvent, complete graph-norm Fredholm realization of index zero and rank-one determinant fiber | lift the circle model/fiber to the smooth global Janus family and its family index/line bundle, Quillen metric/connection, eta holonomy and partition section |
| **P0/P-A** | reject shortcuts and define relative selection | moduli no-go; parent Schur reduction; effective D8 quotient bases/PT/throat inclusion with concrete continuity predicates and a nonempty continuous PT-matched Minkowski/identity-root configuration, plus genuine smooth deck-invariant coefficient fields on the analytic cover with injective continuous descent; weighted `Z^4` Hilbert exactness with bounded reconstruction, maximal symbol domain, closed compatible zero-free range and same-scale zero-mode obstruction, plus a one-order graph-Sobolev source scale on which the physical Lorentz--Gram symbol is an exact bounded contraction and whose target identity Hessian pulls back to a symmetric positive `J†J` with only the zero-mode kernel, split by a bounded projection into an actual normed physical quotient with nondegenerate canonical representatives; `4×4` root branch on an explicit open IFT domain with continuity, exact square, uniqueness, Sylvester invertibility and full two-sector Candidate-A derivatives throughout its PT-paired intersection, now lifted to a measured D8 functional under explicit domination and PT-invariant-measure contracts; pointwise 4D scalar stress; flat-chart simultaneous metric/holonomic variation integrated under an explicit dominated contract, with pointwise Euler-plus-divergence and conditional integrated weak Euler pairing | promote smooth fields/descent to quotient Sobolev spaces/traces, extend the identity-root chart to the global causal Lorentz domain, identify Fourier Hessian with the same global action, discharge domination/flux and obtain curved global PDE/stability |
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
| P-A relative uniqueness | yes; continuous PT-matched effective D8 field configuration, weighted `Z^4` Hilbert exactness on the maximal symbol domain with closed zero-free range and an exact bounded graph-Sobolev shifted symbol, local `4 x 4` root, pointwise scalar stress, flat-chart holonomic `p = d phi` and simultaneous metric/field variation integrated under a dominated contract, plus pointwise Euler/divergence and weak Euler pairing under an explicit zero-flux condition | smooth/global Sobolev field realization with boundary conditions, parent action, automatic domination, derivation of zero flux from boundary data and curved global PDE/root selection not derived |
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
