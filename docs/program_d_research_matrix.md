# Program D Research Matrix

## Purpose

This file is the stable navigation surface for Program D.  It records what is
proved, what is only a geometric construction target, what is a physical
hypothesis, and what has been ruled out.

Evidence codes:

| Code | Meaning |
| --- | --- |
| **T** | theorem or exact algebra formalized in Lean |
| **G** | genuine geometric construction still required |
| **P** | physical emergence hypothesis |
| **N** | no-go or falsification result |

## Dependency graph

```text
D1 mapping-torus quotient and orientation cover
 ├─> D2 fixed throat S2 x S1
 ├─> D3 cellular/singular cohomology and Pin bundles
 └─> D4 throat gauge bundle and charge transgression
       ├─> D5 spectral/Dirac effective dynamics
       ├─> D6 bimetric boundary charge matching
       └─> D7 dimensionless alpha ratio
             └─> D8 absolute scale generation
```

## Current matrix

| ID | Workstream | Deliverable | Evidence | Current result | Terminal blocker | Priority |
| --- | --- | --- | --- | --- | --- | --- |
| **D1.1** | Twisted generator | `(x,u) -> (rho x,u+T)` and square action | **T** | two steps equal pure translation by `2T` | none at algebraic level | closed |
| **D1.2** | Period circle | algebraic `R/(T Z)` quotient | **T** | quotient type and fixed-fiber descent constructed | quotient topology and smooth structure | very high |
| **D1.3** | Orientation cover | quotient by square subgroup | **G** | index-two mechanism explicit | proper action, quotient and covering-map proof | very high |
| **D2.1** | Reflection fixed set | equatorial `S2` inside `S3` | **T/G** | coordinate reflection and fixed-set equation proved | manifold-level identification | high |
| **D2.2** | Canonical throat | fixed locus `S2 x S1_T` | **G** | circle factor constructed algebraically | homeomorphism/diffeomorphism of fixed quotient | very high |
| **D3.1** | Cellular complex | top boundary `1-(-1)=2` | **T** | kernel, image, torsion and Euler algebra proved | realization as CW complex of actual quotient | high |
| **D3.2** | Degree-two cohomology | `H2(-;Z2)=0` candidate | **T/G** | zero cellular degree-two group proved | cellular-to-singular comparison | very high |
| **D3.3** | Pin obstruction | vanish in trivial `H2` group | **T** | generic cohomological Pin theorem proved | tangent classes and Pin principal bundles | very high |
| **D3.4** | Physical Pin sign | select Pin lift and fermionic `Z4` | **P** | finite `ZMod 4` arithmetic available | global Pin lift, eta/anomaly calculation | high |
| **D4.1** | Global Hopf `U(1)` | descend primitive Hopf bundle | **N** | impossible under orientation-reversing compatible monodromy | route rejected | closed |
| **D4.2** | Global line bundle | nontrivial ordinary line bundle on full quotient | **N/G** | cellular `H2` model says none | singular-cohomology comparison | high |
| **D4.3** | Fixed-throat PT flux | one conjugate monopole descending on pointwise-fixed `S2` | **N** | nonzero flux forced to zero | route rejected unless doubled/twisted | closed |
| **D4.4** | Intrinsic throat monopole | primitive line bundle on throat | **T/G** | integer sector and local Dirac patching proved | principal bundle and connection globalization | very high |
| **D4.5** | Bulk-boundary transport | degree `4 -> 3 -> 2` transgression | **T/P** | primitive integer transport algebra proved | actual relative class, circle integration and normalization | high |
| **D5.1** | Unweighted isotropy | `lambda_S2=lambda_S1` | **T/P** | unique minimum only if odd mismatch terms vanish | derive exchange symmetry to all orders | downgraded |
| **D5.2** | Weighted spectral lock | determinant-weighted mode balance | **T/P** | positive weights give unique modulus; `3:2` proxy available | compute field content and regularized determinant weights | top priority |
| **D5.3** | Spectral charge | `q_LL` from first sphere gap | **T/P** | compatibility requires coefficient `c_q=1/8` when `A=L` | derive coefficient from operator/connection normalization | top priority |
| **D5.4** | Dirac/eta program | effective action from twisted Dirac spectrum | **P** | architecture identified | operator construction, spectrum, eta and determinant | top priority |
| **D6.1** | Bimetric radius | `A=R_s` on finite PT bridge | **T/P** | conditional relational algebra exists | nonlinear action and null junction | high |
| **D6.2** | Charge compatibility | same normalized charge in geometry, LL and bridge | **T/P** | algebraic unit transport proved elsewhere | covariant phase-space charge and large-gauge periods | high |
| **D7.1** | Dimensionless ratio | derive `A/L` | **T/P** | conditional fourth-power law proved | choose/derive spectral weights and charge coefficient | high |
| **D8.1** | Absolute scale | derive `L` and `A` without fit | **N/P** | scale-covariance obstruction proved | quantum transmutation or other dimensionful law | final |

## Spectral branch decision

### Rejected as a generic law

```text
lambda_S2 = lambda_S1
```

is not generic.  For a quadratic effective potential

```text
V(d) = w d^2 + b d + c,
```

isotropy `d=0` is stationary exactly when `b=0`.  A derived reflection/exchange
symmetry must forbid all odd mismatch terms.  The geometry `S2 x S1` does not by
itself provide an obvious exchange of the two factors.

### Active replacement

The active spectral hypothesis is a weighted balance

```text
w_S2 T^2 = 2 w_S1 pi^2,
```

where the weights must be computed from degeneracies, statistics, gauge fixing
and the regularized determinant.  The first scalar degeneracies `3` and `2`
are only a diagnostic proxy, not a completed one-loop calculation.

## Immediate theorem sequence

1. **CI closure** — keep `FundamentalGeometryD` and its Python audit green.
2. **Topological quotient** — equip `PeriodCircle T` and the mapping-torus
   quotient with topology; prove the fixed quotient is `S2 x S1`.
3. **Cohomology comparison** — identify the cellular chain model with singular
   homology/cohomology of the quotient.
4. **Pin realization** — construct the Pin bundles after the obstruction classes
   vanish; compute which lift realizes the fermionic `Z4`.
5. **Monopole globalization** — turn the north/south Dirac potentials into a
   principal `U(1)` bundle with connection on the throat.
6. **Twisted Dirac operator** — define the Pin/monopole-twisted Dirac operator on
   the throat and determine zero modes, degeneracies and eta symmetry.
7. **Determinant weights** — compute the regularized effective potential for the
   circle modulus and decide the weighted spectral law.
8. **Charge bridge** — identify the spectral/gauge normalization with the LL and
   bimetric Hamiltonian charge.
9. **Absolute scale** — only after steps 1–8, test dimensional transmutation or
   another non-circular scale generator.

## Falsification checkpoints

Program D must be revised if any of these occur:

- the mapping-torus quotient cannot be made into the required smooth geometry;
- the fixed locus is not `S2 x S1` with the needed normal data;
- the actual `H2` or Stiefel--Whitney calculation contradicts the cellular
  candidate;
- no anomaly-consistent Pin lift exists;
- the throat monopole cannot be globalized compatibly with PT;
- the determinant has no stable modulus or gives weights incompatible with the
  bridge normalization;
- the positive-kinetic bimetric completion cannot recover the Janus weak-field
  signs;
- charge normalizations fail to commute across bulk, throat and bridge.

## Current conclusion

Program D has produced a viable **geometric core candidate**, but not yet an
emergent physical theory.  The ordinary global Hopf-bundle route is rejected.
The surviving central object is the fixed throat with an intrinsic or doubled
monopole gauge sector.  The next decisive calculation is no longer an arbitrary
spectral equality: it is the spectrum and determinant of the correctly twisted
operator on that throat.
