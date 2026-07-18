# Program D10 — Quillen determinant, index gerbe and Janus anomaly geometry

## Question

Does the moduli stack of immersed Spin/PinC Janus throats carry a canonical
Quillen determinant line whose geometry automatically determines

- the elliptic complex;
- the effective potential;
- the quarter-holonomy `Z4` phases;
- the field multiplicities and sector normalization?

## Verdict

```text
Canonical relative anomaly object:       YES, conditionally.
Canonical simple Quillen line for all D10: NO.
Automatic elliptic complex:               NO.
Automatic Z4 root selection:              NO.
Automatic scalar potential:               NO.
Automatic sector normalization:           NO.
Canonical bulk-relative trivialization:   POSSIBLE, after a 4D theorem.
```

The correct object depends on which family is being considered.

## 1. The dependency direction

The determinant object does not create the differential operator. The order is

```text
moduli stack
  + universal geometric family
  + field bundles and connections
  + action Hessian
  + gauge fixing and Fredholm domains
      -> smooth elliptic/Fredholm family
          -> determinant/anomaly object.
```

Thus the abstract moduli stack of immersions is not enough. The Quillen or
Bismut--Freed package becomes canonical only **relative to the already
constructed family of operators and geometric data**.

## 2. Bosonic and ghost sectors

A gauge-fixed elliptic complex has a determinant line of the alternating
cohomology/Fredholm index. Once the complete BRST complex is defined, one can
form the tensor product of determinant lines with the appropriate signed
powers.

This is the natural home of the bosonic determinant magnitude and ghost
Jacobians.

It still depends on

- the actual field content;
- the Hessian of the selected action;
- gauge fixing and zero-mode removal;
- boundary conditions;
- multiplicities and statistics.

## 3. Closed three-dimensional fermion family

The Janus throat is a closed three-dimensional Euclidean manifold in D7/D9.
For a smooth family of self-adjoint Dirac operators on odd-dimensional closed
fibers, the families index is naturally `K1`-valued. The higher determinant
object is an index gerbe with connection, whose curvature is the degree-three
families-index form.

Therefore the intrinsic three-dimensional fermion sector is not directly the
standard even-dimensional Quillen determinant-line situation.

```text
closed 3D self-adjoint Dirac family
    -> K1 index
    -> index gerbe / eta anomaly object.
```

This statement concerns the phase/anomaly sector. It does not prevent the
regularized magnitude of `D^2`, or the boson/ghost complex, from contributing
ordinary determinant factors.

## 4. Three routes to line-valued data

### Route A — choose the `S2` fibration

Treat

```text
S2 -> S2 x S1 -> S1
```

as a family of even-dimensional chiral operators on `S2`. That family can have
a determinant line over the circle and the remaining parameter space.

This is not fully intrinsic to the three-manifold: it chooses the product
fibration/polarization and must be preserved by the allowed moduli and gauge
transformations.

### Route B — cut or choose a spectral section

A spectral section, polarization or suitable cutting construction can reduce
the odd-family gerbe to line-valued data. This is extra structure, not an
automatic consequence of the moduli stack.

### Route C — four-dimensional bulk/inflow

For an odd-dimensional bulk with boundary, Dai--Freed identify the
exponentiated eta invariant as an element of the inverse determinant line of
the even-dimensional boundary. Conversely, in a Janus bulk-boundary setup, a
compatible higher-dimensional theory can transgress or trivialize the boundary
anomaly object.

This is the strongest candidate for a **relative canonical** Janus partition
function:

```text
4D bulk action + APS/Dai--Freed data
    -> trivialization of the 3D relative anomaly
    -> scalar boundary partition function.
```

The bulk action, boundary conditions and normalization still have to be
microscopically derived.

## 5. What the Quillen/Bismut--Freed geometry does determine

After the family is fixed, the determinant line or gerbe can carry

- a Quillen metric;
- a Bismut--Freed connection;
- curvature given by the local families-index density;
- holonomy governed by eta/global-anomaly data;
- gauge-equivariant descent conditions.

This is powerful: it tests local and global anomaly cancellation and controls
how the quantum measure transforms over moduli.

## 6. What it does not determine

### It does not generate the elliptic complex

The line/gerbe is constructed from the Fredholm family. Reversing that arrow is
not justified. The action, Hessian, field bundles, ghosts and domains remain
prior inputs.

### It does not generate the `Z4`

The quarter phases arise from the square roots of the nontrivial Janus normal
line holonomy:

```text
normal holonomy = -1
square roots     = +i, -i.
```

The anomaly object can detect their eta/holonomy consequences, but it does not
create them. Geometry supplies a PT-conjugate pair; an additional physical law
must select one root or the paired sector.

### It does not fix field multiplicities

The cyclic holonomy and determinant object do not select rank five, the `1:5`
ratio or the full superdeterminant exponents. Those require the actual tensor,
spinor and ghost bundles and the gauge-fixed Hessian.

### It does not fix the scalar potential uniquely

Before anomaly cancellation, the partition function is naturally a section of
an anomaly object rather than a number. A scalar effective action requires a
trivialization. Changing a locality-compatible trivialization corresponds to a
finite local counterterm and shifts the scalar effective action.

Consequently a stationary modulus is not scheme-independent until the finite
parts are fixed by a target-independent microscopic condition.

### It does not fix absolute normalization or scale

The determinant object does not determine

- the overall action normalization;
- the renormalization scale;
- independent UV masses;
- the normalization relating spectral, LL, bulk and bimetric charges.

## 7. Precise Janus object

The best current formulation is a mixed anomaly package over the derived Janus
moduli stack:

```text
boson/ghost gauge-fixed complex
    -> determinant line(s)

closed 3D twisted Dirac family
    -> K1 index gerbe + eta section

normal-root local system
    -> PT-conjugate quarter boundary conditions

4D bulk/inflow or explicit trivialization
    -> scalar relative partition function.
```

The combined package is more naturally an invertible anomaly field theory than
a single ordinary line bundle.

## 8. Answer matrix

| Claim | Verdict |
| --- | --- |
| A canonical determinant/anomaly object exists once the universal Fredholm family is built | **Yes** |
| The bare immersion moduli stack alone carries the required object | **No** |
| The intrinsic closed 3D fermion object is a simple Quillen line | **No; naturally an index gerbe/K1 object** |
| A line can be obtained from an `S2` family, cut/polarization or bulk inflow | **Yes, with extra structure** |
| The object fixes curvature and global anomaly holonomy | **Yes, relative to the family** |
| It automatically creates the elliptic complex | **No** |
| It automatically produces/selects `Z4` | **No; the normal-root line supplies `±i`** |
| It automatically fixes `1:5` or field ranks | **No** |
| It automatically fixes the renormalized potential | **No** |
| It can help prove anomaly cancellation and consistency of a proposed potential | **Yes** |
| It fixes absolute alpha without UV input | **No** |

## 9. Lean implementation

Branch head:

```text
lake build JanusFormal.Branches.FundamentalGeometryD10QuillenAnomaly
```

Modules:

```text
P0EFTJanusAnomalyObjectDimensionParity.lean
P0EFTJanusAnomalyTransgressionInflow.lean
P0EFTJanusCircleHolonomyCommonDomainCompactResolvent.lean
P0EFTJanusCircleGraphFredholmIndex.lean
P0EFTJanusCircleBoundedTransformSpectralFlow.lean
P0EFTJanusCircleDeterminantLineFamily.lean
P0EFTJanusCircleDeterminantTopologicalBundle.lean
P0EFTJanusCircleQuillenMetricFlatConnection.lean
P0EFTJanusD2ModeFamilyInflowBridge.lean
P0EFTJanusFiniteModeFredholmDeterminantLine.lean
P0EFTJanusPartitionFunctionSectionNoGo.lean
P0EFTJanusPTPairedAnomalyCancellation.lean
P0EFTJanusQuillenFamilyCanonicity.lean
P0EFTJanusQuillenAnomalySynthesis.lean
```

The formal layer encodes

- one common maximal domain for the normalized infinite circle Dirac family at
  fixed fold, exact bounded scalar holonomy perturbations, entire dependence
  on complexified holonomy, finite spectral windows and an explicitly
  constructed compact two-sided resolvent `(D-i)⁻¹`;
- its complete graph-norm realization as a bounded Fredholm operator, with
  closed range, finite kernel and cokernel of equal rank, index zero, rank-one
  top-exterior determinant fiber and a nonzero induced section;
- the dependent determinant fibers as a genuine topological complex line
  bundle, including global trivialization, exact large-gauge endpoint
  clutching and quotient descent;
- in the chosen circle/Fourier trivialization, an explicit positive Hermitian
  metric, clutching isometry, compatible flat connection, isometric parallel
  transport and unit-norm closed holonomy;
- a concrete holomorphic symmetric finite-mode Dirac family, algebraic
  Fredholmness of index zero, its induced top-exterior determinant-line
  section, rank-one fiber, PT covariance and invertibility at both quarter
  holonomies;
- the determinant-line/index-gerbe parity distinction;
- the extra structures required to reduce an odd family to line data;
- the dependence of scalar actions on trivialization and finite counterterms;
- additive PT-pair and bulk-inflow cancellation, while keeping class vanishing
  distinct from constructing a partition-function trivialization;
- the two PT-conjugate normal-root phases;
- the exact closure matrix for a predictive Janus potential.

The circle result supplies a genuine common unbounded domain, compact
resolvent, Fredholm graph realization, one-dimensional determinant fibers and
a topological complex line bundle.  That bundle now carries an explicit
clutching-compatible Hermitian metric and flat connection in the chosen
Fourier model.  This construction is not identified with the analytic Quillen
metric or Bismut--Freed connection of a global unbounded Janus family, and it
does not prove the families-index curvature formula or eta holonomy.  The
finite-mode determinant line remains a separate holomorphic cutoff model; the
physical Hessian and complete field/ghost regulator are still open.

## 10. Primary references

- D. Quillen, *Determinants of Cauchy--Riemann operators over a Riemann
  surface*.
- J.-M. Bismut and D. Freed, *The analysis of elliptic families I--II*.
- X. Dai and D. Freed, *Eta-Invariants and Determinant Lines*.
- D. Freed, *Determinant Line Bundles Revisited*.
- J. Lott, *Higher-Degree Analogs of the Determinant Line Bundle*.
- A. Carey and B.-L. Wang, *On the relationship of gerbes to the odd families
  index theorem*.
- D. Freed, *Anomalies and Invertible Field Theories*.

## Final conclusion

The strongest defensible statement is

```text
The Janus derived moduli problem should carry a canonical relative anomaly
package after its universal gauge-fixed elliptic family is constructed.
```

It is **not** a single universally canonical Quillen line that automatically
creates the theory. The fermionic closed-3D component is naturally gerbe-valued;
a scalar potential appears only after anomaly cancellation/trivialization, and
its finite normalization remains microscopic input.

Thus D10 is retained as a consistency and anomaly-geometry program, not as an
automatic generator of the Janus action or absolute scale.
