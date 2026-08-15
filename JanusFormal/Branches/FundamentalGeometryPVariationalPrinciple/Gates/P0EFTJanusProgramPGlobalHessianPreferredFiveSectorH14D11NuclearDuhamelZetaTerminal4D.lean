import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11CollapsedReferenceBoundaryLimitsSpectralAtlas4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceBoundedComposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeNuclearMellinDifferenceFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPOperatorNormDifferentiableUnitaryGreenConjugation4D

/-!
# Terminal H14--D11 endpoint-limit nuclear-Duhamel zeta facade

Building this module imports the complete preferred Candidate-A continuation
chain through

* the concrete H14 actual-kernel gap and reduced Green;
* one operator-norm differentiable unitary represented D11 frame;
* the physical C1 five-sector kernel family and canonical complement frame;
* fixed- and moving-coordinate Green derivative identities;
* intrinsic nuclear trace invariance, scalar linearity and subtraction;
* automatic bounded/nuclear composition expansions and intrinsic trace
  cyclicity;
* the actual heat/zeta family transported from one H12 nuclear heat family;
* exact relative scalar heat traces derived from nuclear operator subtraction;
* analytic Mellin continuation uniqueness and analytic actual/reference
  subtraction;
* base and local reference heat derivatives obtained from nuclear operator
  Duhamel identities;
* probability-averaged Duhamel slices of the form

  ```text
  K_left (H' K_right);
  ```

* cyclic rotation and heat-semigroup collapse of every slice to `H' K_full`;
* common rank-one expansions of the collapsed insertion/full-heat operators on
  the short- and long-time regions;
* operator-valued regional integrals obtained by integrating the rank-one
  coefficients;
* derivation of `integral Tr(D) = Tr(integral D)` from semigroup collapse and
  one certified sum/integral interchange on each region;
* short-time renormalized cutoff convergence;
* long-time finite-cutoff primitive identities and decay of the terminal
  primitive;
* derivation, by uniqueness of limits, of

  ```text
  C - D_short = G H' + B,
  D_long       = B;
  ```

* cancellation of the matching operator, intrinsic trace subtraction and
  transport to `G H'`;
* derived finite-part derivatives, standalone reference coefficients and all
  relative spectral-cut coefficients;
* reconstruction of the final spectral atlas with the physical D11 kernel
  basis and the original reference operators/zeta charts.

At this level the following former inputs have disappeared:

```text
aligned expansions of B T and T B,
trace of one Duhamel slice = trace of its cyclic collapse,
probability average of slice traces = collapsed trace,
integral Tr(D) = Tr(integral D),
C - D_short = G H' + B,
D_long = B,
C' - integral_short Tr(D) - integral_long Tr(D) = Tr(G H'),
reference zeta coefficient = -Tr(G H'),
relative spectral coefficient = Tr(G_ref H'_ref).
```

The remaining reference-side analytic content is localized to concrete
spectral and limiting certificates:

1. construct the genuine reference heat and Duhamel operators and prove their
   intrinsic nuclearity and parameter differentiability;
2. supply nuclear expansions of `H'_a K_right(a,t,s)` for fixed Duhamel slices;
3. prove the heat semigroup law for the left/right factors;
4. prove the original Duhamel trace is the probability average of the slice
   traces;
5. construct common rank-one expansions of `H'_a K_a(t)` and prove pointwise
   and integrated nuclear-norm summability;
6. prove the two exchanges of the spectral sum with time integration;
7. prove convergence of the short-time cutoff counterterm and cutoff integral,
   together with convergence of their renormalized remainder to `G H'`;
8. prove the finite long-time primitive identity and decay of its terminal
   value;
9. identify the counterterm derivative with its nuclear operator trace;
10. prove reality of the standalone reference zeta derivative at zero and the
    common analytic continuation domains used by relative subtraction.

No opaque total finite-part derivative, integrated trace equality, exact
boundary identity, global Duhamel--Green scalar equality or complex coefficient
equality remains as an independent input.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11NuclearDuhamelZetaTerminal4D

set_option autoImplicit false
noncomputable section

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11NuclearDuhamelZetaTerminal4D
end JanusFormal
