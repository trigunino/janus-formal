import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedProductThroatLongTimeSpectralReferenceAtlas4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPIntrinsicNuclearTraceBoundedComposition4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPRelativeNuclearMellinDifferenceFamily4D
import JanusFormal.Branches.FundamentalGeometryPVariationalPrinciple.Gates.P0EFTJanusProgramPOperatorNormDifferentiableUnitaryGreenConjugation4D

/-!
# Terminal H14--D11 facade with concrete product-throat long-time decay

This is the strongest current dependency checkpoint for the Candidate-A
selected-trace determinant route.

For the base reference and every local spectral-cut reference, the long-time
analysis is no longer parameterized by an arbitrary positive rate.  A genuine
circle-times-monopole-sphere spectrum supplies

```text
c_ref = 1 / R_ref^2 > 0.
```

The sphere eigenvalues are bounded below by `c_ref`, the circle square is
nonnegative, and the complete infinite product heat trace obeys

```text
Tr K_ref(t)
  ≤ exp(c_ref) Tr K_ref(1) exp(-c_ref t),
  t ≥ 1.
```

Two natural operator estimates then generate both long-time inputs:

```text
‖Tr D_ref,a(t)‖ ≤ B_a Tr K_ref(t),
‖terminalPrimitive_a(T)‖ ≤ C_a Tr K_ref(T).
```

Consequently the imported chain derives

* integrability of the weighted long-time Duhamel derivative;
* differentiation under the long-time heat integral;
* decay of the terminal primitive;
* the exact long-time boundary identity;
* the selected endpoint trace `Tr(G_ref H'_ref)`;
* canonical Schwarz reality and the reference zeta coefficient;
* the unchanged physical D11 kernel family and determinant atlas.

The short-time subtraction remains local and dominated, because its majorant
is controlled by the heat asymptotic expansion rather than by the positive
large-time spectral gap.

No H14 two-sided Fredholm norm gap is reinterpreted as positivity of the heat
generator.  The positive rate in this terminal facade comes solely from the
concrete product reference spectrum.
-/

namespace JanusFormal
namespace P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedProductThroatLongTimeNuclearDuhamelZetaTerminal4D

set_option autoImplicit false
noncomputable section

end
end P0EFTJanusProgramPGlobalHessianPreferredFiveSectorH14D11SelectedTraceShortDominatedProductThroatLongTimeNuclearDuhamelZetaTerminal4D
end JanusFormal
