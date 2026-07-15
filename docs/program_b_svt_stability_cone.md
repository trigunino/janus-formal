# Program B — SVT stability cone

- Program: **B**
- Stable ID: `B-SVT-STABILITY-CONE`
- Evidence: **T** (Lean theorem) plus existing **X** coefficient ledger
- Dependencies: reduced SVT coefficients and positive-kinetic candidate branch
- Lean target: `P0EFTJanusSVTStabilityCone.lean`

## Result

A sufficient simultaneous vector/scalar stability cone is proved under

```text
v > 0,
Mpl² > 0,
aetherScale < Mpl²,
lambdaPhi >= 0,
membraneTension >= 0,
mHR² >= 0.
```

On this cone:

- vector kinetic and gradient coefficients are positive;
- vector mass squared is nonnegative;
- scalar kinetic and gradient coefficients are positive;
- scalar mass squared is nonnegative.

This closes the sign analysis for the encoded reduced coefficients. It does not
derive those coefficients from the complete nonlinear action or close the
scalar lapse/shift constraint.

## Failure criterion

Leaving this sufficient cone requires a separate exact stability proof; in
particular `aetherScale >= Mpl²` invalidates the reduced vector kinetic gate.
