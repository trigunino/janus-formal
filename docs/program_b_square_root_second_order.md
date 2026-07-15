# Program B — square-root expansion through second order

- Program: **B**
- Stable ID: `B-SQRT-O2`
- Evidence: **X** (SymPy audit)
- Dependencies: proportional background square root and HR potential convention
- Script: `scripts/derive_svt_hr_second_order_hessian.py`

## Result

For the series

```text
S = S0 + eps X1 + eps² X2,
```

the Sylvester equations

```text
S0 X1 + X1 S0 = H,
S0 X2 + X2 S0 = -X1²
```

are solved componentwise. The executable audit now squares the resulting
series and verifies that the residual coefficients at orders `eps` and `eps²`
vanish in the tensor, vector and scalar projections.

The projected HR Hessians are therefore based on a checked second-order square
root expansion rather than an assumed formula.

## Remaining scope

This closes the selected diagonal proportional background and the implemented
SVT projections. It does not prove smooth real-root existence for arbitrary
Lorentzian metric pairs or fix the full action normalization/sign.
