# Program B — cosmological mode stability

- Program: **B**
- Stable ID: `B-COSMO-MODE-STABILITY`
- Evidence: **T** (Lean theorem)
- Dependencies: reduced SVT stability cone and PT-flat relative mass
- Lean target: `P0EFTJanusCosmologicalModeStability.lean`

## Result

For a reduced mode with kinetic coefficient `alpha`, gradient coefficient
`beta` and mass squared `m²`, define

```text
c_s² = beta/alpha,
omega²(k) = c_s² k² + m².
```

The gate proves:

- `alpha > 0` and `beta > 0` imply `c_s² > 0`;
- adding `m² >= 0` gives `omega²(k) >= 0`;
- every nonzero Fourier mode has `omega²(k) > 0`;
- the vector and scalar coefficients satisfy these statements on the selected
  SVT cone;
- the PT-flat relative tensor mass is strictly positive for `beta1 > 0` and
  `beta2 >= 0`.

This closes reduced ghost/gradient/tachyon signs. It does not include
time-dependent FLRW friction, Higuchi-type bounds, strong coupling or the full
constraint-reduced scalar action.
