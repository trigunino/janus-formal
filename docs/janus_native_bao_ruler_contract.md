# Janus Native BAO/Ruler Contract

## Contract

A native BAO comparison must compute the DESI vector from Janus quantities:

```text
D_M^J(z) / r_d^J
D_H^J(z) / r_d^J
D_V^J(z) / r_d^J
```

with:

```text
D_H^J(z) = c / H_J(z)
D_V^J(z) = (z D_M^J(z)^2 D_H^J(z))^(1/3)
r_d^J = integral c_s^J(z) / H_J(z) dz over the pre-drag domain
Gamma_drag^J(z_d^J) = H_J(z_d^J)
```

Forbidden:

- fitted Planck/LCDM `r_d`;
- archived Z4 inputs;
- post-hoc anisotropic BAO ruler patches.

## Deeper Domain Obstruction

For the normalized Janus exact branch:

```text
z_max(q0) = -1/(2 q0)
```

Thus a published-like value `q0 = -0.087` gives:

```text
z_max ~= 5.747
```

That does not reach a high-redshift drag/sound-horizon epoch. A marker
`z_d ~ 1059` requires roughly:

```text
q0 >= -4.72e-4
```

The SN+BAO runner selects `q0 -> 0-`, exactly the regime where the high-redshift
domain reappears.

## Verdict

BAO cannot be repaired by fitting `alpha` alone.

A native Janus BAO rescue requires one of:

1. a Janus early-time branch that reaches `z_d^J` for interior `q0`;
2. a modified pre-drag redshift map;
3. active photon-baryon plasma primitives giving `c_s^J`, `Gamma_drag^J`,
   `z_d^J`, and `r_d^J`.

Until then, the current background-proxy BAO rejection stands.
