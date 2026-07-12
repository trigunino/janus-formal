# Janus Alpha: Deep Completion Evaluation

## Executive conclusion

The two deepest programs are **serial**, not mutually exclusive alternatives.

```text
Program B: nonlinear bimetric action and PT junction
  -> derives the bridge geometry, sign map and relational scale equations

Program A: quantum LL world-volume
  -> derives the dimensionful charge/tension unit and the hierarchy

Compatibility theorem
  -> identifies the quantum charge with the charge entering the classical
     junction and conditional alpha spectrum
```

Absolute no-fit closure requires all three blocks.

## Already closed relational chain

The combined branch has reduced the target to

```text
A = alphaSquaredLength = R_s,
E_global = -3 M_bridge/(4 pi),
16 q_LL^2 A^4 = 1,
8 pi |chi| A = 1.
```

Therefore

```text
A = 1/(2 sqrt(q_LL)) = 1/(8 pi |chi|).
```

The missing task is no longer an unspecified “alpha law.”  It is the derivation
of the normalized microscopic charge and its equality with the charge appearing
in the bimetric boundary Hamiltonian.

## Program A: quantum world-volume

### Strengths

- Can break the classical scale orbit without observational fitting.
- A classically scale-invariant `2+1` dimensional scalar/compact-U1/CS candidate
  can generate `q_LL` from a quantum condensate.
- Moderate microscopic couplings can generate an exponential hierarchy.
- Primitive topological sector remains compatible with a large macroscopic
  scale because the hierarchy is placed in the dynamically generated charge,
  not in an integer `10^122`.

### Risks

- Exponential sensitivity to the UV coupling.
- Parity/global anomaly constraints.
- Exact flat directions do not select a unique scale.
- Known large-N three-dimensional scale-breaking phases have stability and
  next-to-leading-order caveats.
- Gauge and renormalization-scheme independence of the condensate must be
  proved.

### Terminal theorem

Construct a reflection-positive Euclidean or unitary Lorentzian quantum theory
whose exact effective action has one stable positive vacuum `v_*`, with

```text
q_LL = c_q v_*^2
```

and a microscopic law fixing `c_q` and the UV data.  Then the existing Lean
algebra transports this to a unique `A`.

## Program B: nonlinear bimetric action

### Strengths

- Required independently of the alpha problem: the published cross
  interactions are not explicit enough for a complete variational theory.
- Common-action integrability gives a sharp test for proposed cross sources.
- Diagonal Noether identities determine the correct exchange-current logic.
- Misner--Sharp plus PT reduces the finite bridge mass law to one sign theorem.
- A reciprocal elementary-symmetric potential supplies a concrete covariant
  candidate completion.

### Risks

- The published relative negative Einstein--Hilbert coefficient gives an
  indefinite quadratic kinetic form if both spin-2 modes propagate normally.
- A ghost-free potential does not by itself repair a wrong-sign kinetic mode.
- The full null-boundary variational principle and quasi-local Hamiltonian
  charge are substantial developments.
- Classical dimensionless coefficients cannot determine the absolute LL charge
  normalization.

### Terminal theorem

Construct one covariant, integrable, constraint-consistent action with a bounded
physical Hamiltonian and prove that its PT-odd boundary charge satisfies

```text
M_bridge = -M_MS^(-),
A = R_s.
```

## Compatibility block

The two programs meet at the LL boundary charge.  The required theorem must
identify all normalizations, not only the integer sector:

```text
Q_bulk^twisted
  -> Q_boundary
  -> q_LL n_aux
  -> M_bridge
  -> E_global
  -> A.
```

Necessary checks:

1. relative cohomology/boundary map;
2. compact circle or other degree-lowering transgression;
3. equality of large-gauge periods;
4. equality of charge operator normalizations;
5. matching of Euclidean and Lorentzian signs;
6. matching of PT orientation conventions;
7. no target radius used to choose a coupling or counterterm.

## Comparative score

| Criterion | Quantum world-volume | Nonlinear bimetric action |
| --- | ---: | ---: |
| Fixes absolute scale | Yes, in principle | No, not alone |
| Fixes bridge relation | Only through compatibility | Yes |
| Existing published foundation | Partial LL/QFT mechanisms | Janus equations plus general bimetric theory |
| Main mathematical difficulty | Nonperturbative QFT and stable vacuum | Covariant variation, constraints, null boundary |
| Main physical risk | Instability/scheme sensitivity | Ghost/kinetic-sign problem |
| Can be completed independently | No | No for final alpha |
| Priority | Second after classical consistency, then co-developed | First mandatory foundation |

## Recommended order

1. **Resolve the kinetic-sign question first.**  If no positive physical
   Hilbert-space completion exists, the published `kappa=-1` action form must be
   rewritten before further alpha work.
2. Construct one common integrable interaction and derive the finite PT
   junction.
3. In parallel, compute the quantum world-volume effective action for the
   scale-invariant candidate.
4. Reject any quantum phase with a flat or unstable vacuum.
5. Derive the bulk/boundary charge normalization theorem.
6. Only then evaluate the numerical `A` prediction.

## Maximum honest status

The repository now contains the deepest algebraic reduction available without
inventing unsupported numerical input:

```text
Topology and primitive sector: closed conditionally/formally
Finite bridge relational algebra: closed conditionally/formally
Misner--Sharp reduction: closed
Common-action linear integrability: closed
Diagonal exchange identities: closed
PT-odd charge pairing algebra: closed
Relative kinetic-sign no-go: closed
Scale-invariant world-volume dimension audit: closed
RG hierarchy transport to alpha: closed conditionally
Condensate transport to alpha: closed conditionally
Absolute vacuum/coupling/charge normalization: open
Full nonlinear action and null junction: open
Bulk-boundary normalization compatibility: open
```

A claimed numerical answer before the last three open blocks would amount to
choosing a new constant rather than deriving it.
