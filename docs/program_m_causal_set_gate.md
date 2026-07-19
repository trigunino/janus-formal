# MF-CAUS-001 — Causal-set kinematics gate

## External reference point

The foundational causal-set proposal defines its discrete kinematics as a
locally finite partial order, with the order interpreted macroscopically as
past/future: Bombelli, Lee, Meyer and Sorkin,
[Physical Review Letters 59 (1987)](https://journals.aps.org/prl/abstract/10.1103/PhysRevLett.59.521).
A later review explicitly calls the order *proto-causality* and local finiteness
the discreteness condition: Surya,
[The causal set approach to quantum gravity](https://arxiv.org/abs/1903.11544).

Program M imports the mathematical gate, not the physical interpretation.

## Gate

A skeleton passes `MF-CAUS-001` when every closed order interval

```text
{ z | x <= z and z <= y }
```

is finite. Its partial-order structure was already proved by
`MF-CAUS-000`.

## Proved result and no-go

Every Program M skeleton built from a finite primitive object type is locally
finite. Therefore local finiteness is automatic throughout the current
one-to-four-object census.

```text
finite primitive system
  -> finite quotient skeleton
  -> every interval finite
```

Consequently, `MF-CAUS-001` rejects no finite candidate. It becomes a genuine
filter only for infinite systems or limits.

## Interpretation boundary

Passing the gate proves only the standard order-theoretic kinematics. It does
not prove:

- that the order represents physical signal propagation;
- a time orientation, clock or causal cone;
- faithful embedding into a Lorentzian manifold;
- continuum topology, dimension or metric;
- dynamics or an action.

Continuum recovery is a separate and nontrivial problem in causal-set research;
for example, topology reconstruction has been studied using thickened
antichains rather than the bare Alexandrov topology
([Major, Rideout and Surya](https://arxiv.org/abs/gr-qc/0604124)).

## Next gate

The next useful finite discriminator must inspect order structure rather than
local finiteness: interval profiles, chain/antichain structure and dimension
estimators, all recorded as candidates rather than physical quantities.

