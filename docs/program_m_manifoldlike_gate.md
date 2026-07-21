# MF-MAN-000 — Why order embedding is insufficient

## Candidate criterion tested

A tempting first definition of manifold-likeness is:

> the skeleton embeds injectively into some ordered target while preserving and
> reflecting order.

MF-MAN-000 proves that this is vacuous. Every partial order embeds into its own
powerset by sending an element to its principal past:

```text
x |-> { y | y <= x }
```

Subset inclusion preserves and reflects the original order exactly. Therefore
every Program M skeleton passes an unconstrained order-embedding test.

## Relation to causal-set research

Causal-set manifold-likeness requires substantially more than order
embeddability. A faithful embedding targets a Lorentzian manifold, preserves
causal order and satisfies a statistical number-to-volume correspondence. The
Hauptvermutung then asks for approximate uniqueness of the recovered continuum;
its precise full formulation remains difficult. See
[Surya's review](https://link.springer.com/article/10.1007/s41114-019-0023-1).

Current research also emphasizes that most large partial orders are not
manifold-like and that there is no general practical recognition algorithm
([Carlip, *Causal sets and an emerging continuum*](https://link.springer.com/article/10.1007/s10714-024-03281-1)).

## Program M consequence

Every future manifold-like witness must name:

- a target class of Lorentzian spaces;
- an order-preserving and order-reflecting injection;
- a density or number-to-volume law with tolerances;
- a scale range;
- statistical assumptions and failure probability;
- recovered dimension/topology/geometry observables;
- an approximate-uniqueness criterion for competing targets.

Without these fields, the witness is rejected as an abstract order embedding.
No Lorentzian manifold, volume measure or faithful embedding has yet been
constructed for Program M candidates.

