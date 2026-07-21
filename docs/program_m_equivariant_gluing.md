# MF-INV-003 — Collage équivariant des involutions

## Théorème

Un collage identifie certains objets par une relation d'équivalence. Une
involution locale combinée descend au quotient exactement lorsque ces
identifications sont stables sous l'involution :

```text
x ~ y  implique  σx ~ σy.
```

Lean construit alors l'application sur le quotient avec `Quotient.map` et
prouve qu'elle reste involutive. C'est la propriété universelle standard des
quotients pour les applications qui respectent l'équivalence
([documentation Mathlib](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Quot.html)).

## Audit fini

Les 28 combinaisons de deux involutions sur deux points et de sept interfaces
partielles sont vérifiées.

Le contre-exemple minimal utilise deux morceaux échangés `0↔1` mais identifie
seulement les deux points `0`. L'involution envoie cette identification vers
les deux points `1`, qui ne sont pas identifiés : elle ne descend pas.

Si l'interface identifie à la fois `0` avec `0` et `1` avec `1`, le collage est
équivariant et l'involution globale existe.

## Conséquence pour M et P

La branche signée devient composable et recollable avec une règle précise : les
interfaces doivent être équivariantes. Cette règle ne crée pas l'involution ;
elle garantit seulement qu'une involution déjà choisie survit au collage.

Le module formel est
`JanusFormal/Foundations/ProgramMEquivariantQuotient.lean`. Le script est
`scripts/audit_program_m_equivariant_gluing.py`; la sortie est
`outputs/program_m/mf_inv_003_equivariant_gluing.json`.
