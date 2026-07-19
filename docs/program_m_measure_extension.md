# MF-MEAS-001 — Extension minimale par une mesure

## Question

Ajouter une mesure additive suffit-il, sans hypothèse géométrique, à déterminer
les poids locaux qui manquent à MF-WEIGHT-001 ?

## Frontière exacte

Sur la chaîne rigide `0→1→2`, les 27 triplets de masses atomiques dans
`{1,2,3}³` sont tous invariants sous les automorphismes relationnels. Même après
normalisation de la première masse à `1`, neuf choix relatifs subsistent.

Une mesure additive **relationnellement invariante** n'est donc pas sélectionnée.

Si l'on ajoute l'axiome plus fort selon lequel les objets sont uniformes sous
toute permutation du support, toutes les masses atomiques deviennent égales.
Lean prouve alors que la masse de tout ensemble fini vaut
`cardinal × masse_atomique` : c'est la mesure de comptage, à une échelle près.
La normalisation de l'atome à `1` la rend unique.

## Interprétation

L'extension possède donc deux versions distinctes :

- **mesure relationnelle libre** : honnête mais encore très ambiguë ;
- **mesure de comptage uniforme** : canonique, mais l'uniformité des objets est
  un nouvel axiome explicite, pas une conséquence des relations.

Même la seconde ne garantit pas une géométrie. MF-MAN-009 a déjà montré que le
comptage des intervalles ne sélectionne que 2 des 10 classes métriquement
ambiguës à cinq objets. La correspondance « nombre = volume » demande encore
une loi statistique ou une limite de densité.

La mesure de comptage est standard dans Mathlib
([cardinalité des ensembles finis](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Finset/Card.html)).

Le module formel est
`JanusFormal/Foundations/ProgramMUniformCountingMeasure.lean`. Le script est
`scripts/audit_program_m_measure_extension.py`; la sortie est
`outputs/program_m/mf_meas_001_measure_extension.json`.
