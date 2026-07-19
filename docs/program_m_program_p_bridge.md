# MF-PBRIDGE-001 — Ce que Program M doit réellement fournir à Program P

## Recentrage

Program M ne doit pas faire apparaître Minkowski, une gorge ou deux dimensions
par principe. Il doit chercher si les premières entrées utilisées par Program P
peuvent être reconstruites depuis une mathématique plus faible.

Program P possède plusieurs routes alternatives. Il n'existe donc pas une liste
plate d'hypothèses toutes obligatoires.

## Première passerelle, sans géométrie

Le noyau commun le plus faible est :

1. un ensemble ou espace de configurations possibles ;
2. des transformations admissibles entre configurations ;
3. un ensemble de valeurs scalaires et des fonctionnelles candidates.

Avec seulement cela, on atteint l'entrée de P0 : comparer des fonctionnelles et
prouver qu'une structure donnée ne sélectionne pas une action unique. Cette
passerelle ne suppose ni variété, ni métrique, ni dimension, ni gorge.

## Entrées des routes plus fortes

| Route | Données supplémentaires |
| --- | --- |
| P-A | structure différentiable, spécification ou action parente, normalisation |
| P-B | symétries, anomalies et données discrètes |
| P-C | source d'Euler, dérivées, conditions de Helmholtz, cohomologie variationnelle, bords |
| P-D | représentations de groupes et pairings scalaires invariants |
| P-E | base lisse, bundles, jets, naturalité et localité |
| P-F | pairings compatibles, intégration, globalisation et structure de Noether |

Les données PT/Z4, les deux secteurs, la gorge, le mapping torus et SpinC sont
des spécialisations Janus. Elles ne font pas partie du noyau minimal.

## Sorties à ne pas introduire comme entrées

- l'action sélectionnée ou sa classe ;
- les équations d'Euler–Lagrange reconstruites ;
- les identités de Noether dérivées ;
- les multiplicités finales de couplages.

Les supposer au départ annulerait précisément le travail de Program P.

## Nouvelle cible précise pour M

La prochaine construction doit partir de la base relationnelle et produire un
**espace de configurations avec ses transformations**, sans géométrie physique.
Le candidat naturel est le groupoïde des systèmes relationnels :

- objets : configurations relationnelles ;
- flèches : renommages/isomorphismes qui préservent exactement les relations ;
- observables : fonctions constantes sur les classes d'isomorphisme.

Cette structure est mathématique, réutilisable et déjà proche de plusieurs
résultats existants de M. MF-CONF-001 devra vérifier si elle peut être construite
canoniquement sans ajouter de physique.

Le script est `scripts/audit_program_m_program_p_bridge.py`; la sortie est
`outputs/program_m/mf_pbridge_001_program_p_bridge.json`.

## Sources internes

- `docs/program_p_variational_principle.md` ;
- `JanusFormal/Branches/FundamentalGeometryPVariationalPrinciple.lean` ;
- `formal/axioms/program_m_foundations.md`.
