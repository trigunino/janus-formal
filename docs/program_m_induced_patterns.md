# MF-PAT-001 — Hiérarchie des sous-posets induits

## Pourquoi changer de méthode

Les diagnostics précédents résumaient chaque grand ordre par quelques nombres.
MF-ADV-008 a montré qu'un noyau hiérarchique pouvait tous les reproduire. Ajouter
un cinquième nombre conduirait à une course sans principe d'arrêt.

La théorie des limites de posets fournit un objet plus naturel : pour chaque
rang `k`, la distribution complète du sous-poset obtenu en choisissant `k`
objets. La hiérarchie de toutes ces distributions caractérise la loi limite,
modulo l'équivalence de noyaux appropriée; voir
[Janson, *Poset limits and exchangeable random posets*](https://arxiv.org/abs/0902.0306)
et la représentation sur un espace totalement ordonné de
[Hladký–Máthé–Patel–Pikhurko](https://arxiv.org/abs/1211.2473).

Un rang fini reste seulement un diagnostic. La hiérarchie entière est la cible
mathématique d'identification.

## Première réalisation : rang quatre

Il existe 16 posets non étiquetés à quatre objets. Pour Minkowski 1+1, la
référence est exacte : après avoir fixé l'ordre de la première coordonnée, les
24 permutations relatives possibles de la seconde coordonnée sont équiprobables.
Elles donnent exactement la distribution des 16 motifs.

Chaque lot de test contient 1024 sous-posets indépendants. La distance utilisée
est la variation totale entre son histogramme complet et la référence exacte.
Le seuil `0.0638021` provient du rang conformal 190 parmi 199 lots Minkowski de
calibration; les lots de validation utilisent de nouvelles graines.

## Résultat

| Modèle | Distance moyenne | Intervalle observé | Acceptés |
| --- | ---: | ---: | ---: |
| Minkowski 1+1 | 0.0491 | 0.0329–0.0703 | 60/64 |
| MF-ADV-008 décoré | 0.535 | 0.496–0.574 | 0/64 |

Le motif complet de rang quatre sépare très largement le dernier adversaire,
sans connaître sa construction interne.

Lean prouve que l'induction commute avec la composition des injections et avec
le réétiquetage, définit l'équivalence par toute la hiérarchie des lois finies,
et formalise qu'au rang un tous les posets sont identiques dans
`JanusFormal/Foundations/ProgramMInducedPatternHierarchy.lean`.

## Limites honnêtes

- le rang quatre seul ne prouve pas l'unicité;
- un autre noyau peut reproduire tous les motifs jusqu'à un rang fini;
- l'identification théorique porte sur la hiérarchie infinie et sur une classe
  d'équivalence de noyaux, pas sur des coordonnées uniques;
- aucune dimension, métrique, variété ou gorge n'est encore dérivée.

Le script est `scripts/audit_program_m_induced_patterns.py`; la sortie est
`outputs/program_m/mf_pat_001_induced_patterns.json`.

