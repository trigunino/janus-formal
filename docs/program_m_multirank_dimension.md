# MF-DIM-001B — Dimension à plusieurs rangs

## Protocole

MF-DIM-001B cherche une paire complète d'ordres réalisateurs pour chaque
sous-poset aux rangs 6, 7 et 8. Il ne se limite pas à `S3`. Les checkpoints sont
`256`, `1024` et `4096` par modèle et par rang.

Le risque familial `5 %` est réparti simultanément entre quatre modèles, trois
rangs et tous les checkpoints par `0,05/[4×3×s(s+1)]`. Les intervalles de
Clopper–Pearson sont bilatéraux : chaque queue reçoit la moitié de l'allocation.

## Résultats à 4096 tirages par cellule

| Modèle | Rang 6 | Rang 7 | Rang 8 |
| --- | ---: | ---: | ---: |
| Minkowski 1+1 | 0 | 0 | 0 |
| MF-ADV-009 | 0 | 0 | 0 |
| MF-ADV-008 | 0 | 0 | 2 |
| Ordre produit 3D | 0 | 41 | 137 |

Pour zéro violation, la borne supérieure simultanée vaut `0,00211`. Pour le
contrôle 3D, les intervalles deviennent strictement positifs au rang 7
(`[0,00536 ; 0,0168]`) et au rang 8 (`[0,0243 ; 0,0447]`). MF-ADV-008 révèle
également une probabilité positive au rang 8, avec une borne inférieure faible
mais non nulle (`4,58e-6`).

Le contrôle 3D passe entièrement au rang 6 avec ces graines, alors que son
incompatibilité avec deux ordres devient nette dès le rang 7. Un rang unique
aurait donc donné une conclusion trompeuse.

## Limite

Les rangs supérieurs à 8 restent ouverts. Une absence de violation sur ces trois
rangs ne prouve pas la dimension globale 2. Le coût de la recherche exacte croît
rapidement avec le nombre d'extensions linéaires; le prochain successeur devra
utiliser un algorithme polynomial de reconnaissance des posets de dimension 2
pour poursuivre plus haut sans changer la propriété testée.

Le script est `scripts/audit_program_m_multirank_dimension.py`; la sortie est
`outputs/program_m/mf_dim_001_multirank_dimension.json`.
