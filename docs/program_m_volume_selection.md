# MF-MAN-009 — La loi nombre-volume lève-t-elle l'ambiguïté ?

## Question

MF-MAN-008 montre que deux paires d'extensions linéaires peuvent reproduire
exactement le même ordre tout en induisant des géométries de rang différentes.
MF-MAN-009 teste si le comptage intrinsèque des intervalles permet de les
départager.

La motivation vient de la condition de plongement fidèle des ensembles
causaux : à densité fixée, le nombre d'éléments doit représenter le volume du
continuum ([Surya, 2019](https://link.springer.com/article/10.1007/s41114-019-0023-1)).
Cette condition est ici testée, pas supposée satisfaite.

## Protocole sans réutilisation des données

Pour chaque ordre partiel non isomorphe de taille au plus cinq :

1. toutes les géométries de rang exactes sont énumérées ;
2. les intervalles stricts de cardinalité maximale calibrent une densité
   globale par moindres carrés exacts ;
3. seuls les autres intervalles servent à comparer les résidus nombre-volume ;
4. une géométrie n'est sélectionnée que si son résidu est strictement minimal.

La séparation calibration/validation est définie par l'ordre avant de regarder
les volumes cibles. Tous les calculs utilisent des fractions rationnelles.

## Résultat exhaustif

| Objets | Classes d'ordres | Classes métriquement ambiguës | Choix unique | Non résolues |
| ---: | ---: | ---: | ---: | ---: |
| 1 | 1 | 0 | 0 | 0 |
| 2 | 2 | 0 | 0 | 0 |
| 3 | 5 | 0 | 0 | 0 |
| 4 | 16 | 1 | 0 | 1 |
| 5 | 63 | 10 | 2 | 8 |

La loi nombre-volume possède donc un pouvoir discriminant réel, mais elle ne
constitue pas un principe général d'unicité. Le premier témoin de MF-MAN-008
reste indécidable parce qu'il ne fournit aucun intervalle de validation.

## Hypothèses externes et limites

Le test introduit explicitement : les rangs comme coordonnées nulles,
`Vol=ΔuΔv/2`, la cardinalité fermée comme estimateur du volume et la perte
quadratique. Ce sont des conventions de la cible Minkowski 1+1, pas des objets
dérivés de `MF-A0`.

La densité est calibrée sur le candidat lui-même ; le protocole évite de tester
sur les mêmes intervalles, mais n'établit aucun modèle statistique. Il ne prouve
ni géométrie émergente, ni unicité continue, ni gorge, ni structure Janus.

## Reproduction

```text
python scripts/audit_program_m_volume_selection.py \
  --output outputs/program_m/mf_man_009_volume_selection.json
```
