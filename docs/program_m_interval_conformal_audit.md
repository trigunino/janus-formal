# MF-LOC-003 — Calibration conforme multi-échelle

## Pourquoi un nouveau protocole

MF-LOC-002 a échoué à `N=256`. Son seuil heuristique n'est pas modifié et ses
graines ne sont pas réutilisées. MF-LOC-003 repart de plages nouvelles à partir
de `2026080000`, séparées en trois ensembles par taille :

- 16 références pour définir le profil central ;
- 39 calibrations pour définir le seuil ;
- 40 validations pour l'évaluation finale.

Les partitions sont deux à deux disjointes et vérifiées par les tests.

## Seuil conforme

Pour un risque `α=0,10`, les scores sont les distances `L¹` au profil central.
Le seuil est le score de rang

```text
ceil((39+1)(1-0,10)) = 36
```

parmi les 39 calibrations. Conditionnellement au jeu de référence, calibration
et prochain sprinkling sont échangeables. La garantie split-conformal donne
alors une couverture marginale finie d'au moins `36/40 = 90 %` à chaque taille.
Cette règle standard est décrite dans la littérature sur la prédiction conforme,
par exemple dans [JMLR 2023](https://jmlr.org/papers/volume24/22-0799/22-0799.pdf).

## Résultats nouveaux

| N | seuil conforme | couverture observée | distance grille | distance trois-couches |
| ---: | ---: | ---: | ---: | ---: |
| 128 | 0,112945 | 95 % | 0,448315 | 1,323347 |
| 256 | 0,082620 | 97,5 % | 0,335639 | 1,203307 |
| 512 | 0,032261 | 90 % | 0,226012 | 1,256720 |
| 1024 | 0,016454 | 90 % | 0,142522 | 1,290837 |

Tous les gates préenregistrés passent : borne conforme correcte, couverture
empirique au-dessus du plancher déclaré de 80 %, et rejet des grilles et ordres
trois-couches aux quatre tailles.

## Portée de la garantie

La couverture de 90 % est **marginale par taille** sous échangeabilité. Elle
n'est ni simultanée sur les quatre tailles, ni conditionnelle à chaque ordre,
ni une probabilité de manifold-likeness. Elle garantit seulement le taux
d'acceptation d'un nouveau sprinkling provenant de la même distribution de
référence.

Le rejet des deux adversaires est expérimental, pas couvert par le théorème
conforme. D'autres non-variétés peuvent encore imiter le profil. La cible
Minkowski 1+1 reste imposée extérieurement ; Janus et la gorge sont absents.

## Reproduction

```text
python scripts/audit_program_m_interval_conformal.py \
  --output outputs/program_m/mf_loc_003_conformal.json
```

