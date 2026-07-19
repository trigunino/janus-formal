# MF-LOC-002 — Stabilité multi-échelle et ordre trois-couches

## Protocole

Le même profil d'abondance MF-LOC-001 est évalué à
`N=128,256,512,1024`. Chaque taille possède avant exécution :

- 16 graines d'entraînement et 16 graines de validation disjointes ;
- la même règle de seuil `1,25 × maximum des distances d'entraînement` ;
- une grille régulière de même cardinalité ;
- un ordre trois-couches de type Kleitman–Rothschild.

Le contrôle trois-couches contient `N/4` éléments en bas et en haut, `N/2` au
milieu, des relations adjacentes indépendantes de probabilité `1/2`, puis la
fermeture transitive bas–haut. Le script vérifie explicitement la transitivité.
Cette construction suit la description des ordres KR dans la
[revue de Surya](https://link.springer.com/article/10.1007/s41114-019-0023-1).

## Résultats

| N | seuil figé | Poisson accepté | distance grille | distance trois-couches |
| ---: | ---: | ---: | ---: | ---: |
| 128 | 0,161918 | 100 % | 0,459543 | 1,308116 |
| 256 | 0,069539 | **87,5 %** | 0,329633 | 1,199727 |
| 512 | 0,063560 | 100 % | 0,230676 | 1,254284 |
| 1024 | 0,019803 | 93,75 % | 0,142709 | 1,289553 |

Les grilles et les ordres trois-couches sont rejetés à toutes les tailles. Les
quatre contrôles trois-couches sont des ordres transitifs valides.

Mais le gate global préenregistré **échoue** : à `N=256`, l'acceptation Poisson
est `87,5 %`, sous le minimum fixé à `90 %`. Le seuil n'a pas été élargi après
observation. Ce résultat négatif est conservé dans les tests et la sortie JSON.

## Conclusion

L'abondance des intervalles discrimine fortement les deux adversaires, mais la
règle de calibration par maximum sur seulement 16 entraînements n'est pas
stable à toutes les tailles. MF-LOC-001 ne peut donc pas encore être promu en
gate multi-échelle fiable.

Un futur protocole devra être défini sur de nouvelles graines avec une taille
de calibration justifiée statistiquement ou utiliser la courbe analytique de
Glaser–Surya. Réutiliser les présentes validations pour ajuster le seuil serait
une fuite de données.

Ni Janus, ni gorge, ni géométrie physique ne sont introduits.

## Reproduction

```text
python scripts/audit_program_m_interval_multiscale.py \
  --output outputs/program_m/mf_loc_002_multiscale.json
```

