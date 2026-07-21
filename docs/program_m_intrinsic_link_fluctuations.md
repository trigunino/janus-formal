# MF-MAN-015 — Fluctuations intrinsèques des liens immédiats

## Objectif

MF-MAN-014 rejette les grilles, mais utilise un quadrillage de coordonnées.
MF-MAN-015 remplace ce quadrillage par une quantité construite uniquement avec
l'ordre fini.

Un **lien immédiat** est une paire `x<y` sans objet `z` entre les deux. Dans un
ensemble causal, ces liens forment le diagramme de Hasse. Leur forte connectivité
est une caractéristique connue des sprinklings de Poisson
([Surya, 2019](https://link.springer.com/article/10.1007/s41114-019-0023-1)).

## Statistique

Pour chaque objet, le test compte :

- ses liens immédiats sortants ;
- ses liens immédiats entrants.

Il calcule pour chaque distribution le rapport variance/moyenne, puis prend la
moyenne des deux rapports. Cette symétrisation rend le résultat exactement
inchangé si toutes les flèches sont inversées.

Le calcul reçoit seulement une matrice d'ordre. Les coordonnées utilisées pour
générer les références et les grilles sont supprimées avant le calcul.

## Protocole

- cardinalités `144, 256, 576, 784` ;
- 79 références de calibration et 80 validations fraîches par taille ;
- intervalle conforme bilatéral, rangs 4 et 76 sur 80 ;
- garantie marginale de 90 % sous échangeabilité ;
- grilles carrées et chaînes totales comme contrôles négatifs.

Résultat : toutes les grilles et toutes les chaînes sont rejetées aux quatre
tailles. Les couvertures Poisson observées sont descriptives ; une valeur
ponctuelle sous 90 % ne réfute pas la garantie marginale conforme.

## Invariances vérifiées

- renommage arbitraire des objets : invariance exacte ;
- inversion globale de l'orientation : invariance exacte ;
- coordonnées : absentes de la statistique.

Un premier essai utilisant seulement la taille totale des futurs a échoué : les
grilles chevauchaient la plage Poisson. Cet échec est conservé dans le rapport.

## Limites

Le test distingue les contrôles actuels mais ne prouve pas la ressemblance à
une variété, une dimension ou une métrique. Sa référence Poisson Minkowski 1+1
reste externe. D'autres ordres artificiels pourraient reproduire la même
distribution de degrés de liens ; ils devront être recherchés explicitement.

## Reproduction

```text
python scripts/audit_program_m_intrinsic_link_fluctuations.py \
  --output outputs/program_m/mf_man_015_intrinsic_link_fluctuations.json
```
