# MF-MAN-013 — Calibration conforme de la cohérence d'échelle

## But

MF-MAN-012 montre qu'une identité asymptotique ne peut pas être imposée avec
tolérance zéro à quatre ou cinq objets. MF-MAN-013 calibre donc les fluctuations
de `|2ρa²-1|` sur des sprinklings Poisson indépendants en Minkowski 1+1.

## Protocole figé

- densités physiques : `128, 288, 512, 800` ;
- 199 échantillons de calibration et 400 de validation par densité ;
- rang conforme `180/200`, soit une garantie marginale de 90 % ;
- région bas-gauche pour estimer la densité ;
- région haut-droite, disjointe à mesure nulle près, pour estimer l'échelle des
  plus longues chaînes ;
- graines de validation distinctes des graines de calibration.

La garantie split-conformal suppose l'échangeabilité et concerne un prochain
échantillon à chaque densité ; elle n'est ni simultanée, ni conditionnelle
([JMLR, 2023](https://jmlr.org/papers/volume24/22-0799/22-0799.pdf)). Les
couvertures observées `93,75 %, 89 %, 88 %, 91 %` sont descriptives et ne sont
pas utilisées comme preuve de la garantie.

## Contrôle négatif décisif

À chaque densité, une grille carrée déterministe de même cardinalité donne
exactement :

```text
2ρa² = 1.
```

Elle est donc acceptée avec score zéro par tous les seuils conformes. Le gate
de rejet des contrôles négatifs échoue explicitement.

Ce résultat ne rend pas la relation inutile : sa normalisation et ses
fluctuations Poisson sont maintenant contrôlées. Il prouve toutefois qu'elle
ne distingue pas une distribution de Poisson d'une grille régulière et ne peut
pas établir seule la ressemblance à une variété lorentzienne.

## Limites

La cible Minkowski 1+1, ses régions, la loi de Poisson et les densités restent
externes. Aucune coordonnée, causalité physique, géométrie Janus ou gorge n'est
dérivée. Le résultat négatif est conservé ; il interdit de promouvoir ce seul
diagnostic dans le gate géométrique.

## Reproduction

```text
python scripts/audit_program_m_scale_conformal.py \
  --output outputs/program_m/mf_man_013_scale_conformal.json
```
