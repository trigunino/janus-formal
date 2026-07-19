# MF-CONF-001 — Groupoïde des configurations relationnelles

## Construction

Une configuration est un système composé :

- d'objets ;
- de noms de relations ;
- d'une règle indiquant quelles relations tiennent entre quels objets.

Une transformation admissible renomme bijectivement les objets et les
relations tout en préservant exactement cette règle. Ces transformations ont :

- une identité ;
- une composition associative ;
- un inverse.

Elles forment donc un groupoïde : plusieurs configurations, reliées uniquement
lorsqu'elles représentent le même contenu relationnel sous des noms différents.

## Preuve et audit

Le module Lean `ProgramMConfigurationGroupoid.lean` construit explicitement
l'identité, l'inverse et la composition, puis prouve les cinq lois d'identité,
d'associativité et d'inversion.

Un audit indépendant utilise le cycle dirigé à trois objets. Il retrouve ses
trois automorphismes, vérifie leur fermeture, leurs inverses et leur
associativité. Le nombre de relations reste constant sur les six renommages :
c'est un premier exemple de fonctionnelle scalaire bien définie modulo les
noms.

## Ce que M fournit maintenant à P

MF-CONF-001 construit réellement deux éléments de la passerelle :

1. un espace de configurations relationnelles ;
2. ses transformations admissibles.

Ce n'est pas encore une variété ni un espace physique. Le mot « espace »
désigne ici une collection mathématique organisée par ses isomorphismes.

## Ce qui manque

La troisième entrée minimale de P reste à construire : une classe déclarée de
fonctionnelles scalaires invariantes sous ces transformations. Le simple nombre
de relations est un exemple, pas une sélection canonique de toutes les
observables pertinentes.

MF-OBS-001 devra donc définir l'interface générale des fonctionnelles sur ce
groupoïde et caractériser exactement leur invariance, sans choisir encore une
action physique.

Le script est `scripts/audit_program_m_configuration_groupoid.py`; la sortie est
`outputs/program_m/mf_conf_001_configuration_groupoid.json`.

Compilation formelle :

```text
lake env lean JanusFormal/Foundations/ProgramMConfigurationGroupoid.lean
```
