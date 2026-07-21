# MF-MAN-014 — Test des fluctuations locales de comptage

## Idée simple

Une grille et un sprinkling Poisson pouvaient tous deux satisfaire exactement
la cohérence globale `2ρa²=1`. Ils diffèrent localement : une grille répartit
les points trop régulièrement, tandis qu'un processus de Poisson produit des
fluctuations dont la variance égale la moyenne.

Le rôle privilégié du sprinkling Poisson dans la correspondance nombre-volume
est étudié notamment par
[Saravani et Aslanbeigi](https://arxiv.org/abs/1403.6429). La revue de
[Surya](https://link.springer.com/article/10.1007/s41114-019-0023-1) rappelle
la loi de Poisson utilisée dans les plongements fidèles.

## Statistique

Le carré de coordonnées nulles est découpé en seize cellules de même volume.
Pour leurs nombres de points `N_i`, le test calcule :

```text
F = variance(N_i) / moyenne(N_i).
```

Un sprinkling Poisson attend `F≈1`. Une grille carrée alignée donne exactement
`F=0`. Une chaîne diagonale donne au contraire une dispersion excessive.

## Calibration indépendante

Le protocole est figé avant les contrôles :

- densités `128, 288, 512, 800` ;
- 199 sprinklings de calibration ;
- intervalle conforme bilatéral défini par les rangs 10 et 190 ;
- 400 nouvelles réalisations de validation ;
- garantie marginale de couverture 90 % sous échangeabilité.

Les couvertures observées sont `91,25 %, 92,75 %, 89,5 %, 91,25 %`. Toutes les
grilles carrées et toutes les chaînes diagonales sont rejetées aux quatre
densités. Le contrôle qui trompait MF-MAN-013 est donc séparé par MF-MAN-014.

## Ce que cela prouve — et ne prouve pas

Le test montre que la cohérence d'échelle et les fluctuations locales apportent
des informations indépendantes. Il ne prouve pas que ces deux tests suffisent
contre toutes les constructions adverses.

Surtout, les seize cellules sont définies dans les coordonnées nulles de la
cible externe. Le test n'est donc pas encore une reconstruction sans
coordonnées ni une preuve d'invariance de Lorentz. Une version future devra
remplacer ce quadrillage par une famille de régions définie intrinsèquement ou
auditer explicitement les changements de repère.

## Reproduction

```text
python scripts/audit_program_m_count_fluctuations.py \
  --output outputs/program_m/mf_man_014_count_fluctuations.json
```
