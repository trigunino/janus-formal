# MF-MAN-007 — Audit Poisson préenregistré en Minkowski 1+1

## Protocole fixé avant exécution

Le protocole `MF-MAN-007-v1` est codé comme constante dans le script :

- graine de base `20260718` ;
- 64 répétitions indépendantes ;
- densités `256`, `1024`, `4096` ;
- carré nul unité, de volume lorentzien `1/2` ;
- trois diamants de même volume `1/8` et de rapports nuls `1:1`, `2:1`, `4:1` ;
- seuils nombre-volume, dispersion directionnelle et biais temporel déclarés
  dans `PROTOCOL["thresholds"]`.

Chaque répétition tire exactement un nombre de Poisson de points puis leurs
coordonnées uniformes. Les graines, la version NumPy et tous les seuils sont
enregistrés dans `outputs/program_m/mf_man_007_poisson.json`.

## Observables

Le contrôle nombre-volume compare moyenne et variance des comptages à
`ρ × volume`, dans le carré et dans chacun des trois diamants. Il exige aussi
au moins 95 % des répétitions dans une fenêtre de trois écarts-types.

Le contrôle temporel calcule la plus longue chaîne par une recherche exacte de
sous-suite croissante. En 1+1, la normalisation asymptotique testée est

```text
temps_estimé = nombre_de_pas / sqrt(2 ρ).
```

## Résultats observés

Tous les seuils préenregistrés passent sans modification :

- erreur relative de la moyenne du comptage total : `0,20 %`, `0,20 %`,
  `0,069 %` environ ;
- les comptages régionaux restent sous le seuil de `8 %` et leurs rapports
  variance/moyenne restent dans `[0,60 ; 1,40]` ;
- biais temporel directionnel maximal : `13,55 %`, `12,23 %`, `7,85 %` ;
- dispersion relative entre les trois directions à densité maximale : `0,45 %`.

Le biais temporel diminue donc avec la densité dans cette plage, contrairement
à l'anisotropie persistante de la grille régulière MF-MAN-006.

## Interprétation limitée

C'est une validation statistique reproductible d'un procédé connu vers une
cible Minkowski imposée. Ce n'est pas une preuve de convergence, d'unicité, de
Lorentz-invariance complète, ni une dérivation de Minkowski depuis MF-A0. Les
64 graines ne constituent pas un théorème asymptotique. Les travaux de
[Bombelli, Henson et Sorkin](https://arxiv.org/abs/gr-qc/0605006) justifient le
rôle particulier du sprinkling de Poisson pour éviter une direction privilégiée,
mais leur théorème n'est pas reproduit ici.

Le résultat ne contient ni hypothèse Janus ni gorge. Il valide seulement un
banc d'essai que de futurs candidats issus de M pourront affronter.

## Reproduction

```text
python scripts/audit_program_m_poisson_minkowski2.py \
  --output outputs/program_m/mf_man_007_poisson.json
```

