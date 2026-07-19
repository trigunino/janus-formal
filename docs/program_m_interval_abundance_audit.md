# MF-LOC-001 — Abondance des intervalles sans coordonnées

## Observable

Pour chaque paire stricte `x<y`, l'audit compte les éléments intérieurs
`z` tels que `x<z<y`. Il construit l'histogramme normalisé des tailles
`0,…,20`, puis un dernier bac pour toutes les tailles supérieures.

L'entrée est uniquement la matrice d'ordre. Le profil est invariant sous
renommage, ce que vérifie un test. Cette famille d'observables suit le critère
de localité proposé par
[Glaser et Surya](https://arxiv.org/abs/1309.3403), qui le présentent comme une
condition nécessaire, non suffisante, de manifold-likeness.

## Calibration séparée

Le protocole `MF-LOC-001-v1` fixe :

- 512 éléments par ordre ;
- 32 sprinklings d'entraînement, graines `2026072000…2026072031` ;
- 32 sprinklings de validation, graines `2026073000…2026073031` ;
- distance `L¹` au profil moyen d'entraînement ;
- seuil figé égal à `1,25 ×` la plus grande distance d'entraînement ;
- acceptation requise d'au moins 90 % des validations ;
- grille régulière `16×32` comme contrôle négatif déclaré.

Les plages de graines sont disjointes. Le seuil obtenu uniquement sur
l'entraînement est `0,0438621`.

## Résultats

- les 32 ordres Poisson tenus à l'écart sont acceptés : `100 %` ;
- la grille anisotrope est à distance `0,222770`, soit plus de cinq fois le
  seuil, et elle est rejetée ;
- les deux gates préenregistrés passent.

MF-DIM-001 donnait pourtant `d≈1,897` à cette même grille. Le profil
d'intervalles ajoute donc une information discriminante que la seule fraction
d'ordre avait perdue.

## Limites

Le test compare à une référence Minkowski 1+1 apprise et ne dérive pas cette
référence. Une autre structure non manifold-like pourrait imiter le même
histogramme. Le choix de 512 éléments et du cutoff 20 est fini ; courbure,
densités différentes et stabilité multi-échelle restent à tester. Il n'y a ni
preuve asymptotique, ni coordonnées reconstruites, ni hypothèse Janus ou gorge.

## Reproduction

```text
python scripts/audit_program_m_interval_abundance.py \
  --output outputs/program_m/mf_loc_001_intervals.json
```

