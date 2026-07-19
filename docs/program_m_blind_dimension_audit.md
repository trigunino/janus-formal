# MF-DIM-001 — Dimension estimée depuis l'ordre seul

## Invariant et convention

L'estimateur reçoit uniquement une matrice booléenne d'ordre. Il calcule

```text
r = 2 R / (n (n-1)),
```

où `R` est le nombre de paires strictement ordonnées, puis inverse numériquement

```text
r(d) = Γ(d+1) Γ(d/2) / (2 Γ(3d/2)).
```

Cette formule est celle de Myrheim–Meyer pour un intervalle de Minkowski à
grande densité ; la convention est vérifiée par `r(1)=1` et `r(2)=1/2`.
Voir la [revue de Surya, §4.1](https://link.springer.com/article/10.1007/s41114-019-0023-1).

Les coordonnées servent uniquement au générateur des données synthétiques.
Elles sont supprimées avant l'appel de `myrheim_meyer_dimension`. Un test
vérifie aussi l'invariance par permutation simultanée des lignes et colonnes.

## Validation tenue à l'écart

Le protocole `MF-DIM-001-v1` utilise des graines distinctes de MF-MAN-007 :

- graine de base `20260719` ;
- 64 sprinklings jamais utilisés pour ajuster la formule ;
- densité `1024` ;
- seuils fixés : erreur de moyenne ≤ `0,10`, au moins 90 % des estimations
  individuelles dans `[1,70 ; 2,30]`.

Résultats :

- moyenne estimée : `2,004649` ;
- écart-type : `0,038625` ;
- couverture individuelle : `100 %` ;
- gate préenregistré : réussi.

## Contrôles et résultat négatif

- une chaîne totale donne `d=1` ;
- une antichaîne donne une estimation non bornée ;
- la grille régulière anisotrope `24×24` donne pourtant `d≈1,8968`.

Cette grille avait échoué au test chaîne-temps directionnel MF-MAN-006. Deux
structures peuvent donc sembler bidimensionnelles selon `r` tout en différant
géométriquement. Le test Myrheim–Meyer est nécessairement partiel : `d≈2`
signifie seulement « compatible avec cet invariant d'ordre ».

## Limites

L'audit ne reconstruit ni coordonnées, topologie de continuum, métrique ni
dimension locale. Il suppose la formule analytique des intervalles plats pour
interpréter `r`. Courbure, petites régions et causal sets non manifold-like
peuvent biaiser l'estimateur. Aucun élément Janus ou gorge n'est utilisé.

## Reproduction

```text
python scripts/audit_program_m_blind_dimension.py \
  --output outputs/program_m/mf_dim_001_blind.json
```

