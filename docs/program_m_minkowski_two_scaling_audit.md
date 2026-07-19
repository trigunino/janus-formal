# MF-MAN-006 — Changement d'échelle en Minkowski 1+1

## Familles comparées

L'audit conserve la densité `ρ=2` et compare, pour des tailles
`4, 8, 16, 32, 64` :

1. une chaîne placée sur la diagonale `(i,i)` ;
2. la grille carrée de tous les points `(i,j)`.

Ce sont des familles déterministes définies avant le calcul.

## Nombre–volume

Dans le diamant carré de taille linéaire `n`, le volume vaut
`(n-1)²/2`, donc `ρV=(n-1)²`.

- La chaîne contient seulement `n` points. Son erreur relative vaut
  `|n-(n-1)²|/(n-1)²` et tend vers `1` : elle ne remplit pas un volume 1+1.
- La grille contient `n²` points. Son erreur relative vaut
  `(2n-1)/(n-1)²` et tend vers `0` ; elle passe ce contrôle macroscopique
  particulier.

À `n=64`, les erreurs exactes enregistrées sont respectivement
`3905/3969` et `127/3969`.

## Chaîne–temps

Pour la grille, le facteur chaîne-temps `1/2` reproduit exactement le temps
propre sur la diagonale. Mais pour des intervalles dont les extensions nulles
sont dans le rapport `2:1`, l'erreur relative reste

```text
3/(2 sqrt(2)) - 1 ≈ 0.0606601718
```

à toutes les tailles. La convergence nombre-volume ne suffit donc pas : le
réseau régulier conserve une anisotropie directionnelle détectable.

## Relation à la littérature

Saravani et Aslanbeigi étudient précisément les avantages et limites des
réseaux lorentziens 1+1 pour la correspondance nombre-volume
([2014](https://arxiv.org/abs/1403.6429)). Les sprinklings de Poisson jouent un
rôle distinct dans l'absence de direction privilégiée, comme le montre le
théorème de [Bombelli, Henson et Sorkin](https://arxiv.org/abs/gr-qc/0605006).

## Conclusion limitée

Ni la chaîne ni cette grille régulière ne fournissent un certificat de
continuum complet. La chaîne échoue au volume ; la grille réussit un test de
volume macroscopique mais échoue au contrôle temporel multidirectionnel. Cela
ne prouve rien contre un sprinkling aléatoire, une autre discrétisation ou une
dimension différente. Janus et la gorge ne sont pas utilisés.

