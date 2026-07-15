# Programme B — contrainte secondaire en minisuperspace

## Résultat

Sur l'espace de phase diagonal FLRW
`(a_plus, p_plus, a_minus, p_minus)`, le Hamiltonien candidat est linéaire
dans les deux lapses :

`H = N_plus C_plus + N_minus C_minus`.

Avec `r = a_minus/a_plus`, les contraintes utilisées sont

`C_plus = -p_plus^2/(12 M_plus^2 a_plus) + a_plus^3 B(r)`,

`C_minus = -p_minus^2/(12 M_minus^2 a_minus) + a_plus^3 A(r)`,

où

`B(r)=beta0+3 beta1 r+3 beta2 r^2+beta3 r^3` et
`A(r)=beta1+3 beta2 r+3 beta3 r^2+beta4 r^3`.

Le calcul symbolique donne une fonction non identiquement nulle

`S = {C_plus,C_minus}`.

Elle se factorise en

`S = (M_minus^2 a_minus p_plus - M_plus^2 a_plus p_minus)`
`*(beta1 a_plus^2 + 2 beta2 a_plus a_minus + beta3 a_minus^2)`
`/(2 M_plus^2 M_minus^2 a_plus a_minus)`.

Il existe donc deux branches : une branche cinématique reliant les moments,
et une branche algébrique spéciale du potentiel. La seconde doit être
traitée séparément car elle peut modifier le rang des contraintes.

Le jacobien de `(C_plus,C_minus,S)` par rapport à
`(a_plus,p_plus,a_minus,p_minus)` a un rang exact égal à 3 sur un point
rationnel construit avec les résidus exacts `(0,0,0)`. Cela fournit, sur la
surface des contraintes, un témoin constructif d'indépendance locale de `S`;
ce n'est pas encore une preuve globale, notamment sur la branche algébrique
spéciale.

La conservation des contraintes primaires donne exactement

`dot(C_plus) = N_minus S`,

`dot(C_minus) = -N_plus S`.

Pour des lapses non nuls, la cohérence impose donc `S = 0` : c'est la
contrainte secondaire candidate du modèle réduit. Sa conservation,
`dot(S)={S,H}`, est linéaire dans les lapses et fixe génériquement une
combinaison de lapses.

## Portée

Ce résultat avance le bloc canonique B sans dépendre du programme P. Il
n'établit pas encore l'élimination du mode de Boulware–Deser dans la théorie
de champs complète. Il reste à reproduire le rang des contraintes après la
redéfinition des shifts dans l'ADM non homogène, puis à vérifier
l'indépendance globale de `S`.

Terminologie : `C_plus` et `C_minus` sont ici les contraintes obtenues par
variation des lapses. Dans le comptage de Dirac complet, les moments conjugués
des lapses sont les contraintes primaires strictes.

## Artefacts vérifiables

- `scripts/derive_bimetric_minisuperspace_dirac_constraints.py`
- `tests/test_derive_bimetric_minisuperspace_dirac_constraints.py`
- `outputs/reports/bimetric_minisuperspace_dirac_constraints.json`
- `outputs/reports/bimetric_minisuperspace_dirac_constraints.md`
