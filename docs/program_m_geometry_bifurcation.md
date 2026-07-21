# MF-GEO-001 — Bifurcation géométrique depuis la base de M

## Question

La sortie minimale obtenue par MF-FREE-001 sélectionne-t-elle déjà une
géométrie, ou plusieurs géométries restent-elles compatibles ?

## Test direct

On part de quatre objets et d'une seule relation primitive `0→1`. Aucune
topologie, coordonnée ou métrique n'est fournie. La construction libre de M
ajoute seulement les quatre boucles réflexives : elle produit l'ordre formé de
la chaîne `0<1` et de deux objets isolés.

On transmet ensuite exactement cet ordre à la reconstruction de rang déjà
auditée dans MF-MAN-008. Ses six réalisations compatibles se répartissent en
deux classes métriques non équivalentes, même après quotient par les
automorphismes de l'ordre.

## Conclusion

La base actuelle de M ne sélectionne pas une géométrie unique. Elle autorise
bien plusieurs géométries candidates, ce qui rend M réutilisable, mais il
manque un principe mathématique de reconstruction ou de sélection pour choisir
entre elles. Introduire directement la métrique voulue à ce point serait
précisément tricher.

Ce résultat est fini et vise la reconstruction particulière par rangs. Il ne
réfute pas les résultats plus forts obtenus avec des hypothèses continues ou
probabilistes. La littérature des ensembles causaux formule cette frontière
comme le problème de la Hauptvermutung ; voir la
[revue de Surya (2019)](https://link.springer.com/article/10.1007/s41114-019-0023-1)
et le récent résultat probabiliste
[Braun (2025)](https://arxiv.org/abs/2507.01907).

Le script reproductible est
`scripts/audit_program_m_geometry_bifurcation.py`; sa sortie est
`outputs/program_m/mf_geo_001_geometry_bifurcation.json`.
