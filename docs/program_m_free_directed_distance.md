# MF-DIST-001 — Distance orientée libre

## Construction

On attribue explicitement un coût unité à chaque relation primitive. Le coût de
`x` vers `y` est ensuite la longueur de la plus courte chaîne primitive ; il
vaut l'infini si aucune chaîne n'existe.

Cette construction est purement relationnelle, invariante sous renommage et
satisfait l'inégalité triangulaire orientée. Elle est un exemple de métrique
généralisée au sens de Lawvere, où la symétrie et la finitude ne sont pas
exigées ([Lawvere, 1973](https://lawverearchives.com/)).

L'audit exhaustif vérifie les 65 536 relations sur quatre objets : aucune
violation de l'inégalité triangulaire ou de l'équivariance testée.

## Rapport avec la sélection géométrique

Nous obtenons bien une donnée locale canonique sans supposer Minkowski, une
dimension ou une gorge. Mais elle ne sélectionne pas les deux métriques de
MF-GEO-001 : pour son témoin, les objets isolés restent à distance infinie.
Elle produit donc une géométrie orientée généralisée différente d'une métrique
lorentzienne candidate.

Le coût unité reste une hypothèse explicite. Des poids primitifs différents
produiraient d'autres distances. MF-DIST-001 fournit ainsi un candidat minimal
réutilisable, pas encore le principe qui conduit à la géométrie de P.

Le script est `scripts/audit_program_m_free_directed_distance.py`; la sortie est
`outputs/program_m/mf_dist_001_free_directed_distance.json`.
