# MF-REP-003 — Reconstruction cohérente de deux ordres

## Méthode intrinsèque

Pour une extension linéaire candidate `L1`, chaque paire incomparable doit être
inversée dans `L2`, tandis que chaque paire comparable garde son orientation.
Cela détermine entièrement `L2`. Si cette orientation est transitive, `L1` et
`L2` réalisent exactement le poset. Aucune coordonnée du générateur n'est lue.

La reconstruction est faite sur dix objets. Les deux ordres trouvés sont ensuite
restreints aux huit puis aux six premiers objets. Une intersection commute
exactement avec cette restriction : la cohérence aux tailles inférieures est
donc garantie par le témoin du plus grand échantillon.

## Résultats

| Modèle | Réalisations cohérentes sur 32 |
| --- | ---: |
| Minkowski 1+1 | 32 |
| MF-ADV-009, permuton non uniforme | 32 |
| MF-ADV-008, niveaux décorés | 32 |
| Ordre produit à trois coordonnées | 25 |

Sept échantillons tridimensionnels sont rejetés bien qu'aucun ne contienne
`S3`. Il existe donc d'autres obstructions finies à la dimension 2, et la
recherche complète d'un réalisateur est plus forte que MF-REP-002.

MF-ADV-008 passe encore à cette taille. Ce n'est pas contradictoire avec les
trois `S3` trouvés parmi 262144 tirages indépendants par MF-REP-002 : le motif
est simplement très rare.

## Passage au global

Le théorème de compacité donne : un poset infini a une dimension finie `d` si
et seulement si `d` est le supremum des dimensions de ses sous-posets finis.
Ainsi, si tous les sous-posets finis avaient dimension au plus 2, deux ordres
globaux existeraient. Un nombre fini d'échantillons ne permet toutefois jamais
de vérifier cette prémisse universelle.

Enfin, MF-ADV-009 rappelle que l'apparition de deux coordonnées ordinales ne
suffit pas à identifier leur loi : MF-PAT-003, au rang 4, reste nécessaire pour
forcer l'uniformité dans cette classe.

Le script est `scripts/audit_program_m_projective_two_order_reconstruction.py`;
la sortie est
`outputs/program_m/mf_rep_003_projective_two_order_reconstruction.json`.
