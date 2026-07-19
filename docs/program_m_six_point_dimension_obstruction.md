# MF-REP-002 — Premier obstacle observable à deux coordonnées

## Protocole

Le motif standard `S3` comporte trois éléments minimaux et trois maximaux;
chaque minimum précède exactement deux maxima. Sa dimension de Dushnik–Miller
vaut 3, donc il ne peut jamais apparaître dans un ordre produit de deux
coordonnées.

Le test cherche ce motif sans étiquettes dans 262144 sous-posets indépendants
de rang 6 par modèle. Les modèles ont été fixés avant le tirage.

## Résultats

| Modèle | `S3` observés | Lots touchés sur 32 |
| --- | ---: | ---: |
| Minkowski 1+1 | 0 | 0 |
| MF-ADV-009, permuton non uniforme | 0 | 0 |
| MF-ADV-008, niveaux décorés | 3 | 3 |
| Ordre produit à trois coordonnées | 35 | 23 |

L'absence pour les deux premiers modèles est structurelle : ils sont réellement
construits avec deux ordres. Le contrôle tridimensionnel confirme que `S3`
détecte une partie de l'information de dimension supérieure. MF-ADV-008 est
également exclu en principe, même si son signal est rare.

## Limite

`S3` est un témoin suffisant, pas une caractérisation complète de la dimension
2. Ne pas l'observer dans un échantillon fini ne prouve rien à lui seul. Une
reconstruction crédible devra ensuite produire deux ordres cohérents à travers
plusieurs tailles, et pas seulement éviter un motif rare.

Le script est `scripts/audit_program_m_six_point_dimension_obstruction.py`; la
sortie est `outputs/program_m/mf_rep_002_six_point_dimension_obstruction.json`.
