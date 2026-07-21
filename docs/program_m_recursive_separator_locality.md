# MF-SEP-001 — Localité récursive par séparateurs

## Définition intrinsèque

À partir du seul ordre, on construit son graphe de couverture : deux points sont
reliés lorsqu'ils sont causalement voisins, sans point intermédiaire.

Un morceau est dit localement séparable si l'on peut retirer au plus deux
points de façon que chaque composante restante contienne au plus deux tiers du
morceau. On répète ensuite la même opération dans chaque composante.

Cette définition :

- ne contient aucune coordonnée ;
- ne mentionne ni géométrie, ni gorge, ni dimension ;
- est liée aux séparateurs équilibrés et à la largeur arborescente des graphes.

Elle constitue donc une véritable hypothèse non circulaire.

## Falsification

Les couronnes cycliques de 6 à 32 points possèdent toutes un certificat récursif
de largeur au plus 2. Pourtant, chacune a une dimension d'ordre égale à 3.

| Propriété | Couronnes testées |
| --- | ---: |
| localité récursive de largeur 2 | toutes |
| dimension au plus 2 | aucune |

Un cycle se coupe avec deux points, puis les chemins restants se coupent
récursivement. Cette excellente séparabilité graphique ne contrôle donc pas le
nombre d'ordres nécessaire pour représenter les comparaisons.

## Conclusion

La localité récursive par petits séparateurs est mathématiquement propre mais
trop faible. Elle rejoint la classe « trop faible » de MF-AX-001.

Une éventuelle version enrichie devra contrôler non seulement la taille des
interfaces, mais aussi la manière orientée dont passé et futur se recollent à
travers elles. Cette règle de recollement devra à son tour être définie sans
introduire deux orientations globales cachées.

MF-SEP-002 montre toutefois que la largeur fixe 2 rejette déjà la majorité des
échantillons Minkowski au rang 16. Cette base uniforme est donc abandonnée avant
même d'ajouter une règle orientée.

Le script est `scripts/audit_program_m_recursive_separator_locality.py`; la
sortie est `outputs/program_m/mf_sep_001_recursive_separator_locality.json`.

## Référence

Z. Dvořák et S. Norin, *Treewidth of graphs with balanced separations*,
arXiv:1408.3869.
