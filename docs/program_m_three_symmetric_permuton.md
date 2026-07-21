# MF-ADV-009 — Adversaire permuton 3-symétrique

## Construction

On choisit indépendamment chaque point dans l'une des 17 cellules d'un permuton
défini par la permutation `E534BGA9HC2D1687F`, puis on utilise l'ordre produit des
deux coordonnées. Les points étant i.i.d., la loi des ordres finis est
échangeable, projective et ergodique. Elle n'est pas la loi uniforme de Minkowski.

Khovanova et Zhang prouvent que cette permutation est 3-inflatable : les six
motifs de permutation de rang 3 sont exactement équiprobables. Leurs sous-posets
induits ont donc exactement la même loi que la cible jusqu'au rang 3. Leur article
corrige une ancienne affirmation erronée selon laquelle une construction de taille
9 suffisait : [arXiv:1809.08490](https://arxiv.org/abs/1809.08490).

## Test indépendant

Chaque lot contient 8192 motifs. Les seuils sont les maxima de 99 lots Minkowski
de calibration; 32 nouvelles graines testent l'adversaire.

| Rang | Distance moyenne | Lots acceptés |
| ---: | ---: | ---: |
| 2 | 0.00387 | 32/32 |
| 3 | 0.00934 | 31/32 |
| 4 | 0.0502 | 0/32 |

MF-ADV-009 casse donc réellement MF-PAT-002 au rang 3. Le rang 4 le sépare. Dans
le cadre plus riche où les deux ordres de coordonnées sont observables, Král' et
Pikhurko prouvent même que tous les motifs de permutation de rang 4 forcent la loi
uniforme : [arXiv:1205.3074](https://arxiv.org/abs/1205.3074). Pour notre donnée
plus pauvre — seulement le poset produit non étiqueté — cette dernière unicité ne
doit pas être transférée sans preuve supplémentaire.

Le script est `scripts/audit_program_m_three_symmetric_permuton.py`; la sortie est
`outputs/program_m/mf_adv_009_three_symmetric_permuton.json`.
