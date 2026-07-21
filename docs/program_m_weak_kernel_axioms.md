# MF-KER-001 — La base faible suffit-elle ?

## Base testée

MF-KER-001 ne suppose ni gorge, ni métrique, ni dimension 2. Il conserve
seulement :

- une relation d'ordre partiel ;
- l'invariance en loi sous réétiquetage (échangeabilité) ;
- la cohérence par restriction (projectivité).

La théorie des limites de posets confirme que cette base conduit naturellement
à des noyaux d'ordre très généraux. Elle ne sélectionne pas, à elle seule, une
représentation par deux ordres.

## Contre-test

Deux constructions i.i.d. utilisent exactement la même règle produit. La
première possède deux variables latentes, la seconde en possède trois. Les deux
sont des ordres, commutent exactement avec les réétiquetages et avec les
restrictions. L'i.i.d. transforme l'équivariance vérifiée en échangeabilité de
la loi.

| Modèle | Échecs de la base faible | Violations de dimension 2 |
| --- | ---: | ---: |
| Produit 2D | 0/256 | 0/256 |
| Produit 3D | 0/256 | 209/256 |

Ainsi, la base faible ne force pas deux ordres. Ce n'est pas un manque de
puissance statistique : le contre-modèle 3D satisfait mathématiquement les mêmes
trois axiomes.

## Ce que cela nous apprend

Il faut une hypothèse structurelle supplémentaire. Mais écrire directement
« le graphe d'incomparabilité est transitivement orientable » serait seulement
une autre façon d'imposer la dimension 2. La prochaine étape doit comparer des
concepts plus faibles et indépendamment motivés — localité, factorisation,
séparabilité ou une contrainte sur le noyau — et chercher lesquels excluent le
contre-modèle sans contenir déjà la conclusion.

Le script est `scripts/audit_program_m_weak_kernel_axioms.py`; la sortie est
`outputs/program_m/mf_ker_001_weak_kernel_axioms.json`.

## Référence

Svante Janson, *Poset limits and exchangeable random posets*, Combinatorica 31
(2011), arXiv:0902.0306.
