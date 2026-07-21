# MF-KER-002 — Test des axiomes naturels supplémentaires

## Question

Peut-on obtenir deux ordres en ajoutant à MF-KER-001 des principes naturels,
sans écrire directement « dimension 2 » ?

MF-KER-002 teste conjointement :

- des variables i.i.d. sans atomes ;
- une comparaison déterministe et continue presque partout ;
- la symétrie entre les facteurs ;
- la dualité exacte passé/futur ;
- une règle factorisée coordonnée par coordonnée.

## Résultat

Les ordres produits uniformes en dimensions 2 et 3 satisfont tous ces principes.
Pour 128 échantillons de rang 16 :

| Modèle | Échecs des axiomes | Violations de dimension 2 |
| --- | ---: | ---: |
| Produit 2D | 0 | 0/128 |
| Produit 3D | 0 | 107/128 |

La symétrie des coordonnées et la dualité sont revérifiées exactement sur
chaque réalisation. Les autres propriétés découlent de la construction uniforme
i.i.d. et de la règle produit.

## Interprétation

« Factorisé » ne signifie pas « deux facteurs ». Pour obtenir exactement deux
ordres, il faudrait borner le nombre de facteurs à deux — ce qui serait déjà très
proche de la conclusion recherchée.

La localité n'a pas été incluse comme simple mot : sans définition mathématique,
elle ne constitue pas un axiome testable. La prochaine étape doit donc définir
une notion intrinsèque de localité ou de séparabilité, puis vérifier deux choses :

1. elle découle d'une motivation indépendante de la géométrie 1+1 ;
2. elle exclut réellement les modèles 3D sans être équivalente à la dimension 2.

Le script est `scripts/audit_program_m_candidate_kernel_axioms.py`; la sortie
est `outputs/program_m/mf_ker_002_candidate_kernel_axioms.json`.

## Contexte bibliographique

Les ordres aléatoires de dimension `k` sont classiquement obtenus par des points
uniformes de `[0,1]^k` munis de l'ordre produit. La représentation générale par
noyaux reste celle de Janson, *Poset limits and exchangeable random posets*,
arXiv:0902.0306.
