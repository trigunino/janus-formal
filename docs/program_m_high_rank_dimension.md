# MF-DIM-002 — Dimension jusqu'au rang 64

## Question simple

Les posets produits par chaque modèle peuvent-ils être décrits comme
l'intersection de seulement deux ordres totaux ? C'est la propriété exacte
attendue d'une géométrie causale discrète en 1+1 dimensions.

## Méthode

L'ancien test énumérait des extensions linéaires et devenait vite inutilisable.
MF-DIM-002 oriente plutôt le graphe d'incomparabilité. Un poset est de dimension
au plus 2 exactement quand ce graphe admet une orientation transitive. Chaque
réponse positive fournit deux ordres dont l'intersection est revérifiée.

L'implémentation a été comparée à la recherche exhaustive sur les 4 824 posets
naturellement étiquetés de rang 6 : aucun désaccord. L'audit fixé utilise 512
tirages pour chacun des quatre modèles aux rangs 8, 12, 16, 24, 32, 48 et 64.

## Résultats

| Modèle | 8 | 12 | 16 | 24 | 32 | 48 | 64 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| Minkowski 1+1 | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| MF-ADV-009 (bidimensionnel) | 0 | 0 | 0 | 0 | 0 | 0 | 0 |
| MF-ADV-008 (décoré) | 0 | 9 | 77 | 324 | 483 | 512 | 512 |
| Ordre produit 3D | 12 | 229 | 416 | 510 | 512 | 512 | 512 |

Les nombres sont les violations parmi 512 tirages. Le test ne confond donc pas
« grande taille » avec « dimension supérieure à 2 » : MF-ADV-009 reste accepté
au rang 64, tandis que les deux contrôles non bidimensionnels sont de plus en
plus nettement rejetés.

## Ce que cela établit — et ce que cela n'établit pas

On peut désormais monter efficacement jusqu'au rang 64, au lieu de s'arrêter au
rang 8. Aucune violation n'a été observée pour Minkowski dans cet audit. Mais
aucun rang fini ne prouve que toutes les réalisations, à toute taille, sont de
dimension 2. La prochaine question n'est donc pas seulement de monter encore le
rang : il faut chercher un argument structurel ou asymptotique qui contrôle tous
les rangs.

Le script est `scripts/audit_program_m_high_rank_dimension.py`; la sortie est
`outputs/program_m/mf_dim_002_high_rank_dimension.json`.
