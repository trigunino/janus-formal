# MF-AX-001 — Frontière des hypothèses

## But

Avant d'ajouter un nouvel axiome à Program M, on demande s'il est trop faible,
circulaire, ou réellement candidat. Aucun axiome n'est promu seulement parce
qu'il porte un nom intuitif comme « localité » ou « séparateur causal ».

## Carte actuelle

| Hypothèse | Classe | Pourquoi |
| --- | --- | --- |
| ordre + échangeabilité + projectivité | trop faible | contre-modèle produit 3D |
| i.i.d., sans atomes, continu p.p., symétrique, factorisé | trop faible | même contre-modèle 3D |
| graphe de couverture planaire ou de faible largeur arborescente | trop faible | les couronnes cycliques ont dimension 3 |
| deux familles réversibles de paires critiques | circulaire | caractérise déjà un réalisateur à deux ordres |
| incomparabilités transitivement orientables | circulaire | équivaut à la dimension au plus 2 |
| dimension booléenne au plus 2 | circulaire | elle coïncide ici avec la dimension classique |
| localité récursive par séparateurs intrinsèques | trop faible | MF-SEP-001 : les couronnes la satisfont avec largeur 2 |

Le test exécutable vérifie les contre-modèles finis utilisés pour les trois
premières lignes. Les trois équivalences circulaires viennent de résultats
mathématiques, pas d'une fréquence observée.

## Résultat sur les « séparateurs causaux »

La première formulation tentée — couvrir les paires critiques par deux familles
réversibles — échoue conceptuellement : le théorème des paires critiques dit
précisément qu'une telle couverture fournit deux extensions linéaires
réalisatrices. Elle ne fait donc pas émerger deux ordres ; elle les renomme.

## Frontière ouverte

MF-SEP-001 a depuis défini et réfuté la version fondée seulement sur la taille
des séparateurs. Une version enrichie devrait définir, à partir du seul ordre :

- comment l'orientation passé/futur traverse un séparateur ;
- comment des morceaux se recollent sans orientations globales cachées ;
- une borne qui ne mentionne aucune dimension cible ;
- une motivation valable aussi hors de Minkowski 1+1.

Ensuite, la priorité sera de tenter de la réfuter avec les couronnes et les
ordres produits 3D. Une implication vers deux ordres ne sera cherchée que si
elle survit à cette falsification.

Le script est `scripts/audit_program_m_axiom_boundary.py`; la sortie est
`outputs/program_m/mf_ax_001_axiom_boundary.json`.

## Références

- W. T. Trotter et B. Walczak, *Boolean dimension and local dimension*,
  arXiv:1705.09167.
- F. Barrera-Cruz et al., *Comparing Dushnik–Miller Dimension, Boolean
  Dimension and Local Dimension*, arXiv:1710.09467.
