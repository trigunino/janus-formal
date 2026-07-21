# MF-DIM-003 — Pourquoi aucun rang fini ne suffit

## Résultat

Il n'existe pas de rang universel `R` tel que vérifier tous les sous-posets de
taille au plus `R` garantisse une dimension au plus 2.

La famille témoin est celle des couronnes cycliques `C₂n`. Elle contient `n`
points minimaux et `n` points maximaux, avec les relations données par les
arêtes d'un cycle. Chaque couronne a dimension 3. Mais supprimer un seul point
casse le cycle en chemin, et le poset restant a dimension au plus 2. Les
obstructions minimales ont donc des tailles `6, 8, 10, ...` sans borne.

Ce phénomène est classique dans la théorie de la dimension des ordres. La
dimension 3 des couronnes appartient à la famille étudiée par Trotter; la
littérature donne plus généralement la dimension des couronnes généralisées
`S_n^k`.

## Vérification exécutable

MF-DIM-003 construit les couronnes de 6 à 64 points. Pour chacune :

- le reconnaisseur polynomial refuse le poset complet ;
- chacune des suppressions d'un point reçoit deux ordres réalisateurs vérifiés.

Tous les contrôles passent. Cela ne constitue pas la preuve générale à lui
seul, mais vérifie exactement les instances utilisées et protège la construction
contre une erreur d'implémentation.

## Conséquence pour M

Monter mécaniquement à 128, 256, puis davantage ne fermera jamais la prémisse
globale. La bonne prochaine étape doit utiliser une propriété propre au modèle
M — par exemple une représentation par deux variables latentes, une règle de
génération qui préserve la dimension 2, ou un théorème asymptotique excluant les
couronnes et toutes les autres obstructions avec probabilité 1.

Le script est `scripts/audit_program_m_no_finite_dimension_cutoff.py`; la sortie
est `outputs/program_m/mf_dim_003_no_finite_dimension_cutoff.json`.

## Références

- W. T. Trotter, *Dimension of the crown S_n^k*, Discrete Mathematics 8 (1974).
- F. Barrera-Cruz et al., *The Graph of Critical Pairs of a Crown*, Order 37
  (2020), arXiv:1708.06675.
