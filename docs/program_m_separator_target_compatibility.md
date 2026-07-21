# MF-SEP-002 — La localité accepte-t-elle la cible ?

## Pourquoi ce contrôle était nécessaire

MF-SEP-001 avait montré qu'une largeur récursive fixée à 2 accepte les couronnes
de dimension 3. Mais une hypothèse candidate doit aussi être nécessaire pour la
cible supposée. MF-SEP-002 mesure donc la largeur minimale sur des ordres
Minkowski 1+1 et sur un contrôle produit 3D.

## Résultats

Nombre d'échantillons dont la largeur récursive est au plus 2, sur 128 :

| Modèle | Rang 8 | Rang 12 | Rang 16 |
| --- | ---: | ---: | ---: |
| Minkowski 1+1 | 128 | 111 | 42 |
| Produit 3D | 128 | 125 | 100 |

Au rang 16, la largeur exacte observée pour Minkowski vaut 3 dans 74 cas et 4
dans 12 cas. Le contrôle 3D passe en réalité plus souvent le seuil 2 que la
cible 2D.

## Conclusion

La largeur récursive fixée à 2 échoue des deux côtés :

- elle accepte les couronnes de dimension 3 ;
- elle rejette une majorité des échantillons Minkowski au rang 16.

Ajouter une règle de recollement orienté sur cette base ne réparerait pas le
fait que la base elle-même n'est pas nécessaire pour la cible. La piste des
petits séparateurs uniformément bornés est donc arrêtée.

Une éventuelle notion de localité devra être asymptotique et autoriser une
largeur croissante avec le rang. Mais il faudra d'abord établir une loi
d'échelle indépendante, puis vérifier qu'elle distingue réellement 1+1 de 3D.

Le script est `scripts/audit_program_m_separator_target_compatibility.py`; la
sortie est `outputs/program_m/mf_sep_002_separator_target_compatibility.json`.
