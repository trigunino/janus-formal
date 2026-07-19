# MF-WEIGHT-001 — Les relations sélectionnent-elles leurs poids ?

## Témoin exact

On considère uniquement la chaîne primitive `0→1→2`. Son groupe
d'automorphismes est trivial : aucune symétrie non évidente ne peut imposer
l'égalité des deux poids.

Les poids entiers `1,2,3` sont attribués indépendamment aux deux flèches. Les
neuf pondérations obtenues :

- sont invariantes sous tous les automorphismes de la relation ;
- se recollent depuis les morceaux `{0,1}` et `{1,2}` ;
- produisent des distances orientées bien définies.

Même après avoir fixé le premier poids à `1` pour supprimer l'échelle globale,
trois rapports distincts `1:1`, `1:2`, `1:3` subsistent.

## Conclusion

La relation primitive, l'invariance sous renommage et la compatibilité au
collage ne déterminent pas les poids, même à un facteur d'échelle près. La
construction pondérée par plus courts chemins est standard
([MIT, Applied Category Theory, chapitre 2](https://ocw.mit.edu/courses/18-s097-applied-category-theory-january-iap-2019/774c718ff02c6f49e1862440571ea78d_18-s097iap19ch2.pdf)),
mais les poids constituent bien une donnée supplémentaire.

Pour M, trois options restent honnêtes : conserver le coût unité comme choix
minimal déclaré, enrichir les primitives par une mesure/pondération, ou chercher
une loi statistique ou algébrique supplémentaire capable de les déterminer.

Le script est `scripts/audit_program_m_weight_selection_nogo.py`; la sortie est
`outputs/program_m/mf_weight_001_weight_selection_nogo.json`.
