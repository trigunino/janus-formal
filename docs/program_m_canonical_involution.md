# MF-INV-001 — Une involution peut-elle émerger canoniquement ?

## Critère de naturalité

Une involution construite uniquement depuis une relation doit être transportée
par tout renommage. Pour un automorphisme de la relation, cela implique que
l'involution choisie commute avec tous les automorphismes : elle doit appartenir
au centre du groupe d'automorphismes.

## Contre-exemple minimal

La relation vide sur trois objets possède les six permutations comme
automorphismes. Elle admet trois involutions non triviales, les trois échanges
de deux objets. Pourtant aucune n'est centrale : seule l'identité commute avec
toutes les permutations.

Ainsi :

```text
existence de plusieurs involutions
≠ sélection canonique d'une involution.
```

L'audit vérifie ce critère sur les 512 relations binaires à trois objets. Le
témoin vide suffit déjà à réfuter un constructeur universel qui produirait
toujours une involution non triviale sans choix supplémentaire. Cela correspond
au fait classique que le centre de `Sₙ` est trivial pour `n≥3`
([preuve de référence](https://proofwiki.org/wiki/Center_of_Symmetric_Group_is_Trivial)).

## Conséquence pour M

Certaines relations particulières peuvent posséder une involution centrale
non triviale et donc intrinsèquement reconnaissable. Mais la base relationnelle
générale ne la garantit pas. La branche signée doit donc :

- soit rester conditionnelle à une involution fournie ;
- soit restreindre explicitement les configurations à une classe où une
  involution centrale non triviale existe et est unique.

La seconde option est testable, mais constitue un nouvel axiome de sélection.

Le script est `scripts/audit_program_m_canonical_involution.py`; la sortie est
`outputs/program_m/mf_inv_001_canonical_involution.json`.
