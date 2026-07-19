# Program M — Archive et checkpoint courant

Ce fichier est le point d'entrée stable de Program M. Il sépare ce qui est
acquis, réfuté et encore ouvert. Le registre détaillé reste
[`program_m_provenance_register.md`](program_m_provenance_register.md).

**Statut opérationnel au 19 juillet 2026 : fondations consolidées ; prochaine
intégration géométrique en attente de Program P.** Voir
[`program_m_status.md`](program_m_status.md).

Le langage de coefficients est désormais explicitement capable de valeurs
signées. Le cas non signé est une restriction de ce langage, pas une base
concurrente. L'involution non triviale et la loi impaire restent toutefois des
structures optionnelles supplémentaires.

## État au checkpoint MF-ARC-001

### Acquis

- Une relation dirigée produit canoniquement un squelette causal, mais la
  topologie seule perd de l'information.
- La dimension 2 peut être reconnue intrinsèquement en temps polynomial et un
  témoin positif fournit deux ordres vérifiables.
- Minkowski 1+1 et MF-ADV-009 n'ont montré aucune violation jusqu'au rang 64
  dans MF-DIM-002.
- Des obstructions minimales de dimension 3 existent à des rangs arbitrairement
  grands : aucun cutoff fini universel n'est possible (MF-DIM-003).

### Réfuté

- Les statistiques scalaires, la seule topologie et plusieurs compressions ne
  déterminent pas une géométrie unique.
- Ordre partiel + échangeabilité + projectivité ne forcent pas deux ordres
  (MF-KER-001).
- Ajouter continuité presque partout, absence d'atomes, déterminisme, symétrie,
  dualité et factorisation ne suffit toujours pas (MF-KER-002).

### Ouvert

- Trouver une hypothèse structurelle indépendante qui exclut les modèles 3D
  sans reformuler implicitement « dimension 2 ».
- Définir mathématiquement une localité intrinsèque avant de la tester.
- Passer de preuves conditionnelles sur tous les rangs à une construction issue
  de la base faible.
- Relier ensuite seulement cette structure aux observations et à Program P.

MF-AX-001 avait laissé ouverte la localité récursive. MF-SEP-001 l'a définie
intrinsèquement, puis réfutée comme condition suffisante : les couronnes ont des
séparateurs récursifs de largeur 2 tout en ayant dimension 3. Une règle orientée
de recollement reste ouverte.

MF-SEP-002 a ensuite vérifié la compatibilité avec la cible : au rang 16,
seulement 42/128 échantillons Minkowski ont une largeur au plus 2, contre
100/128 pour le contrôle 3D. La piste de largeur uniformément bornée est donc
arrêtée ; une éventuelle localité devra avoir une loi d'échelle.

MF-SEL-002 applique le théorème MF-OBS-000 au profil d'axiomes : puisque les
produits 2D et 3D ont le même profil, aucun sélecteur qui ne lit que ce profil
ne peut les distinguer. Une méthode d'entropie exige donc une contrainte
supplémentaire, explicitement sourcée.

MF-PBRIDGE-001 recentre ensuite le programme : la première entrée de P à faire
émerger n'est pas une géométrie, mais un espace de configurations, ses
transformations admissibles et ses fonctionnelles scalaires. Les données de
variété, métrique, gorge et PT appartiennent à des routes ultérieures.

MF-CONF-001 construit les deux premières données : les systèmes relationnels
forment les configurations et leurs renommages exacts forment un groupoïde
prouvé en Lean. Les fonctionnelles scalaires invariantes restent la prochaine
entrée à organiser.

MF-OBS-001 construit cette troisième interface : une fonctionnelle scalaire est
admissible lorsqu'elle est constante le long des isomorphismes. Lean prouve les
lois de transport et l'audit rejette une fausse observable dépendant du nom
`0`. Aucune fonctionnelle n'est encore sélectionnée comme action.

MF-COMP-002 ajoute une composition canonique : la somme disjointe, associative
et commutative à isomorphisme près, avec unité vide. Il prouve aussi que les
relations traversantes sont des données supplémentaires : deux morceaux d'un
point donnent déjà quatre collages interactifs possibles.

MF-GLUE-001 construit ensuite le collage libre le long d'une interface
compatible : les deux copies de l'interface sont identifiées par un pushout et
seules les relations héritées sont conservées. L'interface reste une entrée ;
aucune relation traversante ni fermeture transitive n'est inventée.

MF-GLUE-002 vérifie sur un diagramme cyclique que le collage libre est
indépendant de l'ordre des trois interfaces et invariant sous renommage. Il
réfute cependant l'unicité d'un global arbitraire : une relation entre points
jamais vus ensemble localement peut être ajoutée sans changer les morceaux.

MF-DESC-001 fixe la bifurcation : les relations primitives descendent par
témoin local et donnent un global minimal unique ; la reachabilité est calculée
ensuite par fermeture globale et peut traverser plusieurs morceaux. Dans
`0→1→2`, `0→2` est globalement atteignable sans être primitif localement.

MF-DESC-002 généralise ce mécanisme en Lean : sous descente primitive, la
reachabilité globale équivaut exactement aux chaînes de pas localement témoins.
Un audit de 4 096 diagrammes ne trouve aucun désaccord. Fermer séparément les
morceaux puis unir reste incorrect.

MF-FREE-001 caractérise la structure ainsi obtenue : la reachabilité est le
préordre libre, donc le plus petit préordre engendré par les pas primitifs. Sa
propriété universelle est prouvée en Lean et l'audit exhaustif des 512 relations
sur trois points ne trouve aucun contre-exemple. Rien de géométrique n'apparaît
encore à ce stade.

MF-GEO-001 relie enfin cette base au test géométrique existant : une seule
flèche primitive produit un préordre libre possédant six réalisations de rang,
réparties en deux classes métriques non équivalentes. La base de M autorise donc
plusieurs géométries, mais ne fournit pas encore leur principe de sélection.

MF-GEO-002 teste le premier principe candidat. Deux morceaux et leur interface
ont chacun une classe métrique unique, mais leur collage global en a deux. La
compatibilité locale au collage ne suffit donc pas tant que certaines paires ne
sont jamais observées ensemble.

MF-REF-001 isole la réparation minimale : chaque paire doit finir dans un même
morceau. Lean prouve que cette condition est exactement nécessaire et
suffisante pour l'unicité de données globales portées par les paires. Elle ferme
le trou de MF-GEO-002, mais ne construit ni ne sélectionne les valeurs locales.

MF-DIST-001 construit une première valeur locale canonique : le plus court coût
orienté avec coût unité sur les flèches primitives. Les 65 536 relations de
rang quatre satisfont les tests. Cette géométrie de Lawvere est toutefois plus
faible et différente d'une métrique lorentzienne ; elle ne choisit pas les
géométries candidates de MF-GEO-001.

MF-WEIGHT-001 teste si le coût unité peut être dérivé. Sur la chaîne rigide à
deux flèches, neuf pondérations sont toutes invariantes et compatibles au
collage. Après fixation de l'échelle, trois rapports distincts subsistent : les
relations seules ne sélectionnent donc pas leurs poids.

MF-MEAS-001 ouvre l'extension mesurée. Une mesure additive seulement invariante
sous la relation reste libre ; neuf rapports de masses survivent après
normalisation sur la chaîne témoin. Une uniformité complète des objets force en
revanche la mesure de comptage, à une échelle près, mais constitue un nouvel
axiome et ne suffit pas encore à sélectionner la géométrie.

MF-SIGN-001 sépare ensuite charge et masse. Une involution munie d'une loi
impaire force des charges opposées et une somme nulle, mais pas leur magnitude.
La même charge ne peut être à la fois invariante et impaire sauf si elle est
nulle : les secteurs signés exigent donc une structure tordue explicitement
ajoutée, sans interprétation physique à ce stade.

MF-INV-001 demande si cette involution peut elle-même émerger. La relation vide
sur trois objets admet trois involutions non triviales, mais aucune n'est
canonique : seule l'identité est centrale dans son groupe d'automorphismes. Une
involution signée universelle ne découle donc pas de la base relationnelle.

MF-INV-002 teste la composition. L'unicité d'une involution centrale n'est pas
stable par somme disjointe. En revanche, une involution explicitement conservée
sur chaque morceau se compose toujours composante par composante dans l'audit.
La branche signée doit donc traiter l'involution comme structure transportée.

MF-INV-003 ferme le collage : l'involution transportée descend au quotient si
et seulement si elle préserve les identifications de l'interface. Lean prouve
l'involution globale ; l'audit accepte les interfaces appariées et rejette une
identification isolée dont la partenaire n'est pas recollée.

MF-PBRIDGE-002 construit enfin l'adaptateur signé vers P. Toute charge réelle
impaire non nulle est factorisée en label `JanusCharge` et magnitude positive ;
l'involution devient exactement `ptCharge`. La géométrie, la gorge,
l'interprétation en masse, la dynamique et l'action restent hors adaptateur.

## Dernière séquence archivée

| ID | Question | Conclusion | Note |
| --- | --- | --- | --- |
| MF-DIM-001B | Que voit-on aux rangs 6–8 ? | les obstructions apparaissent avec le rang | [note](program_m_multirank_dimension.md) |
| MF-DIM-002 | Peut-on monter sans recherche factorielle ? | oui, jusqu'au rang 64 dans l'audit | [note](program_m_high_rank_dimension.md) |
| MF-DIM-003 | Un rang fini peut-il conclure ? | non, couronnes minimales non bornées | [note](program_m_no_finite_dimension_cutoff.md) |
| MF-KER-001 | La base faible force-t-elle deux ordres ? | non | [note](program_m_weak_kernel_axioms.md) |
| MF-KER-002 | Les axiomes naturels supplémentaires suffisent-ils ? | non | [note](program_m_candidate_kernel_axioms.md) |
| MF-AX-001 | Où passe la frontière des hypothèses ? | 4 trop faibles, 3 circulaires | [note](program_m_axiom_boundary.md) |
| MF-SEP-001 | Les petits séparateurs récursifs suffisent-ils ? | non, les couronnes les satisfont | [note](program_m_recursive_separator_locality.md) |
| MF-SEP-002 | Les petits séparateurs sont-ils nécessaires à la cible ? | non, ils rejettent Minkowski avant le contrôle 3D | [note](program_m_separator_target_compatibility.md) |
| MF-SEL-002 | Les axiomes seuls peuvent-ils sélectionner 1+1 ? | non, les modèles 2D et 3D ont le même profil | [note](program_m_selection_from_axioms_nogo.md) |
| MF-PBRIDGE-001 | Quelles entrées M doit-il fournir à P ? | configurations, transformations et fonctionnelles avant toute géométrie | [note](program_m_program_p_bridge.md) |
| MF-CONF-001 | Peut-on construire configurations et transformations ? | oui, groupoïde relationnel prouvé en Lean | [note](program_m_configuration_groupoid.md) |
| MF-OBS-001 | Peut-on définir les fonctionnelles admissibles ? | oui, invariance exacte sous le groupoïde | [note](program_m_configuration_observables.md) |
| MF-COMP-002 | Peut-on composer les configurations ? | oui sans interaction ; les relations croisées exigent une interface | [note](program_m_configuration_composition.md) |
| MF-GLUE-001 | Peut-on recoller le long d'une interface ? | oui, librement et canoniquement après fourniture d'une interface compatible | [note](program_m_interface_gluing.md) |
| MF-GLUE-002 | Les collages successifs sont-ils cohérents ? | oui pour le collage libre audité ; non pour l'unicité globale arbitraire | [note](program_m_gluing_coherence.md) |
| MF-DESC-001 | Que doit-on faire descendre ? | les relations primitives ; la reachabilité est reconstruite après collage | [note](program_m_primitive_descent.md) |
| MF-DESC-002 | La fermeture après collage reconstruit-elle les chaînes locales ? | oui, théorème général et 4 096 audits | [note](program_m_descent_reachability.md) |
| MF-FREE-001 | Quelle structure globale minimale apparaît ? | le préordre libre engendré par les relations primitives | [note](program_m_free_preorder.md) |
| MF-GEO-001 | La base de M sélectionne-t-elle déjà une géométrie ? | non, un même préordre donne deux classes métriques | [note](program_m_geometry_bifurcation.md) |
| MF-GEO-002 | L'unicité locale et le collage sélectionnent-ils le global ? | non, deux classes globales survivent | [note](program_m_geometric_gluing_selection.md) |
| MF-REF-001 | Quel raffinement suffit à l'unicité des données de paires ? | couvrir toute paire, exactement | [note](program_m_pairwise_refinement.md) |
| MF-DIST-001 | Peut-on construire des valeurs locales sans géométrie cible ? | oui, distance orientée libre ; pas de sélection lorentzienne | [note](program_m_free_directed_distance.md) |
| MF-WEIGHT-001 | Les relations sélectionnent-elles les poids primitifs ? | non, même les rapports restent libres | [note](program_m_weight_selection_nogo.md) |
| MF-MEAS-001 | Une mesure additive minimale est-elle sélectionnée ? | non relationnellement ; comptage si uniformité ajoutée | [note](program_m_measure_extension.md) |
| MF-SIGN-001 | Une involution suffit-elle à faire apparaître des signes opposés ? | oui avec loi impaire ajoutée ; magnitude libre | [note](program_m_signed_involution.md) |
| MF-INV-001 | Une involution non triviale est-elle sélectionnée par la relation ? | non en général ; existence sans canonicité | [note](program_m_canonical_involution.md) |
| MF-INV-002 | L'involution intrinsèque unique survit-elle à la composition ? | non ; l'involution équipée compose correctement | [note](program_m_involution_composition.md) |
| MF-INV-003 | Quand l'involution survit-elle au collage ? | exactement pour une interface équivariante | [note](program_m_equivariant_gluing.md) |
| MF-PBRIDGE-002 | Que fournit concrètement l'extension signée à P ? | secteurs et source signée conditionnels, sans géométrie ni action | [note](program_m_signed_program_p_adapter.md) |

## Règle d'archivage désormais obligatoire

Une nouvelle étape n'est considérée terminée que si elle possède :

1. un identifiant unique dans le registre de provenance ;
2. une note lisible indiquant question, résultat et limites ;
3. un script reproductible et sa sortie JSON ;
4. un test automatisé ;
5. une mise à jour de ce checkpoint si la conclusion globale change.

MF-ARC-001 vérifie automatiquement l'unicité des identifiants et la présence
des quatre artefacts pour la séquence récente. Aucune nouvelle hypothèse de
recherche n'est ajoutée par cet archivage.
