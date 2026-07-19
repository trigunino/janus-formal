# MF-COMP-002 — Composition des configurations

## Construction canonique

Deux systèmes utilisant les mêmes noms de relations peuvent être composés par
somme disjointe :

- les objets du résultat viennent de gauche ou de droite ;
- les relations internes de chaque morceau sont conservées ;
- aucune relation traversante n'est ajoutée.

Lean prouve que cette composition est :

- associative à isomorphisme près ;
- commutative à isomorphisme près ;
- munie de la configuration vide comme unité à gauche et à droite.

Elle respecte donc naturellement le groupoïde de MF-CONF-001.

## Pourquoi l'interaction n'est pas canonique

Pour deux configurations réduites chacune à un point, deux relations dirigées
traversantes sont possibles : gauche vers droite et droite vers gauche. Chacune
peut être absente ou présente. Les mêmes morceaux internes donnent donc déjà
quatre composites distincts.

Lean sépare explicitement :

- la somme disjointe canonique ;
- `CrossRelationData`, donnée supplémentaire de relations traversantes ;
- la somme munie de cette donnée.

L'audit fini vérifie les quatre composites. Ainsi, un collage interactif ne peut
pas être déduit des seuls morceaux.

## Portée

MF-COMP-002 apporte une notion de composition purement mathématique. Il
n'introduit ni interaction physique, ni dynamique, ni géométrie.

La prochaine question fondamentale est celle des interfaces : peut-on définir
un sous-système commun et recoller deux configurations le long de celui-ci ?
Mathématiquement, cela mène aux diagrammes de type span/pushout. La donnée de
l'interface restera explicite ; elle ne devra pas être inventée par le collage.

Le module formel est
`JanusFormal/Foundations/ProgramMConfigurationComposition.lean`. Le script est
`scripts/audit_program_m_configuration_composition.py`; la sortie est
`outputs/program_m/mf_comp_002_configuration_composition.json`.
