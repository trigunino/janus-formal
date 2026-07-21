# MF-GLUE-001 — Collage libre le long d'une interface

## Données

Un collage reçoit trois configurations utilisant la même signature de
relations :

- une interface `I` ;
- un morceau gauche `L` contenant une copie induite de `I` ;
- un morceau droit `R` contenant une copie induite de `I`.

Les deux inclusions doivent préserver et refléter exactement les relations de
l'interface. Si les morceaux ne sont pas d'accord sur celle-ci, le collage est
refusé.

## Construction

Le support d'objets est le pushout standard de Mathlib : la somme des objets de
`L` et `R`, où les deux copies de chaque objet de `I` sont identifiées.

La relation du résultat est libre et minimale : elle tient lorsqu'elle possède
un témoin entièrement dans `L` ou entièrement dans `R`. Aucune relation
traversante supplémentaire n'est ajoutée.

Lean prouve que toutes les relations gauche et droite sont transportées dans le
collage. Il prouve aussi qu'une interface bouclée ne peut pas être plongée comme
sous-système induit dans une interface sans boucle.

## Audit fini

Deux morceaux de deux points partagent un point. Le collage contient exactement
trois points et conserve les deux relations internes. Il n'invente pas la
troisième relation entre les deux points extérieurs. Une modification
incompatible de la boucle sur l'interface est rejetée.

Cette précision est importante : la fermeture transitive éventuelle constitue
une opération ultérieure, déjà connue dans MF-TOP-001. Elle ne fait pas partie
du collage des relations primitives.

## Résultat

Le collage est canonique une fois l'interface et ses deux inclusions fournies.
Mais l'interface elle-même reste une donnée explicite. MF-GLUE-001 ne prétend
pas qu'elle puisse être retrouvée uniquement depuis les deux morceaux.

Le module formel est
`JanusFormal/Foundations/ProgramMConfigurationInterfaceGluing.lean`. Le script
est `scripts/audit_program_m_interface_gluing.py`; la sortie est
`outputs/program_m/mf_glue_001_interface_gluing.json`.
