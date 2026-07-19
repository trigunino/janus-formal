# MF-FREE-001 — Préordre libre engendré par les relations primitives

## Résultat

La fermeture réflexive-transitive d'une relation primitive est exactement le
plus petit préordre qui contient cette relation. Elle ajoute donc uniquement ce
qui est imposé par :

- la réflexivité (`x` atteint `x`) ;
- la composition des chaînes (`x→y` et `y→z` donnent `x→z`).

Lean prouve aussi la propriété universelle : une application vers un préordre
préserve toute la reachabilité si et seulement si elle préserve chaque pas
primitif. Sous MF-DESC-002, ce même préordre libre est engendré par les pas qui
possèdent un témoin local.

## Audit exhaustif

L'audit énumère les 512 relations binaires sur trois points et les 29 préordres
sur ces points. Dans chaque cas, la fermeture est un préordre contenant la
relation initiale et elle est incluse dans tout autre préordre qui la contient.
Aucun contre-exemple n'est trouvé.

## Portée et limites

MF-FREE-001 caractérise précisément une première structure qui apparaît sans
géométrie supposée. Il ne produit ni antisymétrie, ni topologie, ni métrique, ni
dimension, ni gorge. Les cycles restent présents sous forme d'atteignabilité
mutuelle ; obtenir un ordre partiel demande encore de quotienter ces cycles.

Le module formel est
`JanusFormal/Foundations/ProgramMFreePreorder.lean`. Le script est
`scripts/audit_program_m_free_preorder.py`; la sortie est
`outputs/program_m/mf_free_001_free_preorder.json`.
