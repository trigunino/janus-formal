# MF-GLUE-002 — Cohérence locale-vers-global

## Question

Une configuration globale construite depuis plusieurs morceaux dépend-elle de
l'ordre dans lequel les interfaces sont traitées ?

MF-GLUE-002 représente tout le problème par un diagramme fini : morceaux,
classes d'objets à identifier et relations locales. Le collage libre est obtenu
en deux opérations :

1. quotienter tous les objets par les identifications d'interface ;
2. réunir toutes les relations locales sur ce quotient.

## Audit

Trois morceaux à deux points sont recollés cycliquement par trois interfaces.
Les six ordres possibles de traitement donnent exactement la même relation
globale. Un renommage complet des morceaux et de leurs objets donne une relation
isomorphe. Une contradiction entre deux relations d'interface est rejetée.

Le résultat libre contient trois points et trois relations : aucune relation
supplémentaire n'apparaît pendant le collage.

## Limite fondamentale

Le diagramme local détermine le **collage libre minimal**, mais pas tout global
possible. Dans un diagramme en chaîne, les deux points extrêmes ne figurent
ensemble dans aucun morceau. Ajouter une relation directe entre eux ne change
aucune donnée locale, mais produit une autre configuration globale.

Ainsi :

- cohérence des collages libres : vérifiée dans l'audit ;
- unicité d'un global arbitraire depuis les seules données locales : réfutée.

Une propriété de descente plus forte devrait déclarer quelles relations
globales sont autorisées, par exemple en imposant que toute relation possède un
témoin local. Cette condition serait une hypothèse nouvelle, pas une conséquence
du collage.

## Statut

MF-GLUE-002 est une vérification exhaustive du diagramme fini déclaré. Le
pushout des supports est standard et formalisé dans Mathlib, mais la cohérence
générale de tous les colimites relationnels n'est pas encore prouvée dans Lean.

Le script est `scripts/audit_program_m_gluing_coherence.py`; la sortie est
`outputs/program_m/mf_glue_002_gluing_coherence.json`.
