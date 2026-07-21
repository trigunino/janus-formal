# MF-SEL-002 — Sélection impossible depuis le seul profil d'axiomes

## Question

Peut-on sélectionner Minkowski 1+1 parmi les lois relationnelles en utilisant
seulement les axiomes faibles déjà retenus ?

Le profil contient ordre partiel, échangeabilité, projectivité, latents i.i.d.
sans atomes, comparaison déterministe continue presque partout, symétries et
factorisation. Les produits 2D et 3D possèdent exactement le même profil.

## No-go

Un sélecteur qui ne lit que ce profil reçoit la même entrée pour les deux
modèles. Il doit donc produire la même sortie. Deux choix seulement existent :

- accepter les deux ;
- rejeter les deux.

Il ne peut pas accepter 2D et rejeter 3D. C'est une application directe de
MF-OBS-000, déjà prouvé en Lean : une décision passe par une compression si et
seulement si elle est constante sur chaque fibre de cette compression.

## Conséquence pour l'entropie

Le maximum d'entropie sélectionne une distribution parmi celles qui respectent
des contraintes données. Il ne fabrique pas les contraintes manquantes. Avec le
profil actuel, une optimisation qui favoriserait 1+1 devrait nécessairement
utiliser au moins une information supplémentaire : observable, dynamique,
conservation, loi d'échelle ou choix de mesure a priori.

Cette information devra être déclarée et soumise au contrôle anti-smuggling. Le
fait qu'une contrainte soit écrite dans une fonction d'entropie ou dans un prior
ne la rend pas plus fondamentale.

## Frontière suivante

La prochaine étape n'est pas de choisir une formule d'entropie. Il faut dresser
la liste minimale des sources légitimes de contraintes et déterminer lesquelles
sont déjà disponibles dans la base mathématique, dans Program P ou dans les
observations. Sans source indépendante, la sélection reste impossible.

Le script est `scripts/audit_program_m_selection_from_axioms_nogo.py`; la sortie
est `outputs/program_m/mf_sel_002_selection_from_axioms_nogo.json`.

## Référence

E. T. Jaynes, *Information Theory and Statistical Mechanics*, Physical Review
106 (1957), 620–630.
