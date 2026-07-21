# MF-DESC-002 — Théorème local-vers-global de reachabilité

## Théorème

Sous la descente primitive de MF-DESC-001 :

```text
reachabilité dans le global
↔ chaîne réflexive-transitive de pas primitifs possédant chacun un témoin local.
```

La chaîne peut changer de morceau à chaque étape. Aucun morceau unique n'a
besoin de contenir ses deux extrémités ou la chaîne entière.

Lean prouve les deux implications pour tout atlas relationnel :

- toute portée globale se décompose en pas primitifs localement témoins ;
- toute composition finie de tels pas donne une portée globale.

## Ordre correct des opérations

Il faut :

```text
unir/coller les relations primitives locales
→ effectuer une seule fermeture réflexive-transitive globale.
```

Fermer chaque morceau séparément puis réunir les fermetures est insuffisant.
Dans `0→1→2`, les deux fermetures locales ne contiennent pas `0→2`, tandis que
la fermeture globale le contient.

## Audit indépendant

Sur 4 096 diagrammes aléatoires comportant jusqu'à dix points et cinq morceaux,
deux algorithmes indépendants concordent sans aucun désaccord :

- fermeture matricielle de l'union primitive globale ;
- exploration de toutes les chaînes formées avec la liste des pas locaux.

## Signification pour Program M

MF-DESC-002 fournit un mécanisme général, mais modeste, d'apparition d'une
structure globale dérivée : des conséquences globales existent sans avoir été
posées comme relations primitives. Rien de géométrique ou physique n'est encore
interprété dans cette portée.

Le module formel est
`JanusFormal/Foundations/ProgramMDescentReachability.lean`. Le script est
`scripts/audit_program_m_descent_reachability.py`; la sortie est
`outputs/program_m/mf_desc_002_descent_reachability.json`.
