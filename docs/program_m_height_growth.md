# MF-MAN-018 — Croissance intrinsèque de la hauteur

## Diagnostic

La hauteur est la taille de la plus longue chaîne stricte du seul ordre fourni.
Elle est inchangée par réétiquetage et par inversion globale des flèches. Elle
n'utilise ni coordonnées, ni métrique, ni dimension supposée.

Pour des points iid dans le carré avec l'ordre produit — le modèle externe
Minkowski 1+1 en coordonnées nulles — la plus longue chaîne croît comme
`√n`. Ce problème est le classique des plus longues sous-suites croissantes;
voir [Deuschel–Zeitouni](https://arxiv.org/abs/math/9803035) et le cadre plus
général des [chaînes monotones aléatoires](https://arxiv.org/abs/2009.13887).

Le seuil a été fixé avant les nouvelles simulations : entre les tailles 288 et
2304, le rapport doit dépasser `2`. La limite attendue pour Minkowski 1+1 est
`√8 ≈ 2.83`, contre `1` pour toute famille de hauteur bornée.

## Résultat

Sur 64 trajectoires indépendantes par modèle :

| Modèle | Hauteurs moyennes | Rapport moyen | Gate combiné |
| --- | --- | ---: | ---: |
| Minkowski 1+1 | 30.1, 42.8, 63.0, 90.3 | 3.02 | 64/64 |
| six niveaux ergodique | 6, 6, 6, 6 | 1 | 0/64 |
| ordre total | 288, 576, 1152, 2304 | 8 | 0/64 |
| antichaîne | 1, 1, 1, 1 | 1 | 0/64 |

L'ordre total passe le test de croissance seul, mais échoue aux moments gelés
de MF-ENS-002. L'intersection est nécessaire : la hauteur croissante ne suffit
pas à caractériser Minkowski.

Lean utilise la notion existante `Set.chainHeight` de Mathlib, prouve son
invariance par inversion et formalise qu'une famille uniformément bornée ne peut
pas avoir une hauteur non bornée dans
`JanusFormal/Foundations/ProgramMHeightGrowth.lean`.

## Limite

L'audit donne une séparation finie, pas encore une preuve probabiliste du
comportement asymptotique de la cible. Une croissance non bornée n'est ni une
dimension, ni une variété, ni une distance, ni une géométrie unique.

Le script est `scripts/audit_program_m_height_growth.py`; la sortie est
`outputs/program_m/mf_man_018_height_growth.json`.

