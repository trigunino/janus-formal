# MF-MAN-019 — Décroissance des jumeaux relationnels

## Définition

Deux objets sont des jumeaux exacts si leurs passés stricts et leurs futurs
stricts sont identiques. Le diagnostic mesure la taille de la plus grande classe
de jumeaux, divisée par le nombre total d'objets.

Cette notion est purement relationnelle, invariante par réétiquetage et par
inversion globale. Les éléments indistinguables des posets sont déjà étudiés en
combinatoire, par exemple pour les posets `(2+2)`-libres par
[Dukes–Kitaev–Remmel–Steingrímsson](https://arxiv.org/abs/1006.2696).

## Protocole préenregistré

Entre les tailles 384 et 3072, soit un facteur huit, le rapport entre la fraction
jumelle finale et initiale doit être strictement inférieur à `1/2`.

- une multiplicité jumelle bornée donne naturellement un rapport proche de
  `1/8`;
- une classe atomique de masse positive donne un rapport proche de `1`.

Ce critère autorise donc des coïncidences finies; il interdit seulement qu'une
part macroscopique de l'ensemble reste relationnellement indiscernable.

## Résultat

| Modèle | Fractions jumelles moyennes | Rapport moyen | Gate combiné |
| --- | --- | ---: | ---: |
| Minkowski 1+1 | 0.00427, 0.00199, 0.00108, 0.000509 | 0.131 | 64/64 |
| niveaux infinis MF-ADV-007 | 0.690, 0.692, 0.690, 0.693 | 1.006 | 0/64 |
| ordre total | 1/n | 0.125 | 0/64 |
| antichaîne | 1, 1, 1, 1 | 1 | 0/64 |

L'ordre total passe ce diagnostic seul mais reste rejeté par les moments gelés.
Le gate est donc conservé comme condition nécessaire, jamais comme certificat
de continuum.

Lean définit les jumeaux relationnels, prouve l'invariance d'orientation et
montre qu'une borne inférieure strictement positive interdit la disparition de
la fraction jumelle dans
`JanusFormal/Foundations/ProgramMTwinFractionDecay.lean`.

## Limite

Le test ne détecte pas encore les jumeaux approximatifs ni des sous-ordres
différents mais statistiquement équivalents. La séparation observée est finie;
la convergence asymptotique de la cible n'est pas encore formalisée.

Le script est `scripts/audit_program_m_twin_fraction_decay.py`; la sortie est
`outputs/program_m/mf_man_019_twin_fraction_decay.json`.

