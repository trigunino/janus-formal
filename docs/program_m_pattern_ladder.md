# MF-PAT-002 — Échelle de motifs préenregistrée

## Question

À quel rang la distribution complète des petits sous-posets distingue-t-elle la
cible Minkowski 1+1 de MF-ADV-008 ? Le protocole fixe avant validation les rangs
2, 3, 4 et 5, 512 tirages par lot et 32 lots nouveaux par modèle. Les seuils
sont calibrés uniquement sur 99 autres lots Minkowski. Le maximum de calibration
à chaque rang donne une erreur familiale conservatrice inférieure à 5 %.

## Résultat

| Rang | Motifs dans la cible | Cible acceptée | MF-ADV-008 accepté |
| ---: | ---: | ---: | ---: |
| 2 | 2 | 32/32 | 32/32 |
| 3 | 5 | 31/32 | 0/32 |
| 4 | 16 | 31/32 | 0/32 |
| 5 | 63 | 32/32 | 0/32 |

Le premier rang séparateur est donc 3. MF-ADV-008 reproduisait exactement la
densité de paires comparables et la fréquence moyenne des chaînes triples, mais
pas la distribution complète des cinq posets possibles à trois objets. Les
anciens scalaires avaient bien supprimé une information déjà observable au même
rang.

## Limite et prochain adversaire

Ce résultat ne fournit toujours pas l'unicité à rang fini. MF-ADV-009 fournit
désormais une loi réellement échangeable et projective qui reproduit toute la
distribution jusqu'au rang 3 et n'échoue qu'au rang 4; voir
`docs/program_m_three_symmetric_permuton.md`.

Le script est `scripts/audit_program_m_pattern_ladder.py`; la sortie figée est
`outputs/program_m/mf_pat_002_pattern_ladder.json`.
