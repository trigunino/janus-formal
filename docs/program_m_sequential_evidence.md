# MF-STAT-001 — Bornes séquentielles sans tricher sur l'arrêt

## Objectif

Une fréquence observée nulle ne prouve jamais une probabilité nulle. MF-STAT-001
remplace les simples taux d'acceptation par des intervalles simultanés valides
aux checkpoints `256`, `1024`, `4096` et `16384`.

Le risque total `5 %` est partagé entre :

- les violations de dimension 2 au rang 6 (`2,5 %`) ;
- la loi multinomiale complète des 16 motifs au rang 4 (`2,5 %`).

Pour chaque modèle et l'étape `s`, chaque famille dépense
`α/[4s(s+1)]`. La somme sur les quatre modèles et toutes les étapes possibles
est au plus `α`; décider de continuer après avoir vu une borne insuffisante ne
détruit donc pas la validité globale.

Les violations utilisent l'intervalle binomial exact de Clopper–Pearson. La
distance de variation totale utilise la borne multinomiale de Weissman :

```text
P(||p̂-p||₁ ≥ ε) ≤ (2^K-2) exp(-N ε²/2)
```

## Résultats finaux

| Modèle | Violations dim. 2 / 16384 | Intervalle probabilité | TV rang 4 observée | Intervalle TV vraie |
| --- | ---: | ---: | ---: | ---: |
| Minkowski 1+1 | 0 | [0 ; 0,000535] | 0,0117 | [0 ; 0,0358] |
| MF-ADV-009 | 0 | [0 ; 0,000535] | 0,0489 | [0,0247 ; 0,0731] |
| MF-ADV-008 | 1 | [9,54e-9 ; 0,000688] | 0,534 | [0,510 ; 0,559] |
| Ordre produit 3D | 9 | [0,000115 ; 0,00156] | 0,425 | [0,401 ; 0,449] |

Au checkpoint 4096, la borne supérieure Minkowski au rang 4 valait encore
`0,0703` après correction simultanée des quatre modèles, au-dessus du seuil
préfixé `0,06`. Le protocole a continué sans changer ce seuil et atteint
`0,0358` à 16384.

## Limite

La borne de dimension concerne uniquement les sous-posets de rang 6. Même zéro
violation observée ne démontre pas la prémisse universelle à tous les rangs.
De même, un intervalle étroit autour de zéro n'établit jamais une égalité exacte.
MF-STAT-001 fournit une évidence asymptotique contrôlée, pas une preuve finie.

Le script est `scripts/audit_program_m_sequential_evidence.py`; la sortie est
`outputs/program_m/mf_stat_001_sequential_evidence.json`.
