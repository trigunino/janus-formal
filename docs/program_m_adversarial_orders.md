# MF-ADV-001 — Recherche d'ordres adverses

## Question

Un ordre sans origine géométrique peut-il imiter les fluctuations de liens de
MF-MAN-015 ? Et peut-il ensuite passer simultanément les diagnostics aveugles
de dimension et de localité ?

## Protocole frais

La recherche utilise 400 candidats à 256 objets :

- 240 DAG orientés vers l'avant, avec 12 probabilités d'arête ;
- 160 ordres aléatoires à trois couches, avec 8 probabilités ;
- 20 graines fraîches par paramètre ;
- fermeture réflexive-transitive avant toute évaluation.

Aucune coordonnée ou géométrie cible n'intervient dans leur génération. Les
seuils MF-MAN-015, MF-DIM-001 et MF-LOC-003 sont chargés depuis leurs références
figées, dont les empreintes SHA-256 sont enregistrées.

## Résultats

| Étape | Candidats acceptés / 400 |
| --- | ---: |
| fluctuations intrinsèques des liens | 115 |
| dimension seule | 40 |
| localité seule | 0 |
| dimension + localité | 0 |
| trois diagnostics ensemble | 0 |

Le premier DAG adverse obtient un score de liens `1,0039`, parfaitement dans
l'intervalle Poisson `[0,9155 ; 1,1975]`. Il estime cependant une dimension
`9,83` et son profil de localité est très éloigné du seuil.

## Conclusion honnête

MF-MAN-015 **seul est insuffisant** : il est facilement trompé. L'intersection
des trois diagnostics rejette tous les candidats de cette recherche fraîche.
Cela montre l'intérêt de ne jamais promouvoir un candidat avec un seul résumé.

Ce n'est pas une preuve de suffisance. Les familles explorées sont limitées et
il n'est pas démontré que chaque réalisation est non-manifoldlike. Une future
recherche devra optimiser directement un adversaire contre les trois scores,
au lieu d'échantillonner seulement des paramètres fixes.

## Reproduction

```text
python scripts/audit_program_m_adversarial_orders.py \
  --output outputs/program_m/mf_adv_001_adversarial_orders.json
```
