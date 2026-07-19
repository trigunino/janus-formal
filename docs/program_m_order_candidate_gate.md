# MF-GATE-001 — Rapport unifié pour un ordre candidat

## Entrée

L'outil reçoit seulement une matrice booléenne carrée, en JSON ou `.npy`.
`order[i,j]` signifie l'orientation mathématique fournie `i≤j`. Cette
orientation n'est pas automatiquement appelée temps ou causalité physique.

Avant tout diagnostic, l'outil vérifie :

- réflexivité ;
- antisymétrie ;
- transitivité.

Une relation invalide est rejetée sans calcul dimensionnel ou géométrique.

## Diagnostics assemblés

Pour un ordre valide :

1. MF-DIM-001 calcule la fraction d'ordre et l'estimation Myrheim–Meyer ;
2. MF-LOC-003 calcule le profil d'intervalles et le compare au seuil conforme
   figé pour la cardinalité exacte ;
3. les lois nombre-volume et chaîne-temps restent explicitement `not_tested`
   puisqu'aucun plongement cible n'a été fourni.

Chaque rapport contient l'empreinte SHA-256 de l'entrée brute, les identifiants
des protocoles de référence et les empreintes de leurs contenus JSON.

## Statuts possibles

- `rejected_invalid_partial_order` : l'entrée n'est pas un ordre partiel ;
- `indeterminate_unsupported_cardinality` : aucun seuil conforme n'existe pour
  cette taille ;
- `incompatible_with_external_minkowski2_diagnostics` : au moins un diagnostic
  aveugle échoue ;
- `compatible_with_external_minkowski2_diagnostics` : dimension et abondance
  sont compatibles avec la référence externe.

Le dernier statut ne signifie jamais « géométrie Minkowski reconstruite ».

## Exemples frais à 256 éléments

| Candidat | d estimé | score / seuil | statut |
| --- | ---: | ---: | --- |
| Poisson frais | 1,9547 | 0,0358 / 0,0826 | compatible avec les diagnostics |
| grille 16×16 | 1,8504 | 0,3356 / 0,0826 | incompatible |
| trois-couches | 2,3722 | 1,2033 / 0,0826 | incompatible |

Les coordonnées des générateurs sont supprimées avant l'évaluation. La grille
montre encore pourquoi la dimension seule ne suffit pas.

## Utilisation

```text
python scripts/evaluate_program_m_order_candidate.py \
  --order candidate.npy --output report.json

python scripts/evaluate_program_m_order_candidate.py \
  --examples --output outputs/program_m/mf_gate_001_examples.json
```

## Limites et passage vers Program P

Les références n'existent actuellement que pour `N=128,256,512,1024` et pour
Minkowski 1+1. Le gate ne teste ni volume, temps propre, coordonnées, métrique,
topologie de continuum ou unicité. Il ne contient ni Janus ni gorge.

Program P ne doit recevoir un candidat qu'après ajout d'un plongement cible et
fermeture des lois nombre-volume/chaîne-temps ; le statut actuel sert à filtrer,
pas à promouvoir une géométrie.

