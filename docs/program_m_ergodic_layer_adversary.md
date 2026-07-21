# MF-ADV-006 — Adversaire ergodique à six niveaux

## Construction

Chaque objet reçoit indépendamment l'un de six niveaux. Un objet précède un
autre exactement quand son niveau est strictement plus petit. Cette loi est :

- échangeable, car les étiquettes des objets ne jouent aucun rôle;
- projective, car retirer des objets ne modifie aucune relation restante;
- dissociée et ergodique, car elle vient d'une unique suite de niveaux iid;
- non minkowskienne, car toute chaîne stricte contient au plus six objets.

Les six poids sont choisis pour satisfaire

```text
Σ qᵢ² = 1/2
Σ qᵢ³ = 1/3.
```

Un ordre complet par niveaux a alors une fraction limite de paires comparables
`1-Σqᵢ²=1/2` et une fraction limite de triples en chaîne
`1-3Σqᵢ²+2Σqᵢ³=1/6`. Il reproduit donc, dans chaque grande réalisation, les deux
statistiques de Minkowski utilisées par MF-ENS-002.

La construction relève des noyaux de posets échangeables étudiés par
[Janson](https://arxiv.org/abs/0902.0306) et par
[Hladký–Máthé–Patel–Pikhurko](https://arxiv.org/abs/1211.2473); cette famille
n'est pas inventée comme une géométrie cachée.

## Résultat

Le gate MF-ENS-002 a été laissé inchangé. Sur quatre nouvelles tailles :

| Taille | Acceptés |
| ---: | ---: |
| 224 | 63/64 |
| 448 | 64/64 |
| 896 | 64/64 |
| 1792 | 64/64 |

Le gate est donc cassé par `255/256` réalisations d'une loi ergodique
manifestement non minkowskienne.

Lean formalise les équations exactes sous leurs hypothèses déclarées, construit
l'ordre partiel à six niveaux et prouve l'impossibilité d'une chaîne stricte de
sept objets dans
`JanusFormal/Foundations/ProgramMErgodicLayerAdversary.lean`. Les valeurs
numériques positives utilisées par l'audit satisfont les équations avec un
résidu inférieur à `4×10⁻¹⁶`; une preuve Lean de leur existence algébrique exacte
n'est pas revendiquée.

## Successeur

La prochaine statistique est maintenant préenregistrée sans regarder de
nouvelles données : croissance de la hauteur avec la cardinalité. Elle doit
rejeter toute hauteur uniformément bornée sans supposer une dimension ou une
métrique.

Le script est `scripts/audit_program_m_ergodic_layer_adversary.py`; la sortie
est `outputs/program_m/mf_adv_006_ergodic_layer_adversary.json`.

