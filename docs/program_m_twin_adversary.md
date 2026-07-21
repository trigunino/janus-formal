# MF-ADV-002 — Attaque par classes de jumeaux relationnels

## Construction adverse

Un ordre de référence à 256 objets est généré comme un ordre de Poisson
conditionné. Un objet est ensuite remplacé par une antichaîne de `k` objets qui
ont exactement le même passé strict et le même futur strict.

Ces objets sont des **jumeaux relationnels** : aucune statistique qui ne regarde
que des résumés globaux grossiers ne les distingue facilement. La construction
conserve la réflexivité, l'antisymétrie et la transitivité.

## Protocole frais

- multiplicités `k = 2, 4, 6, 8, 10, 12` ;
- 40 nouvelles graines par multiplicité ;
- 240 candidats au total ;
- références DIM, LOC et MAN-015 figées et hachées ;
- aucune graine du pilote réutilisée.

## Résultat

| Jumeaux imposés | Collisions avec les trois gates / 40 |
| ---: | ---: |
| 2 | 32 |
| 4 | 29 |
| 6 | 23 |
| 8 | 12 |
| 10 | 4 |
| 12 | 1 |

Au total, **101 candidats sur 240** passent simultanément dimension, localité et
fluctuations de liens. Le plus grand témoin validé contient une classe de douze
jumeaux exacts.

## Conclusion

Le gate combiné actuel est cassé. Ses trois diagnostics sont nécessaires et
utiles, mais ils ne certifient pas la généricité de type Poisson et ne détectent
pas toujours une dégénérescence relationnelle volontaire.

Il n'est pas affirmé qu'une paire de jumeaux soit impossible dans tout ordre
issu d'un continuum, ni que chaque témoin ne possède aucun plongement. Le point
prouvé par exécution est plus précis : une multiplicité artificielle importante
peut traverser les trois critères actuels.

La prochaine correction doit mesurer la distribution des classes de jumeaux
sur des références Poisson fraîches, puis calibrer un seuil avant de retester
ces adversaires.

## Reproduction

```text
python scripts/audit_program_m_twin_adversary.py \
  --output outputs/program_m/mf_adv_002_twin_adversary.json
```
