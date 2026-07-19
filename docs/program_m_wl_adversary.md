# MF-ADV-004 — Attaque asymétrique contre WL

## Construction

Un objet est remplacé par un éventail contenant une chaîne de chaque longueur
`1,2,...,m`. La règle génératrice est très courte, mais toutes les branches ont
des longueurs différentes. WL peut donc les distinguer individuellement et ne
forme aucune grande classe stable.

## Validation fraîche

| Longueur maximale | Objets de l'éventail | Collisions cinq gates / 40 |
| ---: | ---: | ---: |
| 2 | 3 | 37 |
| 3 | 6 | 36 |
| 4 | 10 | 28 |
| 5 | 15 | 17 |
| 6 | 21 | 7 |
| 7 | 28 | 1 |

Au total, 126 candidats passent DIM, LOC, fluctuations de liens, jumeaux exacts
et WL. Un éventail artificiel de 28 objets survit sur une graine fraîche.

## Leçon

WL détecte la symétrie, pas toute forme de compressibilité algorithmique.
Poursuivre avec un test ad hoc pour chaque générateur serait encore une course
sans fin. La complexité de Kolmogorov idéale n'est pas calculable, et tout
compresseur pratique impose son propre langage de description.

La voie rigoureuse consiste donc à :

1. conserver plusieurs diagnostics nécessaires sans les appeler suffisants ;
2. déclarer explicitement une classe de modèles générateurs lorsqu'on compare
   leurs longueurs de description ;
3. valider les comparaisons sur données indépendantes ;
4. rechercher continuellement des générateurs hors de cette classe.

Le gate reste cassé comme certificat universel. Aucune géométrie n'est promue.

## Reproduction

```text
python scripts/audit_program_m_wl_adversary.py \
  --output outputs/program_m/mf_adv_004_wl_adversary.json
```
