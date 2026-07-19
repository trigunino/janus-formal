# MF-ADV-003 — Attaque par sous-ordres répétés

## Construction

Un objet d'un ordre Poisson conditionné est remplacé par `k` branches privées
de deux éléments. Chaque branche est une chaîne courte et toutes sont
structurellement identiques, mais leurs sommets n'ont pas exactement les mêmes
ensembles passé/futur : MF-MAN-016 ne les classe donc pas comme grands groupes
de jumeaux.

## Validation fraîche

| Branches répétées | Collisions avec les quatre gates / 40 |
| ---: | ---: |
| 2 | 35 |
| 3 | 32 |
| 4 | 27 |
| 6 | 13 |
| 8 | 4 |
| 10 | 0 |

Au total, 111 candidats passent dimension, localité, fluctuations de liens et
le nouveau gate des jumeaux exacts. Une famille de huit branches répétées
survit sur des graines fraîches.

## Conclusion

Le correctif MF-MAN-016 ferme l'attaque exacte MF-ADV-002, mais pas sa
généralisation structurelle. Ajouter successivement un test pour chaque motif
copié conduirait à une course sans fin.

La prochaine étape doit mesurer une notion plus générale de **complexité ou de
compressibilité relationnelle**, capable de détecter des automorphismes et des
sous-structures répétées sans interdire les symétries naturelles calibrées sur
Poisson.

Il n'est toujours pas affirmé que chaque témoin soit absolument non plongeable
dans un continuum. Le résultat démontré est que les quatre résumés actuels ne
détectent pas la répétition artificielle connue.

## Reproduction

```text
python scripts/audit_program_m_branch_adversary.py \
  --output outputs/program_m/mf_adv_003_branch_adversary.json
```
