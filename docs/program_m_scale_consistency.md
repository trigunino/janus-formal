# MF-MAN-012 — Cohérence sans dimension des échelles

## Motivation

MF-MAN-011 interdit de combiner arbitrairement les erreurs de volume et de
temps. En Minkowski 1+1, leurs calibrations ne sont cependant pas indépendantes.
Avec `V=τ²/2` et l'asymptotique bidimensionnelle
`E[L]≈2√(ρV)`, le facteur `a` défini par `τ≈aL` doit vérifier :

```text
2 ρ a² = 1.
```

Cette combinaison est sans dimension. La relation entre plus longue chaîne,
densité et temps propre est asymptotique et dimensionnelle dans la littérature
des ensembles causaux
([Surya, 2019](https://link.springer.com/article/10.1007/s41114-019-0023-1)).

## Audit exact

Pour chaque géométrie de rang ambiguë jusqu'à cinq objets, MF-MAN-012 reprend
séparément :

- la densité calibrée par MF-MAN-009 ;
- le facteur chaîne-temps au carré calibré par MF-MAN-010 ;
- la valeur exacte rationnelle de `2ρa²`.

| Taille | Ambiguïtés | Même valeur dans chaque classe | Valeur exactement 1 | Choix unique |
| ---: | ---: | ---: | ---: | ---: |
| 4 | 1 | 1 | 0 | 0 |
| 5 | 10 | 10 | 0 | 0 |

Le diagnostic supprime le problème d'unités, mais ne départage aucune
réalisation. Pour le premier conflit MF-MAN-010, Lean prouve que les deux
candidats donnent exactement `2ρa²=3`. Pour le premier témoin à quatre objets,
les deux donnent `8`.

## Interprétation correcte

Ces valeurs ne rejettent pas statistiquement Minkowski 1+1. L'identité utilisée
est asymptotique, tandis que les systèmes ont seulement quatre ou cinq objets.
Une tolérance finie ne peut pas être inventée après observation. La prochaine
étape doit donc calibrer la distribution de ce diagnostic sur des sprinklings
Poisson indépendants et à plusieurs densités.

Le résultat actuel est un no-go de sélection : même la normalisation théorique
sans dimension ne résout pas l'ambiguïté microscopique.

## Vérification

```text
python scripts/audit_program_m_scale_consistency.py \
  --output outputs/program_m/mf_man_012_scale_consistency.json

lake build JanusFormal.Foundations.ProgramMScaleConsistencyNoGo
```
