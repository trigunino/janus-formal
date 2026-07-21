# MF-MAN-010 — Sélection chaîne-temps et conflit avec le volume

## Question

Après MF-MAN-009, huit ambiguïtés sur dix restent ouvertes à cinq objets. On
ajoute donc un second observable intrinsèque : le nombre maximal de pas dans
une chaîne entre deux éléments comparables.

La longueur de la plus longue chaîne est le candidat standard pour une distance
temporelle discrète ; son lien asymptotique avec le temps propre dépend toutefois
d'un ensemble causal aléatoire et d'une limite de densité
([Surya, 2019](https://link.springer.com/article/10.1007/s41114-019-0023-1),
[Brightwell et Łuczak, 2015](https://arxiv.org/abs/1510.05612)). MF-MAN-010 ne
suppose pas cette limite acquise.

## Protocole

Pour chaque géométrie de rang :

1. le nombre maximal de pas est calculé uniquement depuis l'ordre ;
2. le facteur chaîne-temps au carré est calibré sur les intervalles ayant le
   plus grand nombre de pas ;
3. le résidu est évalué uniquement sur les chaînes plus courtes ;
4. volume et temps ne sont combinés que par dominance de Pareto.

La dominance de Pareto évite d'inventer un poids relatif entre deux erreurs de
nature et d'unité différentes. Une géométrie doit être au moins aussi bonne sur
les deux diagnostics et strictement meilleure sur l'un d'eux.

## Résultat exhaustif

À cinq objets :

- 10 classes d'ordres ont plusieurs géométries de rang ;
- chaîne-temps choisit seule une géométrie dans 2 cas ;
- nombre-volume choisit aussi dans ces 2 cas, mais choisit l'autre géométrie ;
- aucune géométrie n'est conjointement dominante ;
- les 10 ambiguïtés restent donc ouvertes sans poids externe.

Le premier conflit est stocké intégralement avec les coordonnées, signatures,
calibrations et résidus rationnels. Ce résultat négatif interdit de déclarer
une géométrie gagnante en réglant après coup une combinaison des pertes.

## Limites

La cible `ds²=-du dv`, les rangs uniformes, la perte quadratique et la relation
`τ²=ΔuΔv` sont externes. Le calcul est exhaustif seulement jusqu'à cinq objets.
Il n'établit ni convergence statistique, ni temps physique, ni géométrie
émergente, ni gorge.

## Reproduction

```text
python scripts/audit_program_m_chain_time_selection.py \
  --output outputs/program_m/mf_man_010_chain_time_selection.json
```
