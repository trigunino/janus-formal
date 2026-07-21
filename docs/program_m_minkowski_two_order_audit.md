# MF-MAN-005 — Audit d'ordre pour Minkowski 1+1

## Question testée

Un ordre partiel fini peut-il être plongé exactement dans l'ordre produit des
deux coordonnées nulles de MF-MAN-004 ?

Pour un ordre fini, cela revient à trouver deux extensions linéaires dont
l'intersection redonne exactement l'ordre initial. Le script énumère toutes
les extensions et toutes leurs paires ; les coordonnées retournées sont leurs
rangs. Cette caractérisation est la dimension d'ordre classique. Voir par
exemple [Biró et al.](https://arxiv.org/abs/1402.5113).

## Témoins reproductibles

- **Positif :** la chaîne à trois éléments s'encode par
  `(0,0), (1,1), (2,2)`. Sur tous ses diamants définis par deux éléments,
  densité `2` et tolérance de comptage `1` vérifient la loi nombre-volume ;
  les pas de chaîne reproduisent exactement le temps propre avec facteur `1`.
- **Négatif :** l'exemple standard `S₃`, composé de six éléments avec
  `aᵢ < bⱼ` exactement lorsque `i ≠ j`, n'admet aucune paire d'extensions
  réalisant son ordre. Il ne peut donc pas se plonger dans cette cible 1+1.

Le résultat est enregistré dans
`outputs/program_m/mf_enum_001.json`, sous `minkowski_two_order_audit`.

## Portée exacte

Le témoin positif contrôle l'ordre et les six diamants définis par ses points.
Il ne fournit ni modèle probabiliste, ni limite de haute densité, ni contrôle
d'autres régions. Le témoin négatif rejette cette cible 1+1 précise, mais pas
une cible de dimension supérieure ni une autre géométrie.

La « dimension d'ordre » est ici un invariant combinatoire et non une preuve
que la dimension physique de l'espace-temps a émergé. Aucun choix Janus ou
gorge n'intervient.
