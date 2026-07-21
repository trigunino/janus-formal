# MF-MAN-008 — Ambiguïté des plongements de rang en 1+1

## Question

MF-MAN-005 trouve une paire d'extensions linéaires et utilise leurs rangs
comme coordonnées nulles `(u,v)`. Mais l'ordre choisit-il cette réalisation de
façon unique ?

Cette question est une version finie et très restreinte du problème de
quasi-unicité des approximations continues. La revue de Surya présente cette
question sous le nom de Hauptvermutung des ensembles causaux : deux
approximations fidèles devraient être approximativement isométriques
([Surya, 2019](https://link.springer.com/article/10.1007/s41114-019-0023-1)).

## Audit exact

Pour chaque ordre partiel non isomorphe de taille au plus quatre, le script :

1. énumère toutes ses extensions linéaires ;
2. conserve toutes les paires dont l'intersection redonne exactement l'ordre ;
3. interprète leurs rangs comme coordonnées nulles externes ;
4. compare les matrices induites par `ds²=-du dv` ;
5. quotient cette comparaison par tous les automorphismes de l'ordre.

Mathlib contient déjà le théorème d'extension linéaire de Szpilrajn et le type
`OrderEmbedding` ; aucun équivalent de cet audit métrique fini n'a été trouvé.

## Résultat négatif

Les nombres de classes d'ordres partiels pour `N=1,2,3,4` sont respectivement
`1,2,5,16`. Toutes sont plongeables par deux ordres linéaires dans cette petite
plage. La première ambiguïté apparaît à quatre objets.

Le témoin est l'ordre composé de `0<1` et de deux objets isolés. Ses six
réalisations de rang exactes donnent deux signatures métriques non équivalentes :

```text
(-1, 2, 2, 2, 2, 9)
(-1, 2, 6, 2, 6, 1)
```

Les automorphismes de l'ordre, les translations et l'échange des deux
coordonnées nulles ne suppriment pas cette différence. Ainsi, choisir la
première paire d'extensions linéaires introduirait une géométrie non déterminée
par l'ordre.

## Portée exacte

Le résultat réfute l'unicité de la géométrie **de rang** utilisée par
MF-MAN-005. L'espacement uniforme des rangs et la métrique 1+1 restent des
conventions externes. Le témoin est fini et ne démontre ni ambiguïté
macroscopique, ni échec de toute méthode de reconstruction, ni violation de la
Hauptvermutung.

Les méthodes de reconstruction plus riches utilisent notamment les volumes
d'intervalles avant de factoriser une matrice de produits internes
([Johnston, 2022](https://arxiv.org/abs/2111.09331)). Elles constituent une
branche ultérieure possible, mais devront elles aussi fournir un audit de
stabilité et d'unicité.

## Reproduction

```text
python scripts/audit_program_m_embedding_ambiguity.py \
  --output outputs/program_m/mf_man_008_embedding_ambiguity.json
```
