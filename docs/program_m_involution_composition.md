# MF-INV-002 — Stabilité de l'involution sous composition

## Test exhaustif

On prend toutes les relations étiquetées sur deux objets possédant exactement
une involution centrale non triviale. On compose chaque paire par somme
disjointe, puis on demande si le système global possède encore exactement une
telle involution.

Le résultat est négatif : certaines compositions acquièrent plusieurs
involutions centrales. La propriété « la relation sélectionne intrinsèquement
une involution unique » n'est donc pas fermée sous composition.

En revanche, si chaque morceau est **équipé** de son involution choisie,
l'involution composante par composante est toujours un automorphisme involutif
du composé dans tout l'audit. Elle n'est pas nécessairement centrale après
oubli de l'équipement. C'est la construction standard du coproduct dans la
catégorie des ensembles involutifs
([référence](https://owenbechtel.com/blog/tour-of-inv/)).

## Conséquence

Pour disposer d'une branche signée composable, M doit transporter le couple

```text
(configuration relationnelle, involution choisie)
```

et exiger des morphismes et interfaces équivariants. L'involution peut parfois
être découverte sur un objet isolé, mais elle ne peut pas être oubliée puis
redécouverte de manière unique après chaque composition.

Cela réduit encore l'ambition : les deux secteurs ne sont pas dérivés de la
base universelle ; ils forment une extension algébrique optionnelle et précise.

Le script est `scripts/audit_program_m_involution_composition.py`; la sortie est
`outputs/program_m/mf_inv_002_involution_composition.json`.
