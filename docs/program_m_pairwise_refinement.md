# MF-REF-001 — Raffinement couvrant les paires

## Principe minimal

Un système de morceaux est **couvrant sur les paires** lorsque, pour tous
objets `x,y`, un morceau finit par contenir `x` et `y` ensemble. Cette condition
ne mentionne ni distance, ni dimension, ni géométrie.

## Théorème exact

Pour des données globales arbitraires attachées aux paires d'objets :

```text
toutes les paires sont couvertes
⇔ les restrictions locales déterminent au plus un global.
```

Lean prouve les deux directions. Si une paire n'est jamais couverte, deux
fonctions booléennes globales peuvent différer uniquement sur cette paire tout
en restant identiques sur chaque morceau.

L'audit énumère les 256 familles possibles de morceaux sur trois objets et ne
trouve aucun échec. Pour le témoin de MF-GEO-002, ajouter le morceau `{2,3}`
rend la famille couvrante sur toutes les paires et supprime exactement le trou
d'information identifié.

## Ce que cela résout — et ne résout pas

MF-REF-001 donne une condition nécessaire et suffisante d'**unicité du
recollement**, analogue à la partie séparée de la condition de faisceau
([Stacks Project, section 6.7](https://stacks.math.columbia.edu/tag/006S)).

Il ne construit pas les valeurs locales, ne prouve pas qu'elles satisfont les
axiomes d'une métrique et ne choisit pas une géométrie parmi plusieurs données
locales possibles. Le prochain problème est donc l'existence et la sélection
des données locales, pas davantage de collage abstrait.

Le module formel est
`JanusFormal/Foundations/ProgramMPairwiseRefinement.lean`. Le script est
`scripts/audit_program_m_pairwise_refinement.py`; la sortie est
`outputs/program_m/mf_ref_001_pairwise_refinement.json`.
