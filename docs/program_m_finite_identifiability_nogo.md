# MF-ID-001 — Limite d'une observation finie

## Résultat

Une structure finie observée une seule fois ne peut pas identifier
universellement son mécanisme générateur. Si deux lois distinctes donnent une
probabilité non nulle à la même observation, toute règle qui ne voit que cette
observation renvoie nécessairement la même réponse pour les deux lois.

La preuve Lean est dans
`JanusFormal/Foundations/ProgramMFiniteIdentifiabilityNoGo.lean`.

## Conséquence pour Program M

Ajouter successivement des filtres aux contre-exemples déjà trouvés ne peut pas
produire, à lui seul, une preuve universelle de géométrie. Ces filtres restent
des diagnostics nécessaires, mais la revendication doit porter sur une loi
d'ensembles et sur son comportement quand la taille augmente.

Ce no-go ne suppose ni espace, ni métrique, ni dimension, ni causalité, ni
gorge. Il ne dit pas qu'une reconstruction est impossible avec des hypothèses
supplémentaires; il oblige à les déclarer.

