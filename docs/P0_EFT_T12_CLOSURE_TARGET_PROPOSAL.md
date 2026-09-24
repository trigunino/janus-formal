# T12 — proposition de correction de la cible terminale

Statut : proposition à valider ; T12 reste ouvert.

Le raccord sectoriel à la fibre D9/Friedrichs positive est exclu par
`no_actual_to_fullFriedrichs_sector_pairing` : un champ Nakanishi–Lautrup
pur non nul a un auto-pairing strictement négatif, H11 compris, alors que
sa cible sectorielle a un pairing non négatif. La densité L2 ne change pas
cette incompatibilité.

## Modification proposée

Conserver le critère `hessianMatchesNaturalFredholmFamily`, la même action,
la géométrie réelle, les ghosts et antighosts, H11 et les quotients justifiés.
Remplacer uniquement la cible D9 positive imposée par une famille signée
construite depuis les opérateurs réels. Ne pas imposer les poids d'un modèle
modal avant d'avoir prouvé leur accord avec l'opérateur géométrique.

La fermeture exige toujours une preuve concrète du transport du Hessien,
des domaines et de la propriété Fredholm globale ; puis le raccord à la
ligne de Quillen existante, le certificat terminal, la façade et l'audit.
Aucune de ces conclusions ne devient une hypothèse. La densité L2 acquise
ne sera pas utilisée comme une densité en norme de graphe.

Cette correction retire une cible contradictoire ; elle ne prouve pas
que la famille signée réelle est Fredholm. Si cette propriété échoue dans
le cadre autorisé, T12 devra rester ouvert avec l'obstruction précise.

Vérification du 2026-09-24 : audit Lean gardé des deux théorèmes ci-dessus
vert (pic 3880 Mo), dépendances limitées à propext, Classical.choice et
Quot.sound. Aucun changement du statut terminal T12.
