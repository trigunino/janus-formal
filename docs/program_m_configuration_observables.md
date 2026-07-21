# MF-OBS-001 — Fonctionnelles scalaires sur les configurations

## Définition

Une fonctionnelle scalaire attribue une valeur à chaque configuration
relationnelle. Elle est admissible si deux configurations isomorphes reçoivent
la même valeur.

Autrement dit, changer les noms des objets et des relations ne doit pas changer
le résultat. La fonctionnelle descend alors du système étiqueté vers le
groupoïde construit par MF-CONF-001.

## Résultats formels

Lean définit une famille de configurations et la propriété
`GroupoidInvariant`. Il prouve :

- l'invariance le long des identités, inverses et compositions ;
- qu'appliquer une fonction scalaire à une observable invariante conserve
  l'invariance ;
- que toute constante est admissible mais non informative ;
- qu'une différence de valeurs entre deux configurations isomorphes réfute
  immédiatement l'admissibilité.
- que, sur toute famille non vide, deux constantes booléennes distinctes sont
  admissibles : l'invariance seule ne sélectionne donc jamais une fonctionnelle
  unique.

## Audit exhaustif minimal

Les 16 relations binaires sur deux objets sont testées sous les deux
renommages.

| Fonctionnelle | Invariante ? |
| --- | --- |
| nombre total de relations | oui |
| nombre de boucles | oui |
| nombre de paires mutuelles | oui |
| degré sortant de l'objet nommé `0` | non |

Le dernier exemple montre que l'interface ne se contente pas d'accepter toute
fonction numérique : elle élimine effectivement l'information artificielle des
étiquettes.

## Passerelle vers Program P

Les trois premières données de P0 existent maintenant sous forme abstraite :

1. configurations relationnelles ;
2. transformations admissibles ;
3. interface de fonctionnelles scalaires invariantes.

Cela ne sélectionne aucune fonctionnelle particulière. Program P peut désormais
être posé sur ce socle pour établir des no-go ou comparer des candidats, mais
une action physique demanderait encore une source indépendante.

Le module formel est
`JanusFormal/Foundations/ProgramMConfigurationObservables.lean`. Le script est
`scripts/audit_program_m_configuration_observables.py`; la sortie est
`outputs/program_m/mf_obs_001_configuration_observables.json`.
