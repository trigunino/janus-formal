# MF-ENS-002 — Première séparation d'ensembles

## Comparaison

Deux lois exactement échangeables et projectives sont comparées à cardinalité
fixée :

- cible : points iid uniformes dans un diamant de Minkowski 1+1, ordonnés dans
  les deux coordonnées nulles;
- concurrent : chaque élément reçoit iid un niveau bas ou haut, et tous les bas
  précèdent tous les hauts.

Le second modèle est un noyau de poset échangeable standard au sens de la
théorie des limites de posets de [Janson](https://arxiv.org/abs/0902.0306). Il
n'utilise ni variété ni métrique.

Les deux lois ont la même fraction limite de paires comparables, `1/2`. Ce
diagnostic ne peut donc pas les séparer. La fraction de triples formant une
chaîne stricte tend en revanche vers `1/6` pour la cible et vaut exactement
`0` pour le concurrent.

## Résultat et erreur conservée

Le premier seuil avait été placé par erreur à `1/6`, exactement sur la limite
de la cible. Ses taux d'acceptation restent entre `0.359` et `0.563` aux tailles
128–1024 : cet échec est conservé.

Après correction analytique, le seuil successeur est le milieu `1/12`. Sur de
nouvelles tailles 160, 320, 640 et 1280, avec 64 réalisations par modèle et par
taille :

- cible acceptée : `256/256`;
- concurrent accepté : `0/256`.

Le script est `scripts/audit_program_m_ensemble_separation.py`; les résultats
sont dans `outputs/program_m/mf_ens_002_ensemble_separation.json`. Lean prouve
séparément qu'un ordre à deux niveaux ne possède aucune chaîne stricte de trois
éléments dans
`JanusFormal/Foundations/ProgramMEnsembleFirstSeparation.lean`.

## Limite

C'est une séparation réelle mais étroite entre deux lois déclarées. Ce n'est ni
une preuve des limites asymptotiques de MF-ENS-001, ni une identification de la
géométrie, ni une preuve d'unicité contre tous les noyaux de posets.

