# MF-ENS-001 — Contrat d'émergence sur des ensembles

## Objet mathématique

Le nouveau niveau reçoit, pour chaque taille finie `n`, une loi de probabilité
sur les ordres partiels étiquetés à `n` éléments. Deux cohérences sont exigées :

- **échangeabilité** : renommer les éléments ne change pas la loi;
- **projectivité** : extraire un sous-ensemble injectif redonne la loi de la
  taille correspondante.

Ce sont des hypothèses d'ensemble supplémentaires, pas des conséquences de
`MF-A0`. L'interface Lean est dans
`JanusFormal/Foundations/ProgramMEnsembleEmergence.lean`.

## Certificat demandé

Un candidat à l'émergence doit fournir des tests définis à toutes les tailles,
un ensemble non borné de tailles de validation jamais utilisées pour la
construction, puis démontrer :

1. que la probabilité d'acceptation tend vers `1` sous le modèle cible;
2. qu'elle tend vers `0` sous chaque concurrent déclaré non équivalent;
3. quelle relation d'équivalence exprime exactement l'unicité revendiquée.

Le théorème `EnsembleEmergenceCertificate.separates` extrait cette séparation
du certificat. MF-ENS-002 en instancie une première tranche finie pour deux lois,
mais aucun modèle géométrique ne satisfait encore le contrat asymptotique entier.

## Base bibliographique vérifiée

Le cadre rejoint la théorie existante des limites de posets et des posets
aléatoires échangeables : [Janson, *Poset limits and exchangeable random
posets*](https://arxiv.org/abs/0902.0306). La question d'unicité géométrique
reste distincte et difficile; voir aussi le récent résultat de Hauptvermutung
pour causal sets : [Müller, 2025](https://arxiv.org/abs/2503.01719).

Program M n'invente donc pas l'échangeabilité ou la projectivité. Sa tâche est
de les utiliser sans introduire implicitement une dimension, une variété, une
orientation physique ou une gorge.

MF-ADV-005 montre en plus qu'échangeabilité et projectivité autorisent des
mélanges globaux de phases. L'extrémalité/ergodicité devient donc une question
explicite du programme; elle n'est pas ajoutée aux axiomes de ce contrat.
