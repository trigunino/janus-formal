# MF-ADV-005 — Adversaire à moments identiques

## Construction

Le concurrent choisit une fois pour toute une phase globale :

- ordre total avec probabilité `1/6`;
- ordre à deux niveaux avec probabilité `2/3`;
- antichaîne avec probabilité `1/6`.

Chaque composante et leur mélange sont échangeables et projectifs. Le mélange
est non ergodique : même à grande taille, une réalisation reste dans une phase
globale aléatoire.

Ses moments sont exactement ceux utilisés pour Minkowski 1+1 dans MF-ENS-002 :

```text
paires      = (1/6)·1 + (2/3)·(1/2) + (1/6)·0 = 1/2
triples     = (1/6)·1 + (2/3)·0       + (1/6)·0 = 1/6
```

Ces égalités et la non-injectivité de la signature à deux moments sont prouvées
dans `JanusFormal/Foundations/ProgramMEnsembleMomentNoGo.lean`.

## Audit

Le gate MF-ENS-002 a été gelé puis évalué aux nouvelles tailles 192, 384, 768
et 1536. Les 240 réalisations stratifiées sont toutes rejetées. Le gate ne
compare donc pas seulement les moyennes d'ensemble : il demande que les deux
statistiques soient simultanément proches de leurs limites dans une même
réalisation.

Résultat : égaler un nombre fini de moments ne suffit pas à identifier une loi,
mais cet adversaire précis ne casse pas le gate.

## Décision laissée ouverte

La théorie des limites de posets traite les lois échangeables et leurs
représentations par noyaux : [Janson](https://arxiv.org/abs/0902.0306), puis
[Hladký–Máthé–Patel–Pikhurko](https://arxiv.org/abs/1211.2473). Program M doit
maintenant préciser si l'émergence demande une loi extrémale/ergodique ou si une
décomposition en phases est un résultat admissible. L'ergodicité n'est pas
ajoutée silencieusement à MF-ENS-001.

Le script est `scripts/audit_program_m_ensemble_moment_adversary.py` et la
sortie est `outputs/program_m/mf_adv_005_ensemble_moment_adversary.json`.

