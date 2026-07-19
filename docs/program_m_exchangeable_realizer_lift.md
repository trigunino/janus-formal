# MF-REP-004 — Lift échangeable des deux ordres

## Problème

La compacité de la dimension fournit une paire d'ordres pour chaque poset
global de dimension au plus 2, mais un choix déterministe arbitraire peut casser
l'échangeabilité. Un choix déterministe n'est cependant pas nécessaire : il
suffit de construire une loi jointe échangeable sur le poset et ses réalisateurs.

## Proposition conditionnelle

Soit `μ` une loi échangeable sur les posets dénombrables, portée par les posets
de dimension au plus 2. Il existe une loi échangeable sur `(P,L1,L2)` telle que
`P = L1 ∩ L2` et dont la marginale en `P` est `μ`.

Preuve assemblée à partir d'outils standards :

1. les espaces de relations sur `N` sont compacts métrisables et l'ensemble
   fermé des triples réalisateurs a des fibres compactes non vides ;
2. un théorème de sélection borélienne fournit une première loi jointe ;
3. on la moyenne sur le groupe fini `S_n` ; sa marginale reste `μ` ;
4. une sous-suite converge par compacité ; sa limite est invariante sous toute
   permutation finie ;
5. si `μ` est ergodique, un point extrémal de l'ensemble compact convexe des
   lifts invariants est ergodique. En effet, toute décomposition aurait des
   marginales invariantes dont la moyenne vaut l'extrémale `μ`.

Une paire ergodique d'ordres totaux échangeables détermine alors un permuton
non aléatoire par la théorie des limites de permutations. Les marginales sont
uniformes : la restriction d'un ordre total échangeable à `n` étiquettes est
uniforme parmi les `n!` ordres.

Cette proposition complète les représentations générales des posets
échangeables de [Janson](https://arxiv.org/abs/0902.0306) avec la théorie des
limites de permutations ; voir aussi l'introduction aux permutons de
[Borga](https://arxiv.org/abs/2107.09699). Elle reste conditionnelle au fait que
la loi soit portée par des posets globalement de dimension au plus 2.

## Certificat fini

MF-REP-004 part d'un poset à cinq objets et d'une paire réalisatrice, puis
moyenne exactement leur orbite sur les 120 éléments de `S5`. Le certificat
vérifie que :

- chaque paire réalise toujours son poset ;
- la loi jointe est invariante par les transpositions adjacentes, donc par `S5` ;
- sa marginale poset est également invariante ;
- la projection conserve toute la masse.

Le script est `scripts/audit_program_m_exchangeable_realizer_lift.py`; la
sortie est `outputs/program_m/mf_rep_004_exchangeable_realizer_lift.json`.
