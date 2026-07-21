# MF-PAT-003 — Ce que force réellement le rang quatre

## Résultat

Dans la classe des ordres obtenus par deux coordonnées continues et l'ordre
produit, la distribution complète des 16 posets non étiquetés de rang 4 suffit
à forcer la loi uniforme de Minkowski 1+1.

La preuve utilise le théorème 2 de Chan, Král', Noel, Pehova, Sharifzadeh et
Volec : certains ensembles de motifs de permutation de rang 4 sont
`Σ-forcing`, c'est-à-dire que leur seule probabilité totale force le permuton
uniforme ([arXiv:1909.11027](https://arxiv.org/abs/1909.11027)).

L'un de leurs ensembles est :

```text
1234, 1432, 2143, 2341, 3214, 3412, 4123, 4321
```

Le certificat MF-PAT-003 énumère exactement les 24 permutations et montre que
cet ensemble est l'union de sept classes entières de posets non étiquetés. Si
les 16 probabilités de posets valent celles de Minkowski, la somme de ces sept
classes vaut donc `8/24 = 1/3`; le théorème publié force alors le permuton
uniforme.

## Ce que cela ne prouve pas

Ce résultat est conditionnel à l'existence de deux coordonnées continues dont
la relation observée est leur ordre produit. Program M ne doit pas introduire
ces coordonnées en secret. Parmi tous les noyaux de posets échangeables, le
rang 4 pourrait encore ne pas être unique.

La prochaine question change donc : peut-on dériver la représentation par deux
ordres à partir de la structure faible, ou construire un noyau de posets sans
deux coordonnées qui copie les 16 probabilités de rang 4 ?

Le certificat est `scripts/audit_program_m_rank_four_forcing.py`; sa sortie est
`outputs/program_m/mf_pat_003_rank_four_forcing.json`.
