# HESSIAN-GLOBAL-01 — Gårding par dominance sectorielle finie

Date : **9 août 2026**.

Cette note réduit la dernière estimation principale de la façade
`global_candidateA_hessian_preferred_action_symmetry_frontier_gate` à un calcul
fini sur les cinq secteurs physiques Candidate-A.

## 1. Décomposition

Pour une variation `x`, on choisit cinq poids quadratiques non négatifs
`N_s(x)` tels que :

\[
\|x\|^2=\sum_s N_s(x).
\]

Chaque secteur possède une constante diagonale positive `c_s`, et l’énergie
diagonale vérifie :

\[
\sum_s c_s N_s(x)\leq Q_{\mathrm{diag}}(x).
\]

Une constante `c_floor` est choisie sous les cinq `c_s`.

## 2. Couplages

Les termes hors diagonale sont indexés par les vingt-cinq couples ordonnés de
secteurs. Pour chaque couple `(s,t)` :

\[
|Q_{st}(x)|\leq C_{st}\|x\|^2.
\]

Le module

```text
P0EFTJanusProgramPFiniteSectorPairwiseGarding4D
```

somme automatiquement ces estimations :

\[
\left|\sum_{s,t}Q_{st}(x)\right|
\leq
\left(\sum_{s,t}C_{st}\right)\|x\|^2.
\]

## 3. Marge globale

Sous la condition finie :

\[
\sum_{s,t}C_{st}<c_{\mathrm{floor}},
\]

la constante globale est construite :

\[
c_{\mathrm{principal}}
=
c_{\mathrm{floor}}-\sum_{s,t}C_{st}>0.
\]

Le théorème donne alors :

\[
c_{\mathrm{principal}}\|x\|^2
\leq Q_{\mathrm{principal}}(x).
\]

La Gårding principale n’est donc plus une hypothèse globale opaque.

## 4. Spécialisation Candidate-A

Le module

```text
P0EFTJanusProgramPCandidateAFiveSectorPairwiseGarding4D
```

nomme les cinq constantes diagonales :

```text
metric / diffeomorphism
Abelian gauge
primitive SpinC matter
longitudinal / LL
boundary / finite-BV
```

et expose :

```lean
CandidateAFiveSectorPairwiseGardingData
CandidateAFiveSectorPairwiseGardingData.candidateA_five_sector_pairwise_garding_gate
```

Une route plus compacte, avec une constante globale déjà sommée pour les
couplages, reste disponible dans :

```text
P0EFTJanusProgramPCandidateAFiveSectorGardingDominance4D
```

## 5. Raccord à H10–H14

La façade :

```lean
global_candidateA_hessian_preferred_sector_garding_frontier_gate
```

conserve l’entrée terminale numérique cinq secteurs. Son prérequis principal
peut maintenant être obtenu par :

```lean
global_candidateA_hessian_five_sector_pairwise_garding_gate
```

Puis la petite perturbation physique H11 est comparée à la marge calculée :

\[
C_{\mathrm{phys}}
<
c_{\mathrm{floor}}-\sum_{s,t}C_{st}.
\]

## 6. Travail restant

Les preuves analytiques sont désormais locales et finies :

1. identifier les cinq composantes diagonales du bloc principal ;
2. démontrer leurs cinq bornes coercives ;
3. calculer les vingt-cinq blocs croisés ;
4. borner chaque bloc croisé ;
5. vérifier la stricte dominance diagonale ;
6. comparer la marge résultante à la constante physique H11 déjà calculée sur
   le cœur dense.

Les équations de noyau, le projecteur de défaut, la fermeture de l’image, le
paramétrix et l’indice ne sont pas redemandés : ils sont reconstruits en aval.

## 7. Statut Lean

La réduction sectorielle, sa spécialisation Candidate-A et la façade publique
sont présentes sur la branche de la PR #60. La certification finale reste
conditionnée par un build Lean vert de la chaîne complète.
