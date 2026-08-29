# HESSIAN-GLOBAL-01 — symétries et résolution positive des cinq secteurs

Date : **9 août 2026**.

La façade la plus structurée est :

```lean
global_candidateA_hessian_projectionResolution_actionSymmetry_closure_gate
```

Elle combine le noyau construit par symétries exactes de l’action avec une
résolution positive de l’identité par les mêmes cinq secteurs.

## 1. Noyau réel

Les cinq familles de transformations Candidate-A fournissent les zéro-modes par
Noether. Le profil numérique donne :

\[
\dim\ker H=\sum_s m_s.
\]

## 2. Résolution positive

Les cinq projections bornées `P_s` satisfont :

\[
\sum_s P_sx=x
\]

et :

\[
\langle P_sx,x\rangle=\|P_sx\|^2.
\]

Le module

```text
P0EFTJanusProgramPFiniteProjectionNormResolution4D
```

en déduit automatiquement :

\[
\|x\|^2=\sum_s\|P_sx\|^2.
\]

La décomposition de norme n’est donc plus un champ autonome de la façade
analytique.

## 3. Hessien principal projeté

Une seule forme principale est restreinte aux cinq secteurs. Les dix formes
croisées symétriques sont générées automatiquement. Les cinq bornes diagonales
et la somme des normes croisées donnent la marge principale.

La perturbation physique H11, bornée sur le cœur dense, est ensuite soustraite.
La marge totale produit :

\[
c\|x\|^2\leq Q(x)
\]

puis :

\[
c\|x\|\leq\|Hx\|
\]

sur `(ker H)ᗮ`.

## 4. H12

La structure

```lean
GlobalCandidateAProjectionFiniteMarginActualKernelGap4D
```

ajoute seulement la stationnarité LL. Elle construit le paquet actual-kernel
attendu par H12.

Le gate

```lean
global_candidateA_projection_finite_margin_h12_closure_gate
```

fournit :

```text
Fredholm
indice zéro
image fermée
Green réduit
résolvante
stabilité perturbative
```

## 5. Données restantes

Après la famille locale :

1. cinq familles de symétries exactes ;
2. cinq projections positives résolvant l’identité ;
3. cinq estimations diagonales du Hessien principal ;
4. l’identité de décomposition du pairing principal ;
5. la borne dense-core du bloc physique H11 ;
6. la stricte positivité de la marge totale.

Les équations du noyau, l’indépendance, le comptage, la décomposition de norme,
le gap, Fredholm, Green et résolvante sont dérivés.

## 6. Statut

La façade, son audit et son workflow ciblé sont présents dans la PR #60. La PR
reste en brouillon en attente d’un build Lean complet et vert.
