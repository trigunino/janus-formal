# HESSIAN-GLOBAL-01 — symétries et projecteurs sectoriels naturels

Date : **9 août 2026**.

La façade structurelle la plus réduite est :

```lean
global_candidateA_hessian_selfAdjointProjection_actionSymmetry_closure_gate
```

## 1. Noyau par symétries exactes

Les cinq familles physiques sont construites comme transformations locales de
la véritable action Candidate-A. L’invariance de l’action implique les
équations du noyau du Hessien. Le profil numérique donne le comptage exact par
secteur.

## 2. Cinq projecteurs naturels

Les cinq applications sectorielles bornées satisfont :

```text
P_s² = P_s
⟨P_s x,y⟩ = ⟨x,P_s y⟩
Σ_s P_s x = x
```

La symétrie et l’idempotence donnent :

\[
\langle P_sx,x\rangle=\|P_sx\|^2.
\]

La résolution de l’identité donne alors :

\[
\|x\|^2=\sum_s\|P_sx\|^2.
\]

Aucune positivité ni identité de Pythagore n’est fournie indépendamment.

## 3. Hessien principal projeté

Une seule forme principale continue est restreinte aux cinq secteurs. Les dix
formes croisées symétriques sont dérivées. Cinq bornes diagonales et la somme
des dix normes croisées produisent la marge principale.

La constante physique H11, calculée sur le cœur dense, est soustraite une seule
fois. La marge totale fournit la Gårding puis la borne d’opérateur sur
`(ker H)ᗮ`.

## 4. H12 et H14

Le paquet

```lean
GlobalCandidateASelfAdjointProjectionFiniteMarginActualKernelGap4D
```

ajoute seulement la stationnarité LL à la preuve de marge sur le véritable
complément du noyau.

Le gate

```lean
global_candidateA_selfAdjoint_projection_h12_closure_gate
```

construit :

```text
Fredholm
indice zéro
image fermée
Green réduit
résolvante
stabilité perturbative
```

La façade terminale conserve H10, H11, H12, H13 et H14.

## 5. Entrées analytiques restantes

Après la famille locale :

1. cinq familles de symétries exactes de l’action ;
2. cinq projecteurs sectoriels symétriques idempotents résolvant l’identité ;
3. cinq estimations diagonales du Hessien principal ;
4. l’identité de décomposition du pairing principal ;
5. la borne dense-core du bloc physique H11 ;
6. la stricte positivité de la marge totale.

Les équations du noyau, l’indépendance, le comptage, la positivité des
projecteurs, la décomposition de norme, le gap, Fredholm, Green et résolvante
sont dérivés.

## 6. Statut

La façade, l’audit et le workflow ciblé appartiennent à la PR #60. La PR reste
en brouillon tant que la chaîne Lean complète n’est pas verte.
