# HESSIAN-GLOBAL-01 — fermeture unifiée par symétries et Hessien projeté

Date : **9 août 2026**.

La façade publique unifiée est :

```lean
global_candidateA_hessian_projectedPrincipal_actionSymmetry_closure_gate
```

Elle réunit les deux réductions les plus fortes de la fermeture H10–H14.

## 1. Construction du noyau

Les cinq familles physiques sont :

```text
metric / diffeomorphism
Abelian gauge
primitive SpinC matter
longitudinal / LL
boundary / finite-BV
```

Pour chaque générateur `v`, une invariance locale exacte de l’action :

\[
S(x+t v)=S(x)
\]

implique automatiquement :

\[
Hv=0.
\]

Un profil numérique fixe les cinq multiplicités et la chaîne démontre :

\[
\dim\ker H
=
\sum_s \operatorname{multiplicité}(s).
\]

Checkpoint :

```lean
global_candidateA_hessian_projectedPrincipal_actionSymmetry_exact_count
```

## 2. Construction du gap sur le vrai complément

Un seul Hessien principal continu est projeté sur les cinq secteurs. Les cinq
restrictions diagonales portent les estimations coercives. Les dix formes
croisées symétriques sont construites automatiquement.

Avec la constante physique H11 calculée depuis le cœur dense, la marge totale
est :

\[
c_{\mathrm{total}}
=
c_{\mathrm{floor}}
-
\sum_{s<t}\|B_{st}\|
-
C_{\mathrm{phys}}.
\]

Le checkpoint quadratique est :

```lean
global_candidateA_hessian_projectedPrincipal_actionSymmetry_garding_gate
```

La borne quadratique est ensuite convertie en :

\[
c_{\mathrm{total}}\|x\|\leq\|Hx\|
\]

sur `(ker H)ᗮ`.

Checkpoint :

```lean
global_candidateA_hessian_projectedPrincipal_actionSymmetry_actualKernelGap_gate
```

## 3. Sorties H12 et H14

Le gap actual-kernel produit :

```text
image fermée
Fredholm
indice zéro
Green réduit
résolvante réelle dans le gap
stabilité sous petite perturbation auto-adjointe
```

Checkpoint :

```lean
global_candidateA_hessian_projectedPrincipal_actionSymmetry_h12_gate
```

La façade terminale conserve simultanément :

```text
H10  bord mobile GHY same-action
H13  vrai Hessien local Candidate-A
H11  extension physique continue sur le domaine commun
H12  Fredholm/index zéro/Green/résolvante
H14  certificat global
```

## 4. Données physiques restantes

Après construction de la famille locale, les travaux irréductibles sont :

1. construire les cinq familles de transformations et prouver l’invariance de
   l’action ;
2. démontrer leur orthogonalité et leur exhaustivité par Gårding ;
3. construire les cinq projections bornées du Hessien principal ;
4. prouver les cinq bornes diagonales ;
5. vérifier la décomposition du pairing principal ;
6. établir la borne cœur-vers-chart et la constante physique H11 ;
7. vérifier la positivité stricte de la marge totale.

Les équations `Hv = 0`, le projecteur de défaut, le paramétrix, la fermeture de
l’image, l’indice et la résolvante ne sont plus des hypothèses indépendantes.

## 5. Statut

La façade, l’audit et le workflow ciblé sont présents sur la branche de la PR
#60. La PR reste en brouillon jusqu’à certification Lean intégrale.
