# HESSIAN-GLOBAL-01 — frontière du Hessien principal projeté

Date : **9 août 2026**.

Cette note décrit la chaîne analytique la plus courte actuellement exposée pour
la fermeture H10–H14.

## 1. Entrée principale

On part d’une seule forme bilinéaire continue principale :

\[
B_{\mathrm{principal}}:\mathcal H\times\mathcal H\to\mathbb R.
\]

Cinq projections bornées isolent les secteurs Candidate-A : métrique,
Abélien, SpinC primitif, LL et bord/BV.

Les cinq restrictions diagonales possèdent des constantes positives. Les dix
formes croisées sont générées automatiquement par :

\[
B_{st}(x,y)
=
B(P_sx,P_ty)+B(P_tx,P_sy).
\]

Leurs constantes sont leurs normes d’opérateur.

## 2. Marge totale

La marge principale est :

\[
c_{\mathrm{principal}}
=
c_{\mathrm{floor}}-
\sum_{s<t}\|B_{st}\|.
\]

La véritable perturbation H11 possède une constante `Cphysical` calculée depuis
le cœur dense. La marge totale est :

\[
c_{\mathrm{total}}
=
c_{\mathrm{principal}}-C_{\mathrm{physical}}>0.
\]

## 3. Passage à l’opérateur

L’énergie totale est identifiée au pairing du véritable opérateur :

\[
Q_{\mathrm{total}}(x)
\leq
\|x\|\,\|Hx\|.
\]

Ainsi :

\[
c_{\mathrm{total}}\|x\|
\leq\|Hx\|.
\]

Sur `(ker H)ᗮ`, cette borne remplit directement le champ analytique du paquet
`SelfAdjointKernelComplementGapData`.

## 4. Sorties

La façade :

```lean
global_candidateA_hessian_projected_principal_frontier_gate
```

conserve le terminal H10–H14.

Les checkpoints analytiques sont :

```lean
global_candidateA_hessian_projected_principal_garding_gate
global_candidateA_hessian_projected_principal_actual_kernel_gap_gate
global_candidateA_hessian_projected_principal_h12_gate
```

Ils donnent successivement :

```text
marge quadratique totale
gap de l’opérateur sur l’orthogonal du noyau
Fredholm et indice zéro
Green réduit
résolvante réelle
stabilité perturbative
```

## 5. Travail restant

La frontière physique est réduite à :

1. construire les cinq projections sectorielles ;
2. prouver la décomposition de la norme ;
3. prouver cinq estimations diagonales ;
4. identifier la décomposition du pairing principal ;
5. calculer la borne H11 physique sur le cœur dense ;
6. fournir les coordonnées finies du vrai noyau ou les obtenir des symétries de
   l’action.

La PR #60 reste en brouillon tant que la chaîne Lean complète n’est pas verte.
