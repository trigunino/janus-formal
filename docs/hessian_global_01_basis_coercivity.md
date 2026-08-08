# HESSIAN-GLOBAL-01 — frontière base du noyau et coercivité

Date : **9 août 2026**.

Cette couche retire les deux derniers paquets abstraits de la fermeture
H10--H14 préférée.

## 1. Projection H10

La famille locale H10-réduite possède déjà sa projection linéaire bornée vers
le cœur métrique-normal. Sur le cœur lisse diagonal, cette projection se
compose avec le véritable morphisme cœur-vers-chart.

La seule estimation

\[
\|T x\|_{\mathrm{chart}}
\le C_T\|\iota x\|_{\mathrm{graphe}}
\]

implique automatiquement

\[
\|P_{\partial}T x\|
\le \|P_{\partial}\|C_T\|\iota x\|.
\]

`LinearMap.extendOfNorm` construit alors la projection complétée. L’accord sur
le cœur dense et le Hessien Robin H10 sont dérivés ; aucune projection de bord
complétée n’est fournie comme donnée indépendante.

## 2. Les six blocs physiques

Les six blocs non-Robin sont les véritables seconds Fréchet de :

1. l’interaction Candidate-A ;
2. Einstein--Hilbert `+` ;
3. Einstein--Hilbert `-` ;
4. Maxwell `+` ;
5. Maxwell `-` ;
6. finite/null-BV.

Leur borne commune est déduite de la même estimation cœur-vers-chart. Le
septième bloc est le Hessien Robin de l’action GHY H10.

## 3. Base du vrai noyau

Le paquet

```lean
SelfAdjointKernelBasisCoercivityData H hSelfAdjoint ZeroMode
```

contient une base finie de `ker H`, indexée par le type physique `ZeroMode`, et
une constante `c > 0` telle que

\[
c\|x\|^2\le \langle x,Hx\rangle,
\qquad x\in(\ker H)^\perp.
\]

Cauchy--Schwarz donne

\[
c\|x\|\le\|Hx\|.
\]

Le paquet abstrait de gap utilisé par H12 est donc construit automatiquement.
La dimension du noyau est exactement :

\[
\dim\ker H=\#\mathrm{ZeroMode}.
\]

## 4. Terminal

Le point d’entrée est :

```lean
global_candidateA_hessian_canonicalSix_basisCoercivity_frontier_gate
```

Après les données géométriques et la famille locale, il ne demande que :

1. la borne du morphisme cœur lisse vers le chart physique D10-free ;
2. la base du vrai noyau et la coercivité quadratique sur son orthogonal.

Il reconstruit la projection H10 complétée, l’extension physique H11, le gap
H12, puis les certificats H10--H14, le Green réduit et la résolvante réelle.

La chaîne reste en brouillon tant que le build Lean complet de la PR n’est pas
vert ; aucun nouvel axiome, `sorry`, projecteur artificiel ou paramétrix fourni
n’est introduit par cette réduction.
