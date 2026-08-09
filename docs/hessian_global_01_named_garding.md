# HESSIAN-GLOBAL-01 — modes nommés et estimation globale de Gårding

Date : **9 août 2026**.

Cette couche reformule l’entrée H12 sous la forme réellement produite par une
preuve elliptique globale.

## 1. Modes ambiants concrets

On fixe un type fini `ZeroMode` et des vecteurs

```lean
vector : ZeroMode → E
```

pour le véritable Hessien augmenté `H`. Les données exigées sont :

```text
H (vector mode) = 0
indépendance linéaire des modes dans ker H
span des modes = ker H
```

Aucune équivalence de coordonnées avec le noyau n’est fournie. La base

```lean
Basis ZeroMode ℝ (ker H)
```

est reconstruite par `Basis.mk`. On obtient alors automatiquement

\[
\dim\ker H=\#\mathrm{ZeroMode}.
\]

## 2. Gårding avec défaut fini nommé

L’estimation globale stockée est

\[
c\|x\|^2
\le
\langle x,Hx\rangle
+
C\sum_{m\in\mathrm{ZeroMode}}
  |\langle x,v_m\rangle|^2,
\qquad c>0.
\]

Pour

\[
x\in(\ker H)^\perp,
\]

chaque coefficient \(\langle x,v_m\rangle\) est nul. Il reste donc

\[
c\|x\|^2\le\langle x,Hx\rangle.
\]

Cauchy--Schwarz donne ensuite

\[
c\|x\|\le\|Hx\|.
\]

Cette borne est exactement celle consommée par les gates du complément réel
du noyau.

## 3. Spécialisation Candidate-A

Le paquet

```lean
GlobalCandidateAActualKernelNamedGarding4D
```

porte l’estimation précédente pour

```lean
globalCandidateAActualKernelOperator
```

et conserve la stationnarité LL. Il construit :

```text
GlobalCandidateAActualKernelGap4D
noyau fini
image fermée
Fredholm
indice zéro
Green réduit
résolvante locale
stabilité perturbative
```

## 4. Terminal H10--H14

Le point d’entrée est :

```lean
global_candidateA_hessian_canonicalSix_namedGarding_frontier_gate
```

Après la famille locale H10-réduite, il ne demande plus que deux paquets
analytiques :

1. la borne du véritable morphisme du cœur lisse vers le chart physique
   D10-free ;
2. les modes ambiants nommés, leur indépendance et génération de `ker H`, puis
   l’estimation globale de Gårding ci-dessus.

La projection H10 complétée, les six Hessiennes non-Robin, l’extension H11 et
le gap H12 sont tous reconstruits. Aucun projecteur fini artificiel,
paramétrix, inverse généralisé, équivalence du noyau fournie à la main ou
gap supposé n’est ajouté.

La chaîne reste en brouillon tant qu’un build Lean complet de la PR n’est pas
vert. Les fichiers de cette réduction ne contiennent volontairement ni
`sorry`, ni `admit`, ni nouvel axiome.
