# HESSIAN-GLOBAL-01 — exclusion des zéro-modes cachés

Date : **9 août 2026**.

Cette couche retire l’hypothèse terminale

```text
span des modes nommés = ker H.
```

## 1. Décomposition orthogonale du noyau

Soit `S` le sous-espace de `ker H` engendré par les modes physiques nommés.
Pour tout `z ∈ ker H`, on utilise la décomposition hilbertienne

\[
z=p+q,
\qquad p\in S,
\qquad q\in S^\perp.
\]

Comme les modes nommés sont annulés par `H`, on a `S ⊆ ker H`. Ainsi
`Hq = 0`.

## 2. Gårding élimine le reste

L’estimation globale est

\[
c\|x\|^2
\le
\langle x,Hx\rangle
+C\sum_m |\langle x,v_m\rangle|^2,
\qquad c>0.
\]

Pour `q ∈ Sᗮ`, tous les coefficients du défaut fini sont nuls. Comme `Hq=0`,

\[
c\|q\|^2\le0.
\]

Donc `q=0`. Chaque élément du noyau appartient à `S`, et par conséquent

\[
S=\ker H.
\]

La base du noyau, sa dimension et le gap sur son orthogonal sont alors
construits automatiquement.

## 3. Deux formes concrètes d’entrée

### Décomposition par coefficients

```lean
FiniteKernelNamedDecompositionData
```

permet de donner directement, pour chaque élément du noyau, ses coefficients
dans les modes nommés. Le module reconstruit l’égalité de span.

### Absence de modes cachés

```lean
FiniteKernelNamedModeNoHiddenData
```

ne demande pas cette formule. Il demande seulement la décomposition
orthogonale standard et la Gårding globale ; la coercivité prouve que la
composante orthogonale est nulle.

## 4. Perturbation bornée

Le module

```lean
FiniteKernelNamedReferenceGardingPerturbationData
```

traite une écriture

\[
H=A+K.
\]

Si `A` possède une Gårding nommée de constante `c` et

\[
\|K\|<c,
\]

alors `H` conserve le même défaut fini avec constante

\[
c-\|K\|>0.
\]

Cette forme correspond à l’opérateur elliptique principal complété par les
blocs physiques bornés.

## 5. Terminal Candidate-A

Le gate

```lean
global_candidateA_hessian_canonicalSix_noHidden_frontier_gate
```

consomme :

1. la famille locale H10-réduite ;
2. la borne du vrai morphisme cœur lisse vers chart physique ;
3. des modes nommés indépendants et annulés par le Hessien ;
4. la décomposition orthogonale standard du noyau ;
5. une estimation globale de Gårding avec défaut sur ces modes.

Il dérive la génération exacte du noyau avant de construire H12 et la fermeture
H10--H14. Aucun projecteur fini artificiel, paramétrix, inverse généralisé,
base abstraite ou égalité de span fournie à la main n’est introduit.

La validation Lean complète reste à obtenir ; la couche demeure donc en
brouillon et n’emploie ni `sorry`, ni `admit`, ni nouvel axiome.
