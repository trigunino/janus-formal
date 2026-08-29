# HESSIAN-GLOBAL-01 — six Hessiennes physiques canoniques

Date : **8 août 2026**.

Cette couche supprime la dernière liberté artificielle de l’entrée H11 : les
six formes non-Robin ne sont plus fournies par l’utilisateur.

Elles sont définies comme les véritables seconds Fréchet des champs scalaires
existants de `FullCoupledActionBlocks` :

1. interaction Candidate-A ;
2. Einstein–Hilbert `+` ;
3. Einstein–Hilbert `-` ;
4. Maxwell `+` ;
5. Maxwell `-` ;
6. finite/null-BV.

Le module générique démontre :

\[
D^2 S_{\mathrm{phys}}
=
\sum_{j=1}^{6} D^2 S_j + D^2 S_{\mathrm{Robin}}.
\]

Sur le cœur lisse dense, la somme canonique est tirée en arrière par le vrai
morphisme `Core -> chart`. Une seule estimation

\[
\|Tx\|_{\mathrm{chart}}\le C\|\iota x\|_{\mathrm{graph}}
\]

contrôle alors les six blocs avec la constante

\[
\left(\sum_j\|D^2S_j\|\right)C^2.
\]

## Robin dérivé de l’égalité d’action H10

Le module

```text
P0EFTJanusProgramPSecondFrechetLinearPullback4D
```

formalise la règle :

\[
D^2(f\circ L)(x)=L^*D^2f(Lx)L
\]

pour une application linéaire continue `L`.

Par conséquent, la route préférée ne reçoit plus une égalité entre Hessiennes
Robin. Elle reçoit seulement :

- l’identité scalaire du bloc Robin avec l’action GHY H10 après projection ;
- l’annulation de la projection au point de base ;
- l’accord, sur le cœur typé, entre la projection locale et la projection dans
  le domaine complété.

Le module

```text
P0EFTJanusProgramPGlobalCandidateAH10RobinProjectionCore4D
```

construit alors automatiquement l’accord des Hessiennes sur le cœur.

## Terminaux

Le terminal de compatibilité est :

```lean
global_candidateA_hessian_canonicalSix_denseCore_frontier_gate
```

Le terminal préféré, sans égalité de Hessiennes fournie, est :

```lean
global_candidateA_hessian_canonicalSix_projectionCore_frontier_gate
```

Il attend :

- les données de projection H10 au niveau de l’action ;
- la borne du morphisme cœur-vers-chart ;
- le paquet de gap/coercivité du noyau réel.

Aucune forme physique arbitraire, constante bloc par bloc, égalité de Hessien
Robin ou application de régularisation `Hilbert -> champs lisses` n’est
introduite.
