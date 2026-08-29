# HESSIAN-GLOBAL-01 — frontière au noyau réel

Date : **8 août 2026**.

Cette note remplace, pour la route préférée, le projecteur fini abstrait utilisé
dans les premières formulations H12. Le Hessien augmenté étant borné et
auto-adjoint, l’espace réduit canonique est directement

\[
(\ker H)^\perp.
\]

Aucun choix de projecteur, de complément ou de quotient n’est nécessaire.

## 1. Réduction auto-adjointe canonique

Le module

```text
P0EFTJanusProgramPSelfAdjointKernelComplementReduction4D
```

construit la restriction

```text
H_red : (ker H)ᗮ → (ker H)ᗮ.
```

L’auto-adjonction de `H` garantit l’invariance de cet espace. Les seules données
analytiques sont ensuite :

```text
FiniteDimensional ℝ (ker H)
gap > 0
gap ‖x‖ ≤ ‖H_red x‖
```

pour tout `x ∈ (ker H)ᗮ`.

Ces données impliquent automatiquement :

```text
range H = (ker H)ᗮ
range H fermée
H Fredholm
index H = 0
H_red bijectif
```

ainsi que l’existence du Green réduit

```text
G_red = H_red⁻¹
```

avec

\[
\|G_{\mathrm{red}}\|\leq \mathrm{gap}^{-1}.
\]

## 2. Résolvante dans le gap

Le module

```text
P0EFTJanusProgramPSelfAdjointKernelComplementResolvent4D
```

construit, pour

\[
|\lambda|<\mathrm{gap},
\]

la résolvante réelle

```text
R(λ) = (H_red - λ I)⁻¹
```

et prouve

\[
\|R(\lambda)\|
\leq
(\mathrm{gap}-|\lambda|)^{-1}.
\]

L’identité de résolvante est installée sur le même espace réduit :

\[
R(\lambda)-R(\mu)
=
(\lambda-\mu)R(\lambda)R(\mu).
\]

À `λ = 0`, cette résolvante redonne exactement `G_red`.

## 3. Spécialisation Candidate-A

Les modules

```text
P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelComplement4D
P0EFTJanusProgramPGlobalCandidateAAugmentedActualKernelResolvent4D
```

appliquent ces résultats au véritable représentant de Riesz du Hessien
Candidate-A augmenté.

Le paquet H12 préféré est désormais :

```lean
GlobalCandidateAActualKernelGap4D
```

Il contient :

```text
le noyau réel fini
le gap sur son orthogonal
la stationnarité LL
```

et rien d’autre.

Le module

```text
P0EFTJanusProgramPGlobalCandidateAActualKernelGapFromFredholm4D
```

montre également que l’ancienne paire

```text
range_closed
kernel_finite
```

produit automatiquement ce gap par le théorème de l’inverse borné. La route au
noyau réel n’ajoute donc aucune hypothèse à un certificat H12 déjà construit.

## 4. H11 ramené à une seule estimation

Le Robin est déjà la seconde dérivée de Fréchet H10. On définit donc sur le
cœur lisse :

\[
B_{6}
=
B_{\mathrm{phys}}-B_{\mathrm{Robin}}.
\]

Le module

```text
P0EFTJanusProgramPGlobalCandidateASixPhysicalAggregateBound4D
```

ne demande qu’une estimation :

\[
|B_6(x,y)|
\leq
C_6\|\iota x\|\,\|\iota y\|.
\]

La continuité de Robin donne automatiquement sa propre constante, puis la
borne complète est :

\[
C_{\mathrm{phys}}
=
\|B_{\mathrm{Robin}}\|+C_6.
\]

L’extension H11 est ensuite construite canoniquement par densité avec
`LinearMap.extendOfNorm`. Aucune forme continue n’est choisie à la main.

## 5. Nouvelle frontière terminale

La façade

```text
P0EFTJanusProgramPGlobalHessianActualKernelBoundedFrontier4D
```

expose :

```lean
global_candidateA_hessian_actualKernel_bounded_frontier_gate
```

avec exactement trois paquets :

```text
1. famille locale H10-réduite ;
2. une estimation du reste physique non-Robin ;
3. noyau réel fini + gap sur son orthogonal.
```

La sortie assemble :

```text
H10 : same-action GHY et véritable second Fréchet
H13 : raccord matière–LL de la même action
H11 : extension physique sur le domaine commun
H12 : Fredholm et indice zéro
scindage exact : range H = (ker H)ᗮ
Green réduit
résolvante réelle dans le gap
```

## 6. Frontière mathématique restante

Hors certification Lean, les contenus encore irréductibles sont maintenant :

1. construire concrètement la famille locale avec ses six blocs physiques
   `C²` ;
2. prouver une seule estimation bilinéaire pour leur somme ;
3. démontrer la finitude du véritable noyau et une borne coercive sur son
   orthogonal.

Il n’est plus nécessaire de construire un projecteur de zéro-modes, un
paramétrix abstrait, sept prolongements indépendants ou une seconde
complétion.
