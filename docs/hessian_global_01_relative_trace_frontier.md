# HESSIAN-GLOBAL-01 — frontière de trace et déterminant relatifs

Date du lot : **8 août 2026**.

Cette page commence après la fermeture structurelle H10–H14 et après la
construction de la résolvante réduite. Elle explique pourquoi le déterminant
ne doit pas être construit à partir de l’exponentielle du Riesz borné, puis
isole l’entrée analytique correcte.

Les nouveaux modules restent à valider par Lean.

## 1. Pourquoi la chaleur absolue bornée ne convient pas

Sur le complément exact des zéro-modes, le Riesz réduit `Hred` est borné et :

```text
U(t) = exp(-t Hred)
```

est inversible.

Une application compacte inversible impose la compacité de l’identité, donc la
finitude dimensionnelle de l’espace. Ainsi, dans la réalisation physique
infinie-dimensionnelle :

```text
U(t) n’est pas compact,
U(t) n’est pas un heat kernel nucléaire absolu.
```

Ce n’est pas une lacune technique : c’est un no-go fonctionnel.

## 2. Objet correct : chaleur relative

On fixe sur le même espace réduit un opérateur de référence `Href`,
auto-adjoint et coercif. L’objet déterminantiel borné pertinent est :

```text
exp(-t Hred) - exp(-t Href).
```

Le paquet :

```lean
FiniteDefectReducedRelativeHeatData
```

stocke :

```text
Href auto-adjoint,
une constante de coercivité cref > 0,
une expansion compacte sommable de la différence pour tout t > 0.
```

La compacité de la différence est ensuite démontrée.

Modules :

```text
P0EFTJanusProgramPSummableCompactOperatorExpansion4D
P0EFTJanusProgramPFiniteDefectReducedRelativeHeat4D
P0EFTJanusProgramPGlobalCandidateAAugmentedReducedRelativeHeat4D.
```

## 3. Série de trace relative

Pour aller au-delà de la compacité, l’expansion est renforcée en une somme de
rang un :

```text
Σᵢ aᵢ |uᵢ><vᵢ|.
```

Le paquet :

```lean
SummableRankOneOperatorExpansion
```

porte :

```text
Σᵢ |aᵢ| ‖uᵢ‖ ‖vᵢ‖ < ∞,
Σᵢ aᵢ <uᵢ,vᵢ> convergente,
l’opérateur est exactement la somme des rang-un.
```

Il fournit la série scalaire :

```text
Tr_expansion(t) = Σᵢ aᵢ(t) <uᵢ(t),vᵢ(t)>.
```

Modules :

```text
P0EFTJanusProgramPSummableRankOneOperatorExpansion4D
P0EFTJanusProgramPFiniteDefectReducedRelativeTrace4D
P0EFTJanusProgramPGlobalCandidateAAugmentedReducedRelativeTrace4D
P0EFTJanusProgramPGlobalHessianRelativeTraceFrontier4D.
```

## 4. Ce qui est construit

À partir des trois paquets HESSIAN et d’un paquet relatif rang-un, on dispose
désormais de :

- H10–H14 ;
- l’espace réduit exact ;
- le Green réduit ;
- l’intervalle réel de résolvante ;
- l’identité de résolvante ;
- la différence de chaleur relative compacte ;
- une série de trace relative convergente pour chaque temps positif.

Le certificat de regroupement est :

```lean
GlobalCandidateARelativeTracePrerequisites4D.
```

## 5. Ce qui reste avant un déterminant zêta

Quatre obligations sont encore réelles.

### R1 — indépendance de présentation

Démontrer que la série scalaire est indépendante de l’expansion rang-un
choisie et coïncide avec la trace nucléaire intrinsèque.

### R2 — asymptotique de petit temps

Construire l’expansion locale de :

```text
Tr(exp(-t Hred) - exp(-t Href))
```

quand `t → 0⁺`, puis isoler les termes à soustraire.

### R3 — transformée de Mellin

Démontrer la convergence dans un demi-plan, puis la continuation régulière au
voisinage de `s = 0` de la fonction zêta relative.

### R4 — géométrie de Quillen

Identifier le déterminant relatif obtenu avec la ligne déterminante et la
connexion Bismut–Freed/Quillen de la famille géométrique Janus globale.

Le module historique :

```text
P0EFTJanusProgramPGlobalQuillenFrontier4D
```

ne fournit actuellement qu’un modèle cercle abstrait. Il ne doit pas être
présenté comme l’identification R4.

## 6. Frontière actuelle

Après HESSIAN-GLOBAL-01, la prochaine entrée analytique irréductible est donc :

```lean
GlobalCandidateAAugmentedReducedRelativeTraceData4D.
```

Après sa construction, il restera R1–R4. Aucun choix arbitraire de trace, de
contre-terme fini ou de déterminant n’est autorisé à les remplacer.
