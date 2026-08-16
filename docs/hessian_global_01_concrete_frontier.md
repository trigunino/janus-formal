# HESSIAN-GLOBAL-01 — frontière concrète finale

Date : **8 août 2026**.

Ce document décrit la route constructive la plus étroite actuellement exposée
sur `agent/hessian-spinc-maximal-domain`. Il ne remplace pas la validation du
noyau Lean : les modules ont été avancés selon la décision du projet de ne pas
bloquer l’implémentation sur les corrections d’élaboration.

## Point d’entrée

Façade :

```text
P0EFTJanusProgramPGlobalHessianConcreteAnalyticFrontier4D
```

Gate terminal :

```lean
global_candidateA_hessian_concrete_analytic_closure_gate
```

Cette route produit le certificat historique :

```lean
global_candidateA_hessian_closure_gate
```

## Ce qui n’est plus une entrée

Les éléments suivants sont reconstruits par les gates et ne figurent plus dans
la frontière :

- le paquet SpinC maximal et son accord same-action ;
- le certificat H10 ;
- une preuve indépendante de régularité Robin ;
- un germe Robin abstrait ;
- les sept preuves de symétrie des prolongements H11 ;
- les sept constantes de bornes et leur somme ;
- une borne globale fournie pour `H + P` ;
- l’auto-adjonction fournie de `H + P` ;
- la surjectivité fournie de `H + P` ;
- son inverse borné ;
- un inverse généralisé ;
- les deux défauts de paramétrix ;
- l’image fermée, le noyau fini, le conoyau fini, Fredholm et l’indice zéro.

## H10 — théorème interne

Le gate concret est :

```lean
global_candidateA_h10_closure_gate
```

Il assemble l’unique action GHY mobile Candidate-A, son domaine ouvert, sa
régularité `C²`, son second Fréchet symétrique, l’accord same-action sur le germe
lisse et l’indépendance du représentant lisse dans le cœur complété.

H10 ne constitue donc plus un quatrième paquet terminal.

## Paquet 1 — famille physique avec vraie projection de bord

Type :

```lean
ProgramPGlobalMinimalPhysicalLocalActionFamilyH10ReducedData4D
```

Le paquet contient le vrai tangent physique minimal D10-free, son ouvert
admissible, le datum Candidate-A local, les projections matière et LL, et la
projection linéaire continue :

```text
minimal physical tangent
  → completed H10 metric-normal parameter.
```

L’identité exacte :

```text
local Robin action
  = completed two-sheet H10 action ∘ boundaryProjection
```

construit le germe Robin et transfère automatiquement sa régularité `C²`.

Les seules régularités locales encore indépendantes concernent six blocs :

```text
Candidate-A interaction
Einstein–Hilbert +
Einstein–Hilbert −
Maxwell +
Maxwell −
finite/null BV
```

Matière et LL proviennent de leurs actions quadratiques de graphe ; Robin
provient de H10.

## Paquet 2 — accords denses H11

Type :

```lean
GlobalCandidateASevenPhysicalCanonicalContinuousAgreements4D
```

Pour chaque bloc physique, il faut fournir :

1. une forme bilinéaire continue sur l’unique Hilbert commun ;
2. son accord exact avec le véritable second Fréchet du bloc sur le cœur lisse
   diagonal dense.

Aucune symétrie n’est demandée. La symétrie du second Fréchet est démontrée sur
le cœur grâce au `C²`, puis étendue à tout l’espace par continuité et densité.

Les bornes sont ensuite automatiques :

```text
‖B_j(x,y)‖ ≤ ‖B_j‖ ‖x‖ ‖y‖,
C_total = Σ_j ‖B_j‖.
```

Le Riesz physique, l’opérateur augmenté, son action quadratique `C²`, son graphe
fermé et son auto-adjonction sont construits en aval.

## Paquet 3 — obstruction finie orthogonale et coercivité

Type :

```lean
GlobalCandidateAAugmentedOrthogonalCoerciveShift4D
```

Il contient uniquement :

- un projecteur fini idempotent `P` ;
- `PH = 0` et `HP = 0` ;
- la dimension finie de `range P` ;
- une constante `c > 0` et la coercivité de `H` sur `ker P` ;
- l’auto-adjonction de `P` ;
- la stationnarité LL.

### Borne globale dérivée

Le module générique

```text
P0EFTJanusProgramPFiniteDefectGlobalLowerBound4D
```

prouve :

\[
\|x\|
\le
\left(c^{-1}(1+\|P\|)+\|P\|\right)
\|(H+P)x\|.
\]

La constante globale n’est donc plus une donnée.

### Auto-adjonction et surjectivité dérivées

`H` est déjà auto-adjoint par H11 et `P` est auto-adjoint. Par conséquent
`H + P` est auto-adjoint.

La borne globale fournit l’anti-Lipschitz et l’injectivité. Pour un opérateur
auto-adjoint, l’orthogonal de l’image est son noyau ; l’image est donc dense.
La borne anti-Lipschitz donne une image fermée. Elle est ainsi tout l’espace,
donc `H + P` est surjectif.

L’open mapping theorem construit son inverse continu. Les identités :

```text
QH = HQ = I - P,
HQH = H
```

et les conclusions Fredholm sont ensuite automatiques.

## Chaîne terminale

```text
H10 déjà fermé
  → projection de bord réelle et Robin C²
  → famille locale à six blocs indépendants
  → mismatch matière–LL nul (H13)
  → sept accords denses continus
  → symétrie et bornes dérivées
  → opérateur augmenté auto-adjoint (H11)
  → obstruction finie + coercivité hors défaut
  → borne globale, surjectivité et inverse dérivés
  → paramétrix, Fredholm et indice zéro (H12)
  → certificat H14.
```

## Résidu mathématique irréductible

Hors corrections Lean, il reste trois constructions :

1. instancier la famille locale physique et démontrer ses six régularités `C²` ;
2. construire les sept prolongements continus et leurs accords denses ;
3. identifier le sous-espace fini d’obstruction et établir la coercivité de
   l’opérateur augmenté sur son complément orthogonal.

Le reste de H10–H14 est désormais du transport formel déjà encapsulé dans les
gates.

## Validation

Workflow focalisé :

```text
.github/workflows/program-p-hessian-concrete-frontier.yml
```

Audit statique :

```text
scripts/audit_hessian_concrete_frontier.py
```

Le ticket ne doit être déclaré certifié qu’après compilation Lean de la façade
concrète. Aucune étape H15 n’est prévue.
