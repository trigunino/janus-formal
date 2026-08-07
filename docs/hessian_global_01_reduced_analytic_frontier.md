# HESSIAN-GLOBAL-01 — frontière analytique constructive réduite

Date du lot : **7 août 2026**.

Ce document décrit la route constructive H10–H14 de la branche
`agent/hessian-spinc-maximal-domain`. L’implémentation a été poursuivie sans
attendre une validation Lean complète ; les nouvelles déclarations ne doivent
donc pas être présentées comme certifiées par le noyau avant le passage des
workflows focalisés.

## Résultat structurel

Le certificat terminal reste :

```lean
global_candidateA_hessian_closure_gate
```

La façade terminale constructive est :

```text
P0EFTJanusProgramPGlobalHessianTerminalConstructiveClosure4D
```

et son point d’entrée :

```lean
global_candidateA_hessian_terminal_constructive_closure_gate
```

La frontière terminale ne comporte plus que **trois paquets analytiques** :

```text
famille Candidate-A à six blocs C²
extensions continues canoniques des sept Hessiennes physiques
shift fini auto-adjoint anti-Lipschitz
```

H10 et SpinC ne sont plus des entrées de cette façade.

## SpinC : fermeture géométrique implémentée

La chaîne Clifford–connexion–repère invariant–IPP–courant de Green construit la
réalisation maximale same-action pour toute masse réelle. La façade privilégiée
reste :

```lean
primitive_spinC_smooth_graph_of_geometric_green
```

Les anciennes voies par décroissance Fourier, domaine maximal fourni, symétrie
fournie ou densité de cœur restent uniquement des adaptateurs.

## H10 : fermé par l’unique action mobile Candidate-A

Le terminal H10 concret est :

```lean
global_candidateA_h10_closure_gate
```

Il assemble les théorèmes déjà présents :

- l’action GHY complétée à deux feuilles est `C²` sur le vrai domaine ouvert ;
- son second Fréchet est symétrique ;
- toute présentation lisse admissible coïncide sur un vrai germe avec l’unique
  source mobile de `globalCandidateAGHYAction` ;
- cette source lisse factorise par le cœur métrique-normal complété et ne dépend
  pas du représentant choisi.

Le paquet final est :

```lean
GlobalCandidateAH10ClosureCertificate4D
```

Il ne demande aucune nouvelle action, normale, métrique ou donnée de bord. La
transversalité déjà utilisée pour entrer dans le domaine GHY est sa seule
prémisse géométrique.

Les modules génériques de calcul de germe composante par composante restent
utiles pour auditer l’origine de l’égalité :

```text
P0EFTJanusProgramPGlobalCandidateANormalBoundaryActionGermCalculus4D
P0EFTJanusProgramPGlobalCandidateANormalBoundaryIntegrandGermClosure4D
P0EFTJanusProgramPGlobalCandidateANormalBoundaryGHYFactorGerm4D
P0EFTJanusProgramPGlobalCandidateANormalBoundaryMeanCurvatureGerm4D
P0EFTJanusProgramPGlobalCandidateANormalBoundaryGaussFormGerm4D
P0EFTJanusProgramPGlobalCandidateANormalBoundaryComponentwiseTerminalClosure4D
```

mais leurs huit identités `EventuallyEq` ne sont plus exposées comme un
quatrième paquet terminal.

## Paquet A : famille locale à six blocs `C²`

Le paquet préféré est :

```lean
ProgramPGlobalMinimalPhysicalLocalActionFamilyH10RobinData4D
```

Il conserve seulement les régularités indépendantes :

```text
Candidate-A central
Einstein–Hilbert +
Einstein–Hilbert −
Maxwell +
Maxwell −
BV fini
```

Les trois autres secteurs sont reconstruits :

```text
Robin/GHY ← H10
matière   ← action quadratique du graphe SpinC
LL        ← action quadratique du graphe LL complet
```

Le gate H13 correspondant est :

```lean
global_candidateA_h13_minimalPhysical_h10RobinFamily_gate
```

Le mismatch matière–LL est donc annulé sur la même action sans retirer les sept
blocs physiques.

## Paquet B : extensions canoniques des sept Hessiennes physiques

Le paquet terminal H11 est :

```lean
GlobalCandidateASevenPhysicalCanonicalContinuousExtensions4D
```

Les formes sur le cœur ne sont plus fournies librement : elles sont fixées
comme les véritables seconds Fréchet des sept blocs de l’action locale. Chaque
bloc fournit uniquement son prolongement bilinéaire continu, son accord dense
et sa symétrie.

Les estimations sont ensuite automatiques :

```text
‖B_j(x,y)‖ ≤ ‖B_j‖ ‖ιx‖ ‖ιy‖,
C_total = Σ_j ‖B_j‖.
```

Le prolongement de la somme sur l’unique espace de Hilbert commun, son Riesz,
la fermeture du graphe, l’auto-adjonction et l’accord avec le Hessien augmenté
sont reconstruits par les gates H11 existants.

Le résidu analytique de H11 est donc exactement : **construire les sept
prolongements continus canoniques et prouver leur accord sur le cœur dense**.

## Paquet C : shift fini auto-adjoint anti-Lipschitz

Le nouveau paquet H12 préféré est :

```lean
GlobalCandidateAAugmentedSelfAdjointAntilipschitzShift4D
```

Il contient :

```text
un projecteur de défaut fini P,
la coercivité hors de P,
l’auto-adjonction de H + P,
une estimation anti-Lipschitz de H + P,
la stationnarité LL.
```

Le théorème générique :

```lean
selfAdjoint_surjective_of_antilipschitz
```

utilise l’identité hilbertienne

```text
ker(H + P)ᗮ = closure(range((H + P)†))
```

et l’auto-adjonction pour déduire la densité de l’image. L’estimation
anti-Lipschitz donne ensuite la bijectivité par le critère de Banach de Mathlib.
La surjectivité n’est donc plus une prémisse séparée.

La suite est construite automatiquement :

```text
surjectivité de H + P
→ inverse borné de H + P
→ QH = HQ = I - P
→ HQH = H
→ défauts gauche/droite finis
→ image fermée, noyau et conoyau finis
→ Fredholm, indice zéro.
```

Gate H12 :

```lean
global_candidateA_h12_fredholm_gate_of_selfAdjointAntilipschitzShift
```

## Route terminale à trois entrées

Le gate terminal préféré est :

```lean
global_candidateA_hessian_h10Robin_antilipschitz_closure_gate
```

Sa chaîne complète est :

```text
H10 géométrique déjà fermé
  → Robin C² et Hessien Robin authentique
  → famille locale à six blocs C²
  → mismatch matière–LL nul (H13)
  → sept extensions continues canoniques
  → domaine commun augmenté (H11)
  → shift fini auto-adjoint anti-Lipschitz
  → inverse, paramétrix et Fredholm (H12)
  → certificat H14.
```

Aucune étape H15 n’est prévue.

## Résidu mathématique actuel

Après les réductions formelles, il reste à construire concrètement :

1. les six régularités locales `C²` de la famille Candidate-A ;
2. les sept prolongements continus canoniques des blocs physiques ;
3. un projecteur fini adapté et l’estimation anti-Lipschitz du shift
   auto-adjoint `H + P`.

Tout le reste — Robin, matière, LL, bornes agrégées, surjectivité du shift,
inverse généralisé, défauts, Fredholm, indice et assemblage H14 — est dérivé.

## État de confiance

- **SpinC structurel :** fermé dans l’implémentation.
- **H10 structurel :** fermé par `global_candidateA_h10_closure_gate`.
- **H13 :** réduit aux six blocs locaux indépendants.
- **H11 :** réduit aux sept prolongements continus canoniques.
- **H12 :** réduit à une obstruction finie et une estimation anti-Lipschitz
  auto-adjointe ; la surjectivité n’est plus fournie.
- **Validation Lean des nouveaux modules :** non garantie à ce stade.
- **Ticket terminal :** ne doit être marqué `DONE` qu’après construction des
  trois paquets concrets et compilation de la façade et de l’audit.
